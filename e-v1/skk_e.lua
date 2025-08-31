-- skk_e.lua  (Lua 5.1)
-- SKK-JISYO-E v1: バックスラッシュ・エスケープでS式ゼロ、任意Unicodeを候補・注釈に格納可能
-- 提供機能:
--   * parse_entry(line) -> { reading=..., candidates={ {surface=..., annos={...}}, ... } } | nil,"reason"
--   * serialize_entry(entry) -> "reading /cand.../"  （必ずE形式でエスケープ）
--   * read_e(stdin) / write_e(stdout) の簡易CLI
--   * （おまけ）legacy_to_e(line): 旧SKK行をE形式へ変換する試案（concat の「文字列だけ」を安全に連結する超限定対応）
--
-- License: MIT

local M = {}

-- ========== 文字ユーティリティ ==========
local function is_space(ch) return ch == " " or ch == "\t" end
local function hexval(h)
  local n = tonumber(h, 16)
  if not n then error("bad hex: "..tostring(h)) end
  return n
end

-- ========== アンエスケープ ==========
-- サポート: \\ \/ \; \[ \] \n \t \" \' \u{XXXX}
local function unescape(s)
  local out, i, len = {}, 1, #s
  while i <= len do
    local c = s:sub(i,i)
    if c ~= "\\" then
      out[#out+1] = c
      i = i + 1
    else
      if i == len then
        -- 末尾の単独 "\" はそのままにする（保守的）
        out[#out+1] = "\\"
        i = i + 1
      else
        local n = s:sub(i+1,i+1)
        if n == "\\" or n == "/" or n == ";" or n == "[" or n == "]" or n == "'" or n == '"' then
          out[#out+1] = n
          i = i + 2
        elseif n == "n" then out[#out+1] = "\n"; i = i + 2
        elseif n == "t" then out[#out+1] = "\t"; i = i + 2
        elseif n == "u" then
          -- \u{...}
          if s:sub(i+2,i+2) ~= "{" then
            -- 不正: 素直に "u" を採用
            out[#out+1] = "u"
            i = i + 2
          else
            local j = i + 3
            local brace_end = s:find("}", j, true)
            if not brace_end then
              -- 不正: そのまま出す
              out[#out+1] = "\\u{"
              i = i + 3
            else
              local hex = s:sub(j, brace_end-1)
              local cp = tonumber(hex, 16)
              if not cp then
                out[#out+1] = "\\u{"..hex.."}"
              else
                -- UTF-8 encode
                if cp <= 0x7F then
                  out[#out+1] = string.char(cp)
                elseif cp <= 0x7FF then
                  out[#out+1] = string.char(0xC0 + math.floor(cp/0x40),
                                            0x80 + (cp % 0x40))
                elseif cp <= 0xFFFF then
                  out[#out+1] = string.char(0xE0 + math.floor(cp/0x1000),
                                            0x80 + (math.floor(cp/0x40) % 0x40),
                                            0x80 + (cp % 0x40))
                elseif cp <= 0x10FFFF then
                  out[#out+1] = string.char(0xF0 + math.floor(cp/0x40000),
                                            0x80 + (math.floor(cp/0x1000) % 0x40),
                                            0x80 + (math.floor(cp/0x40) % 0x40),
                                            0x80 + (cp % 0x40))
                else
                  -- 範囲外は素通し
                  out[#out+1] = "\\u{"..hex.."}"
                end
              end
              i = brace_end + 1
            end
          end
        else
          -- 未定義: バックスラッシュを落として次の文字を入れる（保守的）
          out[#out+1] = n
          i = i + 2
        end
      end
    end
  end
  return table.concat(out)
end

-- ========== エスケープ ==========
-- 必ず \ / ; \ [ ] を退避。最小版なら \/ \; \\ だけでもOKだが網羅的に。
local function escape(s)
  s = s:gsub("\\", "\\\\")
  s = s:gsub("/", "\\/")
  s = s:gsub(";", "\\;")
  s = s:gsub("%[", "\\[")
  s = s:gsub("%]", "\\]")
  return s
end

-- ========== スラッシュ分割（\/ を考慮） ==========
local function split_on_slash(body)
  -- 入力例: "/A\/B;anno/C/"/ 先頭/末尾の / は parse_entry 側で処理
  local parts, buf, i, len, esc = {}, {}, 1, #body, false
  while i <= len do
    local c = body:sub(i,i)
    if esc then
      buf[#buf+1] = c
      esc = false
    elseif c == "\\" then
      buf[#buf+1] = c
      esc = true
    elseif c == "/" then
      -- 区切り
      parts[#parts+1] = table.concat(buf)
      buf = {}
    else
      buf[#buf+1] = c
    end
    i = i + 1
  end
  parts[#parts+1] = table.concat(buf)
  return parts
end

-- ========== セミコロン分割（\; を考慮） ==========
local function split_on_semicolon(s)
  local fields, buf, i, len, esc = {}, {}, 1, #s, false
  while i <= len do
    local c = s:sub(i,i)
    if esc then
      buf[#buf+1] = c
      esc = false
    elseif c == "\\" then
      buf[#buf+1] = c
      esc = true
    elseif c == ";" then
      fields[#fields+1] = table.concat(buf)
      buf = {}
    else
      buf[#buf+1] = c
    end
    i = i + 1
  end
  fields[#fields+1] = table.concat(buf)
  return fields
end

-- ========== 1行パース ==========
-- "reading /cand/..." 形式をE仕様で解釈。コメント行・空行は nil を返す。
function M.parse_entry(line)
  if not line then return nil, "nil line" end
  if line == "" or line:match("^%s*$") then return nil end
  if line:sub(1,1) == ";" then return nil end

  -- 読みと本体の分離（最初の空白まで）
  local sp = line:find("%s")
  if not sp then return nil, "no space between reading and body" end
  local reading = line:sub(1, sp-1)
  local rest = line:sub(sp):match("^%s*(.-)%s*$") -- trim

  if not (rest:sub(1,1) == "/" and rest:sub(-1) == "/") then
    return nil, "body must start and end with '/'"
  end
  local inner = rest:sub(2, -2)  -- 先頭/末尾の / を除去

  -- 候補列を / で分割（エスケープ考慮）
  local raw_candidates = split_on_slash(inner)
  local candidates = {}
  for _, rawc in ipairs(raw_candidates) do
    if rawc ~= "" then
      -- 候補を ; で分割（エスケープ考慮）
      local segs = split_on_semicolon(rawc)
      local surface_esc = segs[1] or ""
      local annos = {}
      for i=2,#segs do
        annos[#annos+1] = unescape(segs[i])
      end
      candidates[#candidates+1] = {
        surface = unescape(surface_esc),
        annos = annos
      }
    end
  end

  return { reading = reading, candidates = candidates }
end

-- ========== シリアライズ（E形式で出力） ==========
function M.serialize_entry(entry)
  local parts = {}
  for _, c in ipairs(entry.candidates or {}) do
    local s = escape(c.surface or "")
    if c.annos and #c.annos > 0 then
      local ann = {}
      for i=1,#c.annos do
        ann[#ann+1] = escape(c.annos[i])
      end
      s = s .. ";" .. table.concat(ann, ";")
    end
    parts[#parts+1] = s
  end
  return string.format("%s /%s/", entry.reading, table.concat(parts, "/"))
end

-- ==========（おまけ）旧SKK -> E形式の粗変換 ==========
-- 目的: 既存辞書の "(concat "...")" だけを安全に平文化。
-- 制限: 文字列リテラル以外（関数、変数、評価）は一切非対応→見つけたらエラー。
-- 追加: 共通のUTF-8エンコード関数（unescapeでも使っているロジックの切り出し）
local function utf8_encode(cp)
  if cp <= 0x7F then
    return string.char(cp)
  elseif cp <= 0x7FF then
    return string.char(0xC0 + math.floor(cp/0x40),
                       0x80 + (cp % 0x40))
  elseif cp <= 0xFFFF then
    return string.char(0xE0 + math.floor(cp/0x1000),
                       0x80 + (math.floor(cp/0x40) % 0x40),
                       0x80 + (cp % 0x40))
  elseif cp <= 0x10FFFF then
    return string.char(0xF0 + math.floor(cp/0x40000),
                       0x80 + (math.floor(cp/0x1000) % 0x40),
                       0x80 + (math.floor(cp/0x40) % 0x40),
                       0x80 + (cp % 0x40))
  end
  return "" -- 範囲外は無視
end

-- 置き換え: Lisp文字列のデコード（8進/16進/Unicode/制御系エスケープ対応）
local function dequote_lisp_string(s)
  local out, i, len = {}, 1, #s
  while i <= len do
    local c = s:sub(i,i)
    if c ~= "\\" then
      out[#out+1] = c
      i = i + 1
    else
      -- バックスラッシュの次を検査
      if i == len then
        out[#out+1] = "\\"; i = i + 1
      else
        local n = s:sub(i+1,i+1)

        -- 8進 \NNN （最大3桁）
        if n:match("%d") and n < "8" then
          local j = i + 1
          local oct = {}
          for k = 1,3 do
            local ch = s:sub(j,j)
            if ch:match("[0-7]") then
              oct[#oct+1] = ch
              j = j + 1
            else
              break
            end
          end
          local cp = tonumber(table.concat(oct), 8) or 0
          out[#out+1] = utf8_encode(cp)
          i = j

        -- 16進 \xNN （1〜2桁）
        elseif n == "x" then
          local h1 = s:sub(i+2, i+2)
          local h2 = s:sub(i+3, i+3)
          local hex
          if h1 and h1:match("%x") then
            if h2 and h2:match("%x") then
              hex = h1 .. h2
              i = i + 4
            else
              hex = h1
              i = i + 3
            end
            local cp = tonumber(hex, 16) or 0
            out[#out+1] = utf8_encode(cp)
          else
            -- \x の直後が16進でない → そのまま 'x' を出す
            out[#out+1] = "x"
            i = i + 2
          end

        -- Unicode \uNNNN（4桁）
        elseif n == "u" then
          local hex = s:sub(i+2, i+5)
          if hex:match("^[%x][%x][%x][%x]$") then
            local cp = tonumber(hex, 16) or 0
            out[#out+1] = utf8_encode(cp)
            i = i + 6
          else
            out[#out+1] = "u"
            i = i + 2
          end

        -- Unicode \UNNNNNNNN（8桁）
        elseif n == "U" then
          local hex = s:sub(i+2, i+9)
          if hex:match("^[%x][%x][%x][%x][%x][%x][%x][%x]$") then
            local cp = tonumber(hex, 16) or 0
            out[#out+1] = utf8_encode(cp)
            i = i + 10
          else
            out[#out+1] = "U"
            i = i + 2
          end

        -- 制御系やクォート
        elseif n == "n" then out[#out+1] = "\n"; i = i + 2
        elseif n == "t" then out[#out+1] = "\t"; i = i + 2
        elseif n == "r" then out[#out+1] = "\r"; i = i + 2
        elseif n == "a" then out[#out+1] = string.char(7); i = i + 2
        elseif n == "b" then out[#out+1] = "\b"; i = i + 2
        elseif n == "f" then out[#out+1] = "\f"; i = i + 2
        elseif n == "v" then out[#out+1] = "\v"; i = i + 2
        elseif n == "e" then out[#out+1] = string.char(27); i = i + 2
        elseif n == '"' or n == "\\" then
          out[#out+1] = n; i = i + 2
        else
          -- 未定義の \X は X をそのまま
          out[#out+1] = n; i = i + 2
        end
      end
    end
  end
  return table.concat(out)
end

local function try_eval_concat(expr)
  -- 形だけ: (concat "A" "/" "B") を A.."/"..B にする
  -- 前後空白削除
  expr = expr:match("^%s*(.-)%s*$")
  if not expr:match("^%(%s*concat") then return nil end
  local inside = expr:match("^%(%s*concat%s*(.*)%)%s*$")
  if not inside then return nil end
  local out = {}
  -- 引数は連続する文字列リテラルだけとする
  for token in inside:gmatch('()"[^"]*"'..'()') do end -- no-op just to avoid lint
  local i = 1
  while i <= #inside do
    local ch = inside:sub(i,i)
    if ch:match("%s") then
      i = i + 1
    elseif ch == '"' then
      local j = i + 1
      local esc = false
      while j <= #inside do
        local cj = inside:sub(j,j)
        if esc then esc = false
        elseif cj == "\\" then esc = true
        elseif cj == '"' then break end
        j = j + 1
      end
      if j > #inside or inside:sub(j,j) ~= '"' then
        return nil -- 不正
      end
      local raw = inside:sub(i+1, j-1)
      out[#out+1] = dequote_lisp_string(raw)
      i = j + 1
    else
      -- 文字列リテラル以外が来たら非対応
      return nil
    end
  end
  return table.concat(out)
end

function M.legacy_to_e(line)
  if not line or line == "" or line:match("^%s*$") or line:sub(1,1) == ";" then
    return line, true -- そのまま
  end
  local sp = line:find("%s")
  if not sp then return nil, "no space between reading and body" end
  local reading = line:sub(1, sp-1)
  local rest = line:sub(sp):match("^%s*(.-)%s*$")
  if not (rest:sub(1,1) == "/" and rest:sub(-1) == "/") then
    return nil, "body must start and end with '/'"
  end
  local inner = rest:sub(2,-2)
  local chunks = split_on_slash(inner)
  local parts = {}
  for _, rawc in ipairs(chunks) do
    if rawc ~= "" then
      -- 旧形式の候補は S式が混じることがあるので、セミコロンでいったん分割
      local segs = split_on_semicolon(rawc)
      -- surface だけは (concat "...") の限定評価を試みる
      local surface_raw = segs[1] or ""
      if surface_raw:find("%(concat") then
        local ok = try_eval_concat(surface_raw)
        if not ok then
          return nil, "unsupported lisp form in surface: "..surface_raw
        end
        surface_raw = ok
      end
      local surface = escape(unescape(surface_raw))  -- 念のため通す
      local annos = {}
      for i=2,#segs do
        local a = segs[i] or ""
        -- 注釈内のS式は基本非対応。（必要なら似た処理を追加）
        if a:find("%(concat") then
          local ok = try_eval_concat(a)
          if not ok then
            return nil, "unsupported lisp form in annotation: "..a
          end
          a = ok
        end
        annos[#annos+1] = escape(unescape(a))
      end
      if #annos > 0 then
        parts[#parts+1] = surface .. ";" .. table.concat(annos, ";")
      else
        parts[#parts+1] = surface
      end
    end
  end
  return string.format("%s /%s/", reading, table.concat(parts, "/")), true
end

-- ========== 簡易CLI ==========
local function read_all_lines()
  local t = {}
  for line in io.lines() do t[#t+1] = line end
  return t
end

local function cmd_parse()
  for line in io.lines() do
    local e, err = M.parse_entry(line)
    if e then
      for _, c in ipairs(e.candidates) do
        -- TSV: reading \t surface \t anno1|anno2...
        io.write(
          e.reading, "\t",
          c.surface, "\t",
          table.concat(c.annos or {}, "|"),
          "\n"
        )
      end
    elseif err then
      io.stderr:write("skip: ", err, " :: ", line, "\n")
    end
  end
end

local function cmd_write()
  -- TSV: reading \t surface \t anno1|anno2... をE形式へ
  -- デモ用
  for line in io.lines() do
    if line ~= "" and not line:match("^%s*$") then
      local r, s, rest = line:match("^(.-)\t(.-)\t(.*)$")
      if r and s then
        local annos = {}
        if rest and rest ~= "" then
          for a in tostring(rest):gmatch("([^|]+)") do annos[#annos+1] = a end
        end
        local out = M.serialize_entry({reading=r, candidates={{surface=s, annos=annos}}})
        print(out)
      else
        io.stderr:write("bad tsv: ", line, "\n")
      end
    end
  end
end

local function cmd_legacy_to_e()
  for line in io.lines() do
    local out, ok = M.legacy_to_e(line)
    if out then print(out) end
    if ok ~= true and ok ~= nil then
      -- no-op
    end
  end
end

-- エントリポイント
if ... == nil then
  -- 使い方表示
  io.stderr:write([[
skk_e.lua  (Lua 5.1)
Usage:
  lua skk_e.lua parse        # E形式を読んで TSV(読み/表記/注釈|…) を出力
  lua skk_e.lua write        # TSV(読み\t表記\t注釈|…) を E形式にシリアライズ
  lua skk_e.lua legacy_to_e  # 旧SKK行をE形式へ粗変換（concatの文字列のみ限定対応）
Examples:
  cat SKK-JISYO.E | lua skk_e.lua parse
  cat entries.tsv  | lua skk_e.lua write
  cat SKK-JISYO    | lua skk_e.lua legacy_to_e
]])
else
  local cmd = ...
  if     cmd == "parse"        then cmd_parse()
  elseif cmd == "write"        then cmd_write()
  elseif cmd == "legacy_to_e"  then cmd_legacy_to_e()
  end
end

return M
