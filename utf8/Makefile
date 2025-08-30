# utf8/Makefile - Convert SKK-JISYO.* to UTF-8 (nkf) and make CDB via skk2cdb
# Requires: nkf, skktools (skk2cdb), tinycdb (cdb)

.PHONY: all utf8 cdb list list-cdb clean help check-tools
.DELETE_ON_ERROR:

THIS_MK   := $(lastword $(MAKEFILE_LIST))
THIS_DIR  := $(abspath $(dir $(THIS_MK)))
REPO_ROOT := $(abspath $(THIS_DIR)/..)

SRC          := $(notdir $(wildcard $(REPO_ROOT)/SKK-JISYO.*))
TARGETS      := $(SRC)                   # UTF-8 text dictionaries
CDB_TARGETS  := $(addsuffix .cdb,$(TARGETS))

all: utf8

utf8: $(TARGETS)

# 1) UTF-8化
$(TARGETS): %: $(REPO_ROOT)/%
	@tmp="$@.tmp.$$"; \
	nkf -w -Lu --no-best-fit-chars "$<" \
	| sed -E '1,5{s/(coding:[[:space:]]*)[^;[:space:]]+/\1utf-8/i}' \
	> "$$tmp"; \
	mv "$$tmp" "$@"

# 2) CDB化
cdb: check-tools utf8 $(CDB_TARGETS)

%.cdb: % | check-tools
	@tmp="$@.tmp.$$"; \
	skk2cdb "$<" > "$$tmp"; \
	mv "$$tmp" "$@"

list:
	@printf "%s\n" $(TARGETS)

list-cdb:
	@printf "%s\n" $(CDB_TARGETS)

clean:
	@rm -f -- $(TARGETS) $(CDB_TARGETS)

help:
	@echo "Targets: utf8 (default), cdb, list, list-cdb, clean"

check-tools:
	@command -v nkf >/dev/null 2>&1 || { echo "missing: nkf" >&2; exit 1; }
	@command -v skk2cdb >/dev/null 2>&1 || { echo "missing: skk2cdb (skktools)" >&2; exit 1; }
	@command -v cdb >/dev/null 2>&1 || { echo "missing: cdb (tinycdb)" >&2; exit 1; }
