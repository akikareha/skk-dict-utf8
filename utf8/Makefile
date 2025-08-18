# utf8/Makefile - Convert SKK-JISYO.* to UTF-8 (nkf)
# Requires: nkf

.PHONY: all utf8 list clean help
.DELETE_ON_ERROR:

THIS_MK   := $(lastword $(MAKEFILE_LIST))
THIS_DIR  := $(abspath $(dir $(THIS_MK)))
REPO_ROOT := $(abspath $(THIS_DIR)/..)

SRC     := $(notdir $(wildcard $(REPO_ROOT)/SKK-JISYO.*))
TARGETS := $(SRC)

all: utf8
utf8: $(TARGETS)

$(TARGETS): %: $(REPO_ROOT)/%
	@tmp="$@.$$RANDOM$$RANDOM"; \
	nkf -w -Lu --no-best-fit-chars "$<" \
	| sed -E '1,5{s/(coding:[[:space:]]*)[^;[:space:]]+/\1utf-8/i}' \
	> "$$tmp"; \
	mv "$$tmp" "$@"

list:
	@printf "%s\n" $(TARGETS)

clean:
	@rm -f -- $(TARGETS)

help:
	@echo "Targets: utf8 (default), list, clean"
