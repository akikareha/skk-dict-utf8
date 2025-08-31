.PHONY: all e-v1 cdb list list-cdb clean help
.DELETE_ON_ERROR:

THIS_MK   := $(lastword $(MAKEFILE_LIST))
THIS_DIR  := $(abspath $(dir $(THIS_MK)))
REPO_ROOT := $(abspath $(THIS_DIR)/..)
UTF8_ROOT := $(abspath $(THIS_DIR)/../utf8)

SRC          := $(notdir $(wildcard $(REPO_ROOT)/SKK-JISYO.*))
TARGETS      := $(SRC)                   # UTF-8 text dictionaries
CDB_TARGETS  := $(addsuffix .cdb,$(TARGETS))

all: e-v1

e-v1: $(TARGETS)

$(TARGETS): %: $(UTF8_ROOT)/%
	@tmp="$@.tmp.$$"; \
	cat "$<" | lua skk_e.lua legacy_to_e > "$$tmp"; \
	mv "$$tmp" "$@"

cdb: e-v1 $(CDB_TARGETS)

%.cdb: %
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
	@echo "Targets: e-v1 (default), cdb, list, list-cdb, clean"
