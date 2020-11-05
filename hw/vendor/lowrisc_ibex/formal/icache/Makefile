# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# A simple wrapper around fusesoc to make it a bit easier to run the formal flow

# Whether to use ECC (0 for disabled; 1 for enabled)
ECC := 0

core-name   := lowrisc:fpv:ibex_icache_fpv
vlnv        := $(subst :,_,$(core-name))
build-root  := $(abspath ../../build/$(vlnv))

fusesoc-params := --ICacheECC=$(ECC)

# Since we have a hacky hook that runs sv2v in place on fusesoc's
# copied source files, we have to generate different build roots for
# the two flavours (otherwise bad things will happen if you run make
# -j2)
mk-build-root = $(abspath ../../build/$(vlnv)/$(1))

mk-fusesoc-cmd = \
  fusesoc --cores-root=../.. \
  run --build-root=$(call mk-build-root,$(1)) \
  --target=$(1) \
  $(core-name) $(fusesoc-params)

.PHONY: all prove cover
all: prove cover

prove cover:
	$(call mk-fusesoc-cmd,$@)
