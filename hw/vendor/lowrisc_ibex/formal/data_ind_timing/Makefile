# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# A simple wrapper around fusesoc to make it a bit easier to run the formal flow

core-name   := lowrisc:fpv:ibex_data_ind_timing
vlnv        := $(subst :,_,$(core-name))
build-root  := $(abspath ../../build/$(vlnv))

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

.PHONY: all slow fast single
all: slow fast single

operations  := mull mulh div rem
slow_tgts   := $(addprefix slow_, $(operations))
fast_tgts   := $(addprefix fast_, $(operations))
single_tgts := $(addprefix single_, $(operations))
all_tgts    := $(slow_tgts) $(fast_tgts) $(single_tgts)

slow: $(slow_tgts)
fast: $(fast_tgts)
single: $(single_tgts)

$(all_tgts):
	$(call mk-fusesoc-cmd,$@)
