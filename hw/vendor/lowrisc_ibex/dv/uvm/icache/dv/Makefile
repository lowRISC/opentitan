# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Simple wrappers around dvsim.py to avoid needing long command lines. This
# doesn't do any dependency tracking (as you might expect in a Makefile) because
# the dvsim infrastructure doesn't support it.

# Set WAVES to 1 to get VPD/FSDB dumps
WAVES=0

# Set VERBOSITY to a nonempty string and it will be passed to dvsim with the
# --verbosity parameter, overriding whatever was set in the hjson file.
VERBOSITY=

# Specify the seed for the test to run. If this is empty, dvsim.py will pick
# random seeds. By default, we make runs reproducible, so force the seed.
SEED=1

ibex-top       := ../../../..
scratch-root   := $(ibex-top)/build
dvsim-py       := $(ibex-top)/vendor/lowrisc_ip/dvsim/dvsim.py
dvsim-std-args := --skip-ral --scratch-root $(scratch-root)

waves-arg      := $(if $(filter-out 0,$(WAVES)),--waves,)
verbosity-arg  := $(if $(VERBOSITY),--verbosity $(VERBOSITY),)
seed-arg       := $(if $(SEED),--fixed-seed $(SEED),)

dvsim-mk-args    := $(waves-arg) $(verbosity-arg) $(seed-arg)
run-icache-dvsim := $(dvsim-py) ibex_icache_sim_cfg.hjson $(dvsim-std-args) $(dvsim-mk-args)

.PHONY: all
all: run

.PHONY: just-build
just-build:
	$(run-icache-dvsim) --build-only

.PHONY: run
run:
	$(run-icache-dvsim)
