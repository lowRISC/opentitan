# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Simple wrappers around dvsim.py to avoid needing long command lines. This
# doesn't do any dependency tracking (as you might expect in a Makefile).

# Set WAVES to 1 to get wave dumps
WAVES=0

# Set COVERAGE to 1 to get coverage collection
COVERAGE=0

# Set VERBOSITY to a nonempty string and it will be passed to dvsim with the
# --verbosity parameter, overriding whatever was set in the hjson file.
VERBOSITY=

# The number of seeds to run for each selected test. Defaults to 1.
RESEED=1

# Specify the seed for the test to run. If this is empty, dvsim.py
# will pick random seeds. By default, we make runs reproducible, so
# force the seed if RESEED is 1.
default-seed := 123
SEED=$(if $(filter 1,$(RESEED)),$(default-seed),)

# Specify which tests to run. Defaults to the empty string, which
# means dvsim will run its default (the "smoke" suite of tests).
TESTS=

ibex-top       := ../../../..
scratch-root   := $(ibex-top)/build
dvsim-py       := $(ibex-top)/vendor/lowrisc_ip/util/dvsim/dvsim.py
dvsim-std-args := --scratch-root $(scratch-root)

waves-arg      := $(if $(filter-out 0,$(WAVES)),--waves,)
coverage-arg   := $(if $(filter-out 0,$(COVERAGE)),-c,)
verbosity-arg  := $(if $(VERBOSITY),--verbosity $(VERBOSITY),)
reseed-arg     := --reseed $(RESEED)
seed-arg       := $(if $(SEED),--fixed-seed $(SEED),)
tests-arg      := $(if $(TESTS),--items $(TESTS))

dvsim-mk-args := \
  $(waves-arg) $(coverage-arg) $(verbosity-arg) \
  $(reseed-arg) $(seed-arg) $(tests-arg)

.PHONY: run
run:
	$(dvsim-py) ibex_icache_sim_cfg.hjson $(dvsim-std-args) $(dvsim-mk-args)
