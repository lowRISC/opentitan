# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Top-Level Makefile
###############################################################################

.SUFFIXES:
export

# Explicitly ask for the bash shell
SHELL := bash

# Build the 'all' target by default, override with e.g. GOAL=rtl_tb_compile
GOAL ?= all

###############################################################################
# CONFIGURATION KNOBS

# Seed for instruction generator and RTL simulation
#
# By default, SEED is set to a different value on each run by picking a random
# value in the Makefile. For overnight testing, a sensible seed might be
# something like the output of "date +%y%m%d". For regression testing, you'll
# need to make sure that a the seed for a failed test "sticks" (so we don't
# start passing again without fixing the bug).
SEED                := $(shell echo $$RANDOM)

# Enable waveform dumping
WAVES               := 0
# Enable coverage dump
COV                 := 0
# RTL simulator (xlm, vcs, questa, dsim, )
SIMULATOR           := xlm
# ISS (spike, ovpsim)
ISS                 := spike
# Test name (default: full regression)
TEST                := all
RISCV-DV-TESTLIST   := riscv_dv_extension/testlist.yaml
DIRECTED-TESTLIST   := directed_tests/directed_testlist.yaml
# Verbose logging
VERBOSE             := 0
# Number of iterations for each test, assign a non-empty value to override the
# iteration count in the test list
ITERATIONS          :=
# Pass/fail signature address at the end of test (see riscv_dv handshake documentation)
SIGNATURE_ADDR      := 8ffffffc

### Ibex top level parameters ###
IBEX_CONFIG         := opentitan

# Path to DUT used for coverage reports
DUT_COV_RTL_PATH    := "ibex_top"

export EXTRA_COSIM_CFLAGS ?=

ifeq ($(COSIM_SIGSEGV_WORKAROUND), 1)
	EXTRA_COSIM_CFLAGS += -DCOSIM_SIGSEGV_WORKAROUND
endif

###############################################################################

# Setup the necessary paths for all python scripts to find all other relevant modules.
export PYTHONPATH := $(shell python3 -c 'from scripts.setup_imports import get_pythonpath; get_pythonpath()')

# We run the 'create_metadata' step in this top-level makefile, so the sub-make
# invocations can query the generated metadata objects. Since the targets/dependencies
# are extracted from this metadata, it must be query-able in the makefile 'immediate' stage.
.PHONY: run
run:
	@env PYTHONPATH=$(PYTHONPATH) python3 ./scripts/metadata.py \
	  --op "create_metadata" \
	  --dir-metadata $(METADATA-DIR) \
	  --dir-out $(OUT-DIR) \
	  --args-list "\
	  SEED=$(SEED) WAVES=$(WAVES) COV=$(COV) SIMULATOR=$(SIMULATOR) \
	  ISS=$(ISS) TEST=$(TEST) VERBOSE=$(VERBOSE) ITERATIONS=$(ITERATIONS) \
	  SIGNATURE_ADDR=$(SIGNATURE_ADDR) IBEX_CONFIG=$(IBEX_CONFIG) \
	  DUT_COV_RTL_PATH=$(DUT_COV_RTL_PATH)"
	@$(MAKE) --file wrapper.mk --environment-overrides --no-print-directory $(GOAL)

###############################################################################

# This is the top-level output directory. Everything we generate goes in
# here.
OUT := out

# Derived directories from $(OUT), used for stuff that's built once or
# stuff that gets run for each seed, respectively. Using OUT-DIR on
# the way avoids ugly double slashes if $(OUT) happens to end in a /.
export OUT-DIR      := $(dir $(OUT)/)
export METADATA-DIR := $(OUT-DIR)metadata

# riscv-dv extension directory
export EXT_DIR             := riscv_dv_extension

###############################################################################

.PHONY: clean
clean:
	rm -rf $(OUT-DIR)
	rm -f $(EXT_DIR)/riscv_core_setting.sv

###############################################################################
