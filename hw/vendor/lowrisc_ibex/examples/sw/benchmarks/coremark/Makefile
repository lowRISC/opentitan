# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Build coremark benchmark for Ibex Simple System

COREMARK_DIR = ../../../../vendor/eembc_coremark

export PORT_DIR  = $(CURDIR)/ibex
export ITERATIONS = 10
export OPATH = $(CURDIR)/

# Export OPATH above doesn't seem to work so need to explicitly give it on the
# make command line
all:
	$(MAKE) -C $(COREMARK_DIR)

clean:
	$(MAKE) -C $(COREMARK_DIR) clean
