####################################################################################################
## Copyright lowRISC contributors.                                                                ##
## Licensed under the Apache License, Version 2.0, see LICENSE for details.                       ##
## SPDX-License-Identifier: Apache-2.0                                                            ##
####################################################################################################
## Makefile option groups that can be enabled by test Makefile / command line.                    ##
## These are generic set of option groups that apply to all testbenches.                          ##
## These are meant to be simulator agnostic                                                       ##
## Please add tool specific options with appropriate ifeq's                                       ##
####################################################################################################

# Distinguish UVM TB and the other environments for Verilator, FPGA etc
BUILD_OPTS  += +define+UVM
# uvm specific - set default widths
BUILD_OPTS  += +define+UVM_NO_DEPRECATED
BUILD_OPTS  += +define+UVM_REGEX_NO_DPI
BUILD_OPTS  += +define+UVM_REG_ADDR_WIDTH=${TL_AW}
BUILD_OPTS  += +define+UVM_REG_DATA_WIDTH=${TL_DW}
BUILD_OPTS  += +define+UVM_REG_BYTENABLE_WIDTH=${TL_DBW}

# Enable UVM trace options
UVM_TRACE ?= 0
ifeq (${UVM_TRACE},1)
  RUN_OPTS  += +UVM_PHASE_TRACE
  RUN_OPTS  += +UVM_CONFIG_DB_TRACE
  RUN_OPTS  += +UVM_OBJECTION_TRACE
endif

# Options for generating waves / debugging.
WAVES       ?= 0
DUMP        ?= fsdb
DUMP_FILE   ?= waves.${DUMP}
export WAVES
export DUMP
export DUMP_FILE

ifeq (${WAVES},1)
  ifeq (${SIMULATOR},vcs)
    VCS_WAVES = 1
  endif
endif

# Enable simulation profiling
SIMPROFILE ?= 0
ifeq (${SIMPROFILE},1)
  ifeq (${SIMULATOR},vcs)
    VCS_SIMPROFILE = 1
  else ifeq (${SIMULATOR},xcelium)
    XCELIUM_SIMPROFILE = 1
  endif
endif

# Enable coverage
COV ?= 0
ifeq (${COV},1)
  ifeq (${SIMULATOR},vcs)
    VCS_COV = 1
  else ifeq (${SIMULATOR},xcelium)
    XCELIUM_COV = 1
  endif
endif

# Simulation flow control options
# Skip RAL model generation
SKIP_RAL_GEN ?= 0
