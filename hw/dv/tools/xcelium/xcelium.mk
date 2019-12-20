####################################################################################################
## Copyright lowRISC contributors.                                                                ##
## Licensed under the Apache License, Version 2.0, see LICENSE for details.                       ##
## SPDX-License-Identifier: Apache-2.0                                                            ##
####################################################################################################
## Makefile option groups that can be enabled by test Makefile / command line.                    ##
## These are generic set of option groups that apply to all testbenches.                          ##
####################################################################################################
# Simulator too specific options
# Mandatory items to set (these are used by rules.mk):
# SIMCC       - Simulator compiler used to build / elaborate the bench
# SIMX        - Simulator executable used to run the tests

SIMCC       := xrun -elaborate
SIMX        ?= xrun
SIM_SETUP   ?= ${MAKE_ROOT}/xcelium/xcelium_$(DUMP).tcl

# max number of errors before the run is stopped
ERROR_MAX   := 50
# set standard build options
BUILD_OPTS  += -l ${BUILD_LOG}
BUILD_OPTS  += -access +r
BUILD_OPTS  += -messages
BUILD_OPTS  += -errormax ${ERROR_MAX}
BUILD_OPTS  += -sv
BUILD_OPTS  += -timescale 1ns/1ps
BUILD_OPTS  += -uvmhome ${UVM_HOME}
BUILD_OPTS  += -xmlibdirname ${SV_FLIST_GEN_DIR}/xcelium.d
BUILD_OPTS  += -f ${SV_FLIST}
BUILD_OPTS  += -64bit
BUILD_OPTS  += -xprop F # -xverbose  << add to see which modules does not have xprop enabled


# set standard run options
RUN_OPTS    += -input ${SIM_SETUP}
RUN_OPTS    += +SVSEED=${SEED}
RUN_OPTS    += +UVM_VERBOSITY=${UVM_VERBOSITY}
RUN_OPTS    += +UVM_TESTNAME=${UVM_TEST}
RUN_OPTS    += +UVM_TEST_SEQ=${UVM_TEST_SEQ}
RUN_OPTS    += -l ${RUN_LOG}
RUN_OPTS    += -xmlibdirname ${SV_FLIST_GEN_DIR}/xcelium.d -R
RUN_OPTS    += -64bit


#########################
## Tool Specific Modes ##
#########################
# Enable simulation profiling
XCELIUM_SIMPROFILE ?= 0
ifeq (${XCELIUM_SIMPROFILE},1)
endif

# Enable coverage
XCELIUM_COV ?= 0
ifeq (${XCELIUM_COV},1)
endif
