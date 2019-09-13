####################################################################################################
## Copyright lowRISC contributors.                                                                ##
## Licensed under the Apache License, Version 2.0, see LICENSE for details.                       ##
## SPDX-License-Identifier: Apache-2.0                                                            ##
####################################################################################################
## Entry point test Makefile forr building and running tests.                                     ##
## These are generic set of option groups that apply to all testbenches.                          ##
## This flow requires the following options to be set:                                            ##
## DV_DIR       - current dv directory that contains the test Makefile                            ##
## DUT_TOP      - top level dut module name                                                       ##
## TB_TOP       - top level tb module name                                                        ##
## DOTF         - .f file used for compilation                                                    ##
## COMPILE_KEY  - compile option set                                                              ##
## TEST_NAME    - name of the test to run - this is supplied on the command line                  ##
####################################################################################################
DV_DIR          := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))
COMPILE_KEY     ?= default

####################################################################################################
##                     A D D    I N D I V I D U A L    T E S T S    B E L O W                     ##
####################################################################################################

ifeq (${TEST_NAME},prim_lfsr_gal_xor)
  export DUT_TOP := prim_lfsr
  export TB_TOP  := prim_lfsr_tb
  FUSESOC_CORE   := lowrisc:dv:prim_lfsr_sim:0.1
  COMPILE_KEY    := gal_xor
endif

ifeq (${TEST_NAME},prim_lfsr_fib_xnor)
  export DUT_TOP := prim_lfsr
  export TB_TOP  := prim_lfsr_tb
  FUSESOC_CORE   := lowrisc:dv:prim_lfsr_sim:0.1
  COMPILE_KEY    := fib_xnor
endif

ifeq (${COMPILE_KEY},gal_xor)
  BUILD_OPTS  := +define+LFSR_TYPE="\"GAL_XOR\""+MAX_LFSR_DW=28+MIN_LFSR_DW=4
endif

ifeq (${COMPILE_KEY},fib_xnor)
  BUILD_OPTS  := +define+LFSR_TYPE="\"FIB_XNOR\""+MAX_LFSR_DW=28+MIN_LFSR_DW=3
endif

####################################################################################################
## Include the tool Makefile below                                                                ##
## Dont add anything else below it!                                                               ##
####################################################################################################
include ${DV_DIR}/../../../dv/tools/Makefile
