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
export DUT_TOP  := rv_timer
export TB_TOP   := tb
FUSESOC_CORE    := lowrisc:dv:rv_timer_sim:0.1
COMPILE_KEY     ?= default

####################################################################################################
##                     A D D    I N D I V I D U A L    T E S T S    B E L O W                     ##
####################################################################################################
TEST_NAME       ?= rv_timer_sanity
UVM_TEST        ?= rv_timer_base_test
UVM_TEST_SEQ    ?= rv_timer_base_vseq

# common tests/seqs
include ${DV_DIR}/../../../dv/tools/common_tests.mk

ifeq (${TEST_NAME},rv_timer_sanity)
  UVM_TEST_SEQ   = rv_timer_sanity_vseq
endif

ifeq (${TEST_NAME},rv_timer_disabled)
  UVM_TEST_SEQ   = rv_timer_disabled_vseq
endif

ifeq (${TEST_NAME},rv_timer_cfg_update_on_fly)
  UVM_TEST_SEQ   = rv_timer_cfg_update_on_fly_vseq
  RUN_OPTS      += +zero_delays=1
  RUN_OPTS      += +test_timeout_ns=10_000_000_000
endif

ifeq (${TEST_NAME},rv_timer_random_reset)
  UVM_TEST_SEQ   = rv_timer_random_reset_vseq
endif

ifeq (${TEST_NAME},rv_timer_stress_all)
  UVM_TEST_SEQ   = rv_timer_stress_all_vseq
  RUN_OPTS      += +test_timeout_ns=10_000_000_000
endif

####################################################################################################
## Include the tool Makefile below                                                                ##
## Dont add anything else below it!                                                               ##
####################################################################################################
include ${DV_DIR}/../../../dv/tools/Makefile

