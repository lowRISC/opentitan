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
export DUT_TOP  := top_earlgrey
export TB_TOP   := tb
FUSESOC_CORE    := lowrisc:dv:chip_sim:0.1
COMPILE_KEY     ?= default
TOPS            := ${TB_TOP} xbar_main_bind

# Override RAL generation here
RAL_PKG_NAME    ?= chip
RAL_TOOL_OPTS   += --top

####################################################################################################
##                     A D D    I N D I V I D U A L    T E S T S    B E L O W                     ##
####################################################################################################
TEST_NAME       ?= chip_sanity
UVM_TEST        ?= chip_base_test
UVM_TEST_SEQ    ?= chip_base_vseq

# TODO don't check TLUL completion at the end of sim, current sim may complete before TL
# transaction is completed
RUN_OPTS        += +disable_assert_final_checks

ifeq (${TEST_NAME},chip_sanity)
  SW_DIR         = examples/hello_world
  SW_NAME        = hello_world
endif

ifeq (${TEST_NAME},chip_flash_test)
  SW_DIR         = tests/flash_ctrl
  SW_NAME        = flash_test
  RUN_OPTS      += +cpu_test_timeout_ns=15000000
endif

ifeq (${TEST_NAME},chip_sha256_test)
  SW_DIR         = tests/hmac
  SW_NAME        = sha256_test
  RUN_OPTS      += +cpu_test_timeout_ns=4000000
endif

ifeq (${TEST_NAME},chip_rv_timer_test)
  SW_DIR         = tests/rv_timer
  SW_NAME        = rv_timer_test
  RUN_OPTS      += +cpu_test_timeout_ns=4000000
endif

ifeq (${TEST_NAME},coremark)
  SW_DIR           = benchmarks/coremark
  SW_NAME          = coremark
  RUN_OPTS        += +cpu_test_timeout_ns=20000000
  SW_OPTS         += ITERATIONS=1
endif

ifeq (${TEST_NAME},chip_csr_hw_reset)
  UVM_TEST_SEQ   = chip_csr_vseq
  RUN_OPTS      += +csr_hw_reset
  RUN_OPTS      += +stub_cpu=1
  RUN_OPTS      += +en_scb=0
endif

ifeq (${TEST_NAME},chip_csr_rw)
  UVM_TEST_SEQ   = chip_csr_vseq
  RUN_OPTS      += +csr_rw
  RUN_OPTS      += +stub_cpu=1
  RUN_OPTS      += +en_scb=0
endif

ifeq (${TEST_NAME},chip_csr_bit_bash)
  UVM_TEST_SEQ   = chip_csr_vseq
  RUN_OPTS      += +csr_bit_bash
  RUN_OPTS      += +stub_cpu=1
  RUN_OPTS      += +en_scb=0
endif

ifeq (${TEST_NAME},chip_csr_aliasing)
  UVM_TEST_SEQ   = chip_csr_vseq
  RUN_OPTS      += +csr_aliasing
  RUN_OPTS      += +stub_cpu=1
  RUN_OPTS      += +en_scb=0
endif


####################################################################################################
## Include the tool Makefile below                                                                ##
## Dont add anything else below it!                                                               ##
####################################################################################################
include ${DV_DIR}/../../dv/tools/Makefile
