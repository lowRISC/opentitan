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
export DUT_TOP  := aes
export TB_TOP   := tb
FUSESOC_CORE    := lowrisc:dv:aes_sim:0.1
COMPILE_KEY     ?= default

UVM_TEST        ?= aes_base_test
UVM_TEST_SEQ    ?= aes_base_vseq

####################################################################################################
##                     A D D    I N D I V I D U A L    T E S T S    B E L O W                     ##
####################################################################################################
# common tests/seqs
include ${DV_DIR}/../../../dv/tools/common_tests.mk

TEST_NAME       ?= aes_sanity
UVM_TEST        ?= aes_base_test
UVM_TEST_SEQ    ?= aes_base_vseq

ifeq (${TEST_NAME},aes_wake_up_test)
  UVM_TEST_SEQ   = aes_wake_up_vseq
endif

ifeq (${TEST_NAME},aes_sanity)
  UVM_TEST_SEQ   = aes_sanity_vseq
endif

ifeq (${TEST_NAME},aes_intr_test)
  UVM_TEST_SEQ   = aes_common_vseq
  RUN_OPTS      += +run_intr_test
endif

ifeq (${TEST_NAME},aes_csr_hw_reset)
  UVM_TEST_SEQ   = aes_common_vseq
  RUN_OPTS      += +csr_hw_reset
  RUN_OPTS      += +en_scb=0
endif

ifeq (${TEST_NAME},aes_csr_rw)
  UVM_TEST_SEQ   = aes_common_vseq
  RUN_OPTS      += +csr_rw
  RUN_OPTS      += +en_scb=0
endif

ifeq (${TEST_NAME},aes_csr_bit_bash)
  UVM_TEST_SEQ   = aes_common_vseq
  RUN_OPTS      += +csr_bit_bash
  RUN_OPTS      += +en_scb=0
endif

ifeq (${TEST_NAME},aes_csr_aliasing)
  UVM_TEST_SEQ   = aes_common_vseq
  RUN_OPTS      += +csr_aliasing
  RUN_OPTS      += +en_scb=0
endif

# TODO: remove this test if there are no memories in the DUT
  ifeq (${TEST_NAME},aes_mem_walk)
  UVM_TEST_SEQ   = aes_common_vseq
  RUN_OPTS      += +csr_mem_walk
  RUN_OPTS      += +en_scb=0
endif

####################################################################################################
## Include the tool Makefile below                                                                ##
## Dont add anything else below it!                                                               ##
####################################################################################################
include ${DV_DIR}/../../../dv/tools/Makefile
