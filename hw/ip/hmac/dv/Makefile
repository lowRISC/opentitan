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
export DUT_TOP  := hmac
export TB_TOP   := tb
FUSESOC_CORE    := lowrisc:dv:hmac_sim:0.1
COMPILE_KEY     ?= default

####################################################################################################
##                     A D D    I N D I V I D U A L    T E S T S    B E L O W                     ##
####################################################################################################
TEST_NAME       ?= hmac_sanity
UVM_TEST        ?= hmac_base_test
UVM_TEST_SEQ    ?= hmac_base_vseq

ifeq (${TEST_NAME},hmac_sanity)
  UVM_TEST_SEQ   = hmac_sanity_vseq
endif

ifeq (${TEST_NAME},hmac_long_msg)
  UVM_TEST_SEQ   = hmac_long_msg_vseq
endif

ifeq (${TEST_NAME},hmac_back_pressure)
  UVM_TEST_SEQ   = hmac_back_pressure_vseq
  RUN_OPTS      += +zero_delays=1
endif

ifeq (${TEST_NAME},hmac_nist_sha_vectors)
  UVM_TEST_SEQ   = hmac_nist_vectors_vseq
  RUN_OPTS      += +nist_vectors_dir=${DV_DIR}/../../../dv/sv/nist_vectors/
endif

ifeq (${TEST_NAME},hmac_csr_hw_reset)
  UVM_TEST_SEQ   = hmac_csr_vseq
  RUN_OPTS      += +csr_hw_reset
  RUN_OPTS      += +en_scb=0
endif

ifeq (${TEST_NAME},hmac_csr_rw)
  UVM_TEST_SEQ   = hmac_csr_vseq
  RUN_OPTS      += +csr_rw
  RUN_OPTS      += +en_scb=0
endif

ifeq (${TEST_NAME},hmac_csr_bit_bash)
  UVM_TEST_SEQ   = hmac_csr_vseq
  RUN_OPTS      += +csr_bit_bash
  RUN_OPTS      += +en_scb=0
endif

ifeq (${TEST_NAME},hmac_csr_aliasing)
  UVM_TEST_SEQ   = hmac_csr_vseq
  RUN_OPTS      += +csr_aliasing
  RUN_OPTS      += +en_scb=0
endif

####################################################################################################
## Include the tool Makefile below                                                                ##
## Dont add anything else below it!                                                               ##
####################################################################################################
include ${DV_DIR}/../../../dv/tools/Makefile
