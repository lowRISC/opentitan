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

TEST_PREFIX     ?= ${DUT_TOP}

ifeq (${TEST_NAME},${TEST_PREFIX}_csr_hw_reset)
  UVM_TEST_SEQ   = ${TEST_PREFIX}_common_vseq
  RUN_OPTS      += +csr_hw_reset
  RUN_OPTS      += +en_scb=0
endif

ifeq (${TEST_NAME},${TEST_PREFIX}_csr_rw)
  UVM_TEST_SEQ   = ${TEST_PREFIX}_common_vseq
  RUN_OPTS      += +csr_rw
  RUN_OPTS      += +en_scb=0
endif

ifeq (${TEST_NAME},${TEST_PREFIX}_csr_bit_bash)
  UVM_TEST_SEQ   = ${TEST_PREFIX}_common_vseq
  RUN_OPTS      += +csr_bit_bash
  RUN_OPTS      += +en_scb=0
endif

ifeq (${TEST_NAME},${TEST_PREFIX}_csr_aliasing)
  UVM_TEST_SEQ   = ${TEST_PREFIX}_common_vseq
  RUN_OPTS      += +csr_aliasing
  RUN_OPTS      += +en_scb=0
endif

ifeq (${TEST_NAME},${TEST_PREFIX}_same_csr_outstanding)
  UVM_TEST_SEQ   = ${TEST_PREFIX}_common_vseq
  RUN_OPTS      += +run_same_csr_outstanding
  RUN_OPTS      += +en_scb=0
endif

# make sure DUT has memory and support this seq before run the test
ifeq (${TEST_NAME},${TEST_PREFIX}_csr_mem_walk)
  UVM_TEST_SEQ   = ${TEST_PREFIX}_common_vseq
  RUN_OPTS      += +csr_mem_walk
  RUN_OPTS      += +en_scb=0
endif

ifeq (${TEST_NAME},${TEST_PREFIX}_tl_errors)
  UVM_TEST_SEQ   = ${TEST_PREFIX}_common_vseq
  RUN_OPTS      += +run_tl_errors
endif

ifeq (${TEST_NAME},${TEST_PREFIX}_intr_test)
  UVM_TEST_SEQ   = ${TEST_PREFIX}_common_vseq
  RUN_OPTS      += +run_intr_test
endif

ifeq (${TEST_NAME},${TEST_PREFIX}_stress_all_with_rand_reset)
  UVM_TEST_SEQ   = ${TEST_PREFIX}_common_vseq
  RUN_OPTS      += +run_stress_all_with_rand_reset
  RUN_OPTS      += +test_timeout_ns=10_000_000_000
  RUN_OPTS      += +stress_seq=${TEST_PREFIX}_stress_all_vseq
endif


