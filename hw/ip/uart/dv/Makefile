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
export DUT_TOP  := uart
export TB_TOP   := tb
FUSESOC_CORE    := lowrisc:dv:uart_sim:0.1
COMPILE_KEY     ?= default

COV_DUT_EXCL    ?= ${DV_DIR}/cov/uart_cov_excl.el
####################################################################################################
##                     A D D    I N D I V I D U A L    T E S T S    B E L O W                     ##
####################################################################################################
TEST_NAME       ?= uart_sanity
UVM_TEST        ?= uart_base_test
UVM_TEST_SEQ    ?= uart_base_vseq

# common tests/seqs
include ${DV_DIR}/../../../dv/tools/common_tests.mk

ifeq (${TEST_NAME},uart_sanity)
  UVM_TEST_SEQ   = uart_sanity_vseq
endif

ifeq (${TEST_NAME},uart_tx_rx)
  UVM_TEST_SEQ   = uart_tx_rx_vseq
endif

ifeq (${TEST_NAME},uart_fifo_full)
  UVM_TEST_SEQ   = uart_fifo_full_vseq
endif

ifeq (${TEST_NAME},uart_fifo_overflow)
  UVM_TEST_SEQ   = uart_fifo_overflow_vseq
endif

ifeq (${TEST_NAME},uart_fifo_reset)
  UVM_TEST_SEQ   = uart_fifo_reset_vseq
endif

ifeq (${TEST_NAME},uart_rx_oversample)
  UVM_TEST_SEQ   = uart_rx_oversample_vseq
  RUN_OPTS      += +zero_delays=1
endif

ifeq (${TEST_NAME},uart_intr)
  RUN_OPTS      += +test_timeout_ns=3000_000_000
  UVM_TEST_SEQ   = uart_intr_vseq
endif

ifeq (${TEST_NAME},uart_noise_filter)
  UVM_TEST_SEQ   = uart_noise_filter_vseq
endif

ifeq (${TEST_NAME},uart_rx_start_bit_filter)
  UVM_TEST_SEQ   = uart_rx_start_bit_filter_vseq
endif

ifeq (${TEST_NAME},uart_rx_parity_err)
  UVM_TEST_SEQ   = uart_rx_parity_err_vseq
endif

ifeq (${TEST_NAME},uart_tx_ovrd)
  UVM_TEST_SEQ   = uart_tx_ovrd_vseq
endif

ifeq (${TEST_NAME},uart_loopback)
  UVM_TEST_SEQ   = uart_loopback_vseq
endif

ifeq (${TEST_NAME},uart_perf)
  UVM_TEST_SEQ   = uart_perf_vseq
  RUN_OPTS      += +zero_delays=1
endif

ifeq (${TEST_NAME},uart_stress_all)
  RUN_OPTS      += +test_timeout_ns=10_000_000_000
  UVM_TEST_SEQ   = uart_stress_all_vseq
endif

####################################################################################################
## Include the tool Makefile below                                                                ##
## Dont add anything else below it!                                                               ##
####################################################################################################
include ${DV_DIR}/../../../dv/tools/Makefile
