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
export DUT_TOP  := gpio
export TB_TOP   := tb
FUSESOC_CORE    := lowrisc:dv:gpio_sim:0.1
COMPILE_KEY     ?= default
COV_DUT_EXCL    ?= ${DV_DIR}/cov/gpio_cov_excl.el

####################################################################################################
##                     A D D    I N D I V I D U A L    T E S T S    B E L O W                     ##
####################################################################################################
TEST_NAME       ?= gpio_sanity
UVM_TEST        ?= gpio_base_test
UVM_TEST_SEQ    ?= gpio_base_vseq

# common tests/seqs
include ${DV_DIR}/../../../dv/tools/common_tests.mk

ifeq (${TEST_NAME},gpio_sanity)
  UVM_TEST_SEQ   = gpio_sanity_vseq
endif

ifeq (${TEST_NAME},gpio_sanity_no_pullup_pulldown)
  UVM_TEST_SEQ   = gpio_sanity_vseq
  RUN_OPTS      += +no_pullup_pulldown=1
endif

ifeq ($(TEST_NAME),gpio_random_dout_din)
  UVM_TEST_SEQ   = gpio_random_dout_din_vseq
endif

ifeq ($(TEST_NAME),gpio_random_dout_din_no_pullup_pulldown)
  UVM_TEST_SEQ   = gpio_random_dout_din_vseq
  RUN_OPTS      += +no_pullup_pulldown=1
endif

ifeq ($(TEST_NAME),gpio_dout_din_regs_random_rw)
  UVM_TEST_SEQ   = gpio_dout_din_regs_random_rw_vseq
endif

ifeq ($(TEST_NAME),gpio_intr_rand_pgm)
  UVM_TEST_SEQ   = gpio_intr_rand_pgm_vseq
  RUN_OPTS      += +do_clear_all_interrupts=0
endif

ifeq ($(TEST_NAME),gpio_rand_intr_trigger)
  UVM_TEST_SEQ   = gpio_rand_intr_trigger_vseq
  RUN_OPTS      += +do_clear_all_interrupts=0
endif

ifeq ($(TEST_NAME),gpio_intr_with_filter_rand_intr_event)
  UVM_TEST_SEQ   = gpio_intr_with_filter_rand_intr_event_vseq
  RUN_OPTS      += +en_scb=0
  RUN_OPTS      += +zero_delays=1
  RUN_OPTS      += +do_clear_all_interrupts=0
endif

ifeq ($(TEST_NAME),gpio_filter_stress)
  UVM_TEST_SEQ   = gpio_filter_stress_vseq
  RUN_OPTS      += +en_scb=0
  RUN_OPTS      += +do_clear_all_interrupts=0
endif

ifeq ($(TEST_NAME),gpio_random_long_reg_writes_reg_reads)
  UVM_TEST_SEQ   = gpio_random_long_reg_writes_reg_reads_vseq
  RUN_OPTS      += +do_clear_all_interrupts=0
endif

ifeq ($(TEST_NAME),gpio_full_random)
  UVM_TEST_SEQ   = gpio_full_random_vseq
  RUN_OPTS      += +do_clear_all_interrupts=0
endif

ifeq ($(TEST_NAME),gpio_stress_all)
  UVM_TEST_SEQ   = gpio_stress_all_vseq
  RUN_OPTS      += +do_clear_all_interrupts=0
endif

# gpio interrupt is sticky. Don't do clear interrupt and check at the end of 2 csr seq
ifeq (${TEST_NAME},gpio_csr_rw)
  RUN_OPTS      += +do_clear_all_interrupts=0
endif

ifeq (${TEST_NAME},gpio_csr_aliasing)
  RUN_OPTS      += +do_clear_all_interrupts=0
endif

ifeq (${TEST_NAME},gpio_same_csr_outstanding)
  RUN_OPTS      += +do_clear_all_interrupts=0
endif
####################################################################################################
## Include the tool Makefile below                                                                ##
## Dont add anything else below it!                                                               ##
####################################################################################################
include ${DV_DIR}/../../../dv/tools/Makefile

