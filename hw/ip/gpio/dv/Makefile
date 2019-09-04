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

####################################################################################################
##                     A D D    I N D I V I D U A L    T E S T S    B E L O W                     ##
####################################################################################################
TEST_NAME       ?= gpio_sanity
UVM_TEST        ?= gpio_base_test
UVM_TEST_SEQ    ?= gpio_base_vseq

ifeq (${TEST_NAME},gpio_sanity)
  UVM_TEST_SEQ   = gpio_sanity_vseq
endif

ifeq (${TEST_NAME},gpio_sanity_no_pullup_pulldown)
  UVM_TEST_SEQ   = gpio_sanity_vseq
  RUN_OPTS      += +no_pullup_pulldown=1
endif

ifeq (${TEST_NAME},gpio_intr_test)
  UVM_TEST_SEQ   = gpio_common_vseq
  RUN_OPTS      += +run_intr_test
endif

ifeq (${TEST_NAME},gpio_csr_hw_reset)
  UVM_TEST_SEQ   = gpio_common_vseq
  RUN_OPTS      += +csr_hw_reset
  RUN_OPTS      += +en_scb=0
endif

ifeq (${TEST_NAME},gpio_csr_rw)
  UVM_TEST_SEQ   = gpio_common_vseq
  RUN_OPTS      += +csr_rw
  RUN_OPTS      += +do_clear_all_interrupts=0
  RUN_OPTS      += +en_scb=0
endif

ifeq (${TEST_NAME},gpio_csr_bit_bash)
  UVM_TEST_SEQ   = gpio_common_vseq
  RUN_OPTS      += +csr_bit_bash
  RUN_OPTS      += +en_scb=0
endif

ifeq (${TEST_NAME},gpio_csr_aliasing)
  UVM_TEST_SEQ   = gpio_common_vseq
  RUN_OPTS      += +csr_aliasing
  RUN_OPTS      += +do_clear_all_interrupts=0
  RUN_OPTS      += +en_scb=0
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

ifeq ($(TEST_NAME),gpio_random_long_reg_writes_reg_reads)
  UVM_TEST_SEQ   = gpio_random_long_reg_writes_reg_reads_vseq
  RUN_OPTS      += +do_clear_all_interrupts=0
endif

####################################################################################################
## Include the tool Makefile below                                                                ##
## Dont add anything else below it!                                                               ##
####################################################################################################
include ${DV_DIR}/../../../dv/tools/Makefile

