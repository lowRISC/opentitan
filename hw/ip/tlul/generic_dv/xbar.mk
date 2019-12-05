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
export TB_TOP   := tb
COMPILE_KEY     ?= default

####################################################################################################
##                     A D D    I N D I V I D U A L    T E S T S    B E L O W                     ##
####################################################################################################
TEST_NAME       ?= xbar_sanity
UVM_TEST        ?= xbar_base_test
UVM_TEST_SEQ    ?= xbar_base_vseq

ifeq (${TEST_NAME},xbar_sanity)
  UVM_TEST_SEQ   = xbar_sanity_vseq
endif

ifeq (${TEST_NAME},xbar_sanity_zero_delays)
  UVM_TEST_SEQ   = xbar_sanity_vseq
  RUN_OPTS      += +zero_delays=1
endif

# max outstanding 64, max 1000 cycle seems big enough
ifeq (${TEST_NAME},xbar_sanity_large_delays)
  UVM_TEST_SEQ   = xbar_sanity_vseq
  RUN_OPTS      += +max_host_req_delay=1000
  RUN_OPTS      += +max_host_rsp_delay=1000
  RUN_OPTS      += +max_device_req_delay=1000
  RUN_OPTS      += +max_device_rsp_delay=1000
endif

ifeq (${TEST_NAME},xbar_sanity_slow_rsp)
  UVM_TEST_SEQ   = xbar_sanity_vseq
  RUN_OPTS      += +max_host_req_delay=10
  RUN_OPTS      += +max_host_rsp_delay=1000
  RUN_OPTS      += +max_device_req_delay=1000
  RUN_OPTS      += +max_device_rsp_delay=10
endif

ifeq (${TEST_NAME},xbar_random)
  UVM_TEST_SEQ   = xbar_random_vseq
endif

ifeq (${TEST_NAME},xbar_random_zero_delays)
  UVM_TEST_SEQ   = xbar_random_vseq
  RUN_OPTS      += +zero_delays=1
endif

ifeq (${TEST_NAME},xbar_random_large_delays)
  UVM_TEST_SEQ   = xbar_random_vseq
  RUN_OPTS      += +max_host_req_delay=1000
  RUN_OPTS      += +max_host_rsp_delay=1000
  RUN_OPTS      += +max_device_req_delay=1000
  RUN_OPTS      += +max_device_rsp_delay=1000
endif

ifeq (${TEST_NAME},xbar_random_slow_rsp)
  UVM_TEST_SEQ   = xbar_random_vseq
  RUN_OPTS      += +max_host_req_delay=10
  RUN_OPTS      += +max_host_rsp_delay=1000
  RUN_OPTS      += +max_device_req_delay=1000
  RUN_OPTS      += +max_device_rsp_delay=10
endif

ifeq (${TEST_NAME},xbar_access_same_device)
  UVM_TEST_SEQ   = xbar_access_same_device_vseq
endif

ifeq (${TEST_NAME},xbar_access_same_device_slow_rsp)
  UVM_TEST_SEQ   = xbar_access_same_device_vseq
  RUN_OPTS      += +max_host_req_delay=10
  RUN_OPTS      += +max_host_rsp_delay=1000
  RUN_OPTS      += +max_device_req_delay=1000
  RUN_OPTS      += +max_device_rsp_delay=10
endif

ifeq (${TEST_NAME},xbar_same_source)
  UVM_TEST_SEQ   = xbar_same_source_vseq
endif

ifeq (${TEST_NAME},xbar_error_random)
  UVM_TEST       = xbar_error_test
  UVM_TEST_SEQ   = xbar_random_vseq
endif

ifeq (${TEST_NAME},xbar_unmapped_addr)
  UVM_TEST_SEQ   = xbar_unmapped_addr_vseq
endif

ifeq (${TEST_NAME},xbar_error_and_unmapped_addr)
  UVM_TEST       = xbar_error_test
  UVM_TEST_SEQ   = xbar_unmapped_addr_vseq
endif

ifeq (${TEST_NAME},xbar_stress_all)
  UVM_TEST_SEQ   = xbar_stress_all_vseq
endif

ifeq (${TEST_NAME},xbar_stress_all_with_error)
  UVM_TEST       = xbar_error_test
  UVM_TEST_SEQ   = xbar_stress_all_vseq
endif

ifeq (${TEST_NAME},xbar_stress_all_with_reset)
  UVM_TEST_SEQ   = xbar_stress_all_with_reset_vseq
endif

ifeq (${TEST_NAME},xbar_stress_all_with_reset_error)
  UVM_TEST       = xbar_error_test
  UVM_TEST_SEQ   = xbar_stress_all_with_reset_vseq
endif

####################################################################################################
## Include the tool Makefile below                                                                ##
## Dont add anything else below it!                                                               ##
####################################################################################################
include ${DV_DIR}/../../../dv/tools/Makefile
