####################################################################################################
## Copyright lowRISC contributors.                                                                ##
## Licensed under the Apache License, Version 2.0, see LICENSE for details.                       ##
## SPDX-License-Identifier: Apache-2.0                                                            ##
####################################################################################################
## Entry point test Makefile for building and running tests.                                      ##
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
export DUT_TOP  := alert_handler
export TB_TOP   := tb
FUSESOC_CORE    := lowrisc:dv:alert_handler_sim:0.1
COMPILE_KEY     ?= default

UVM_TEST        ?= alert_handler_base_test
UVM_TEST_SEQ    ?= alert_handler_base_vseq

####################################################################################################
##                     A D D    I N D I V I D U A L    T E S T S    B E L O W                     ##
####################################################################################################
TEST_NAME       ?= alert_handler_sanity
UVM_TEST        ?= alert_handler_base_test
UVM_TEST_SEQ    ?= alert_handler_base_vseq

 ifeq (${TEST_NAME},alert_handler_sanity)
   UVM_TEST_SEQ   = alert_handler_sanity_vseq
 endif

####################################################################################################
## Include the tool Makefile below                                                                ##
## Dont add anything else below it!                                                               ##
####################################################################################################
include ${DV_DIR}/../../../dv/tools/Makefile
