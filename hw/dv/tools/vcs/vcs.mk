####################################################################################################
## Copyright lowRISC contributors.                                                                ##
## Licensed under the Apache License, Version 2.0, see LICENSE for details.                       ##
## SPDX-License-Identifier: Apache-2.0                                                            ##
####################################################################################################
## Makefile option groups that can be enabled by test Makefile / command line.                    ##
## These are generic set of option groups that apply to all testbenches.                          ##
####################################################################################################
# Simulator too specific options
# Mandatory items to set (these are used by rules.mk):
# SIMCC       - Simulator compiler used to build / elaborate the bench
# SIMX        - Simulator executable used to run the tests

SIMCC       := vcs
SIMX        ?= ${BUILD_DIR}/simv
SIM_SETUP   ?= ${MAKE_ROOT}/vcs/vcs_fsdb.tcl

# set standard build options
BUILD_OPTS  += -sverilog -full64 -licqueue -timescale=1ns/1ps -kdb
BUILD_OPTS  += -ntb_opts uvm-1.2
BUILD_OPTS  += -Mdir=${BUILD_DIR}/simv.csrc
BUILD_OPTS  += -l ${BUILD_LOG}
BUILD_OPTS  += -o ${SIMX}
BUILD_OPTS  += -f ${SV_FLIST}
BUILD_OPTS  += +incdir+${BUILD_DIR}
BUILD_OPTS  += -debug_access+pp
BUILD_OPTS  += +warn=noUII-L
# turn on warnings if functions are called with return value ignored
BUILD_OPTS  += +warn=SV-NFIVC
# option below is required for $error / $fatal system calls
BUILD_OPTS  += -assert svaext

# set standard run options
RUN_OPTS    += -licqueue
RUN_OPTS    += -ucli -do ${SIM_SETUP}
RUN_OPTS    += +ntb_random_seed=${SEED}
RUN_OPTS    += +UVM_VERBOSITY=${UVM_VERBOSITY}
RUN_OPTS    += +UVM_TESTNAME=${UVM_TEST}
RUN_OPTS    += +UVM_TEST_SEQ=${UVM_TEST_SEQ}
RUN_OPTS    += -l ${RUN_LOG}

#########################
## Tool Specific Modes ##
#########################

# Enable simulation profiling
VCS_SIMPROFILE ?= 0
ifeq (${VCS_SIMPROFILE},1)
  BUILD_OPTS  += -simprofile
  RUN_OPTS    += -simprofile time
endif

# Enable waves
VCS_WAVES ?= 0
ifeq (${VCS_WAVES},1)
  BUILD_OPTS  += -debug_access+all
endif

# Enable coverage
VCS_COV ?= 0
ifeq (${VCS_COV},1)
  COV_METRICS ?= line+cond+fsm+tgl+branch+assert
  BUILD_OPTS  += -cm ${COV_METRICS}
  CM_HIER     ?=  ${MAKE_ROOT}/vcs/cover.cfg
  # Add -cm_hier switch if ${CM_HIER} file exists
  BUILD_OPTS  += $(shell if [ -f ${CM_HIER} ]; then echo "-cm_hier ${CM_HIER}"; fi)
  # Cover all continuous assignments
  BUILD_OPTS  += -cm_line contassign
  # Dump toggle coverage on mdas, array of structs and on ports only
  BUILD_OPTS  += -cm_tgl mda+structarr+portsonly
  # Ignore initial blocks for coverage
  BUILD_OPTS  += -cm_report noinitial
  # Filter unreachable/statically constant blocks
  BUILD_OPTS  += -cm_noconst
  # Don't count coverage that's coming from zero-time glitches
  BUILD_OPTS  += -cm_glitch 0
  # Ignore warnings about not applying cm_glitch to path and FSM
  BUILD_OPTS  += "+warn=noVCM-OPTIGN"
  # Coverage database output location
  BUILD_OPTS  += -cm_dir ${BUILD_DIR}/cov.vdb

  RUN_OPTS    += -cm ${COV_METRICS}
  # Same directory as build
  RUN_OPTS    += -cm_dir ${BUILD_DIR}/cov.vdb
  # Don't output cm.log which can be quite large
  RUN_OPTS    += -cm_log /dev/null
  # Provide a name to the coverage collected for this test
  RUN_OPTS    += -cm_name ${TEST_NAME}_${RUN_LOC}_${SEED}
  # Don't dump all the coverage assertion attempts at the end of simulation
  RUN_OPTS    += -assert nopostproc
endif

# Enable XPROP
XPROP ?= 1
ifeq (${XPROP},1)
  VCS_XPROP_CFG_FILE ?= ${MAKE_ROOT}/vcs/xprop.cfg
  BUILD_OPTS         += -xprop=${VCS_XPROP_CFG_FILE}
endif

# Coverage analyze/report options
COV_COMMON_EXCL  ?= ${MAKE_ROOT}/vcs/common_cov_excl.el
COV_EXCL         += ${COV_COMMON_EXCL} ${COV_DUT_EXCL}
COV_ANALYZE_TOOL ?= verdi
COV_REPORT_TOOL  ?= urg
COV_DIR          ?= ${BUILD_DIR}/cov.vdb
COV_EXCL_OPTS    ?= -line nocasedef -elfile ${COV_EXCL}
COV_ANALYZE_OPTS ?= -cov -covdir ${COV_DIR} ${COV_EXCL_OPTS}
COV_REPORT_OPTS  ?= -dir ${COV_DIR} ${COV_EXCL_OPTS} -report ${COV_REPORT_DIR}

# env variables to be exported for VCS
export VCS_ARCH_OVERRIDE      := linux
export VCS_LIC_EXPIRE_WARNING := 1
