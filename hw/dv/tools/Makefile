####################################################################################################
## Copyright lowRISC contributors.                                                                ##
## Licensed under the Apache License, Version 2.0, see LICENSE for details.                       ##
## SPDX-License-Identifier: Apache-2.0                                                            ##
####################################################################################################

# directory paths
# _ROOT are paths indicating a 'starting point'
# _PATH paths are intermediate paths leading to a _DIR
# _LOC are directory names without the hierarchy
# _DIR paths are final paths used in make rules
# All these variables can be overridden from the command line
# Test Makefile needs to set DV_DIR, DUT_TOP, TB_TOP, FUSESOC_CORE, COMPILE_KEY and TEST_NAME
# at minimum

export SHELL      := /bin/bash
TIMESTAMP         ?= $(shell date +%m.%d.%y_%H.%M.%S)
MAKE_ROOT         := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))
export PROJ_ROOT  := ${MAKE_ROOT}/../../..
export PRJ_DIR    := ${PROJ_ROOT}
export CURR_DIR   := $(shell pwd)
SCRATCH_ROOT      ?= ${DV_DIR}/scratch

SCRATCH_LOC       ?= ${DUT_TOP}
BUILD_LOC         ?= ${COMPILE_KEY}
RUN_LOC           ?= ${TIMESTAMP}

SCRATCH_PATH      ?= ${SCRATCH_ROOT}/${SCRATCH_LOC}
BUILD_DIR         := ${SCRATCH_PATH}/${BUILD_LOC}
RUN_PATH          ?= ${SCRATCH_PATH}/${TEST_NAME}
RUN_DIR           := ${RUN_PATH}/${RUN_LOC}
COV_REPORT_DIR    ?= ${SCRATCH_PATH}/cov_report
SW_BUILD_DIR      ?= ${RUN_DIR}/sw_build
SW_ROOT_DIR       := ${PRJ_DIR}/sw

JOB_OPTS          ?=
BUILD_JOB_OPTS    ?= $(JOB_OPTS)
RUN_JOB_OPTS      ?= $(JOB_OPTS)

# limit run directories upto a limit specified below
RUN_DIR_LIMIT     ?= 5

# global simulation specific variables (but simulator independent)
SEED              ?= $(shell od -vAn -N4 -tu < /dev/random | xargs)
BUILD_LOG         ?= ${BUILD_DIR}/build.log
RUN_LOG           ?= ${RUN_DIR}/run.log
UVM_VERBOSITY     ?= UVM_LOW

TOPS              ?= ${TB_TOP} ${DUT_TOP}_bind
####################################################################################################
## Options for SV build / C build / simulation run                                                ##
## CL_ prefix represents command line versions of these options - they should be empty and only   ##
## be set on the command line                                                                     ##
####################################################################################################
# BUILD_OPTS are passed to the simulator during the SV testbench compile step
CL_BUILD_OPTS     +=
BUILD_OPTS        += $(addprefix -top , $(TOPS))

# RUN_OPTS are passed to the simulation executable that is invoked to run the simulation
CL_RUN_OPTS       +=
RUN_OPTS          += +UVM_NO_RELNOTES

# SW_OPTS are options for SW apps that come with their own Makefile (example coremark)
CL_SW_OPTS        +=
SW_OPTS           += ${CL_SW_OPTS}

# SW_FLAGS are compiler flags / directives that we can pass for each test using our own Makefiles
CL_SW_FLAGS       +=
SW_FLAGS          += ${CL_SW_FLAGS}

# default project-wide bus widths
TL_AW             ?= 32
TL_DW             ?= 32
TL_DBW            ?= 4

# add auxiliary / helper mk files
# set simulator to vcs by default
SIMULATOR ?= vcs

# common tests/seqs
include ${MAKE_ROOT}/common_tests.mk

# tool to generate ral
include ${MAKE_ROOT}/ral_gen.mk

# tool to generate file list
include ${MAKE_ROOT}/fusesoc.mk

# modes / switches (option groups) that can be turned on easily
include ${MAKE_ROOT}/modes.mk

# add tool specific mk file
ifeq (${SIMULATOR},vcs)
  include ${MAKE_ROOT}/vcs/vcs.mk
else ifeq (${SIMULATOR},xcelium)
  include ${MAKE_ROOT}/xcelium/xcelium.mk
# else add other tool specific mk files
endif

# generic rules to sequence build and run flows
include ${MAKE_ROOT}/rules.mk
