####################################################################################################
## Copyright lowRISC contributors.                                                                ##
## Licensed under the Apache License, Version 2.0, see LICENSE for details.                       ##
## SPDX-License-Identifier: Apache-2.0                                                            ##
####################################################################################################
.DEFAULT_GOAL := all

all: build run

########################
## RAL target         ##
########################
ral:
ifneq (${SKIP_RAL_GEN},1)
	mkdir -p ${RAL_MODEL_DIR} && \
	${RAL_TOOL} ${RAL_TOOL_OPTS}
endif

###############################
## sim build and run targets ##
###############################
build: compile_result

pre_compile:
	mkdir -p ${BUILD_DIR} && \
	env > ${BUILD_DIR}/env_vars

gen_sv_flist: pre_compile ral
	cd ${BUILD_DIR} && ${SV_FLIST_GEN_TOOL} ${SV_FLIST_GEN_OPTS}

compile: gen_sv_flist
	cd ${SV_FLIST_GEN_DIR} && $(BUILD_JOB_OPTS) ${SIMCC} ${BUILD_OPTS} ${CL_BUILD_OPTS}

post_compile: compile

compile_result: post_compile

run: run_result

pre_run:
	rm -rf ${RUN_PATH}/latest
	mkdir -p ${RUN_DIR}
	ln -s ${RUN_DIR} ${RUN_PATH}/latest
	/bin/bash ${MAKE_ROOT}/run_dir_limiter ${RUN_PATH} ${RUN_DIR_LIMIT}
	env > ${RUN_DIR}/env_vars

# TODO: The rm -rf SW_BUILD_DIR below is necessary because currently
#       sw build dependency does not appear to be fully working with the DV flow
#       This should be investigated later or replaced with the new build system
sw_build: pre_run
ifneq (${SW_NAME},)
	rm -rf ${SW_BUILD_DIR}
	mkdir -p ${SW_BUILD_DIR}
	$(MAKE) -C $(SW_ROOT_DIR)/device \
	  TARGET=dv \
	  SW_DIR=boot_rom \
	  SW_BUILD_DIR=$(SW_BUILD_DIR)/rom \
	  MAKEFLAGS="$(SW_OPTS)"
	$(MAKE) -C $(SW_ROOT_DIR)/device \
	  TARGET=dv \
	  SW_DIR=$(SW_DIR) \
	  SW_NAME=$(SW_NAME) \
	  SW_BUILD_DIR=$(SW_BUILD_DIR)/sw \
	  MAKEFLAGS="$(SW_OPTS)"
endif

simulate: sw_build
	cd ${RUN_DIR} && $(RUN_JOB_OPTS) ${SIMX} ${RUN_OPTS} ${CL_RUN_OPTS}

post_run: simulate

run_result: post_run
	/bin/bash ${MAKE_ROOT}/pass_fail ${RUN_LOG} ${MAKE_ROOT}/pass_patterns ${MAKE_ROOT}/fail_patterns

############################
## coverage rated targets ##
############################
cov_merge:
	# TODO: add script to merge coverage in scratch scope

# open coverage tool to review and create report or exclusion file
cov_analyze:
	cd ${SCRATCH_PATH} && ${COV_ANALYZE_TOOL} ${COV_ANALYZE_OPTS}

# generate coverage report directly
cov_report:
	cd ${SCRATCH_PATH} && ${COV_REPORT_TOOL} ${COV_REPORT_OPTS}

clean:
	rm -rf ${SCRATCH_PATH}/*

.PHONY: ral \
	build \
	run \
	reg \
	pre_compile \
	compile \
	post_compile \
	compile_result \
	sw_build \
	pre_run \
	simulate \
	post_run \
	run_result \
	cov_merge \
	cov_analyze \
	cov_report \
	clean
