####################################################################################################
## Copyright lowRISC contributors.                                                                ##
## Licensed under the Apache License, Version 2.0, see LICENSE for details.                       ##
## SPDX-License-Identifier: Apache-2.0                                                            ##
####################################################################################################
all: build run

########################
## standalone targets ##
########################
ral:
	${RAL_TOOL} ${RAL_TOOL_OPTS}

cov_merge:
	# TODO: add script to merge coverage in scratch scope

###############################
## sim build and run targets ##
###############################
build: compile_result

pre_compile:
	mkdir -p ${BUILD_DIR} && \
	env > ${BUILD_DIR}/env_vars

gen_sv_flist: pre_compile
	cd ${BUILD_DIR} && ${SV_FLIST_GEN_TOOL} ${SV_FLIST_GEN_OPTS}

compile: gen_sv_flist
	$(BUILD_JOB_OPTS) cd ${SV_FLIST_GEN_DIR} && ${SIMCC} ${BUILD_OPTS} ${CL_BUILD_OPTS}

post_compile: compile

compile_result: post_compile

run: run_result

pre_run:
	rm -rf ${RUN_PATH}/latest
	mkdir -p ${RUN_DIR}
	ln -s ${RUN_DIR} ${RUN_PATH}/latest
	/bin/bash ${MAKE_ROOT}/run_dir_limiter ${RUN_PATH} ${RUN_DIR_LIMIT}
	env > ${RUN_DIR}/env_vars

sw_build: pre_run
ifneq (${SW_NAME},)
	mkdir -p ${SW_BUILD_DIR}
	$(MAKE) -C $(SW_ROOT_DIR) \
	  TARGET=dv \
	  SW_DIR=boot_rom \
	  SW_BUILD_DIR=$(SW_BUILD_DIR)/rom \
	  MAKEFLAGS="$(SW_OPTS)"
	$(MAKE) -C $(SW_ROOT_DIR) \
	  TARGET=dv \
	  SW_DIR=$(SW_DIR) \
	  SW_NAME=$(SW_NAME) \
	  SW_BUILD_DIR=$(SW_BUILD_DIR)/sw \
	  MAKEFLAGS="$(SW_OPTS)"
endif

simulate: sw_build
	$(RUN_JOB_OPTS) cd ${RUN_DIR} && ${SIMX} ${RUN_OPTS} ${CL_RUN_OPTS}

post_run: simulate

run_result: post_run
	/bin/bash ${MAKE_ROOT}/pass_fail ${RUN_LOG} ${MAKE_ROOT}/pass_patterns ${MAKE_ROOT}/fail_patterns

clean:
	rm -rf ${SCRATCH_PATH}/*

.PHONY: build \
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
	run_result
