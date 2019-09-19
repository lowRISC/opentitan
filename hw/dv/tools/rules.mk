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

# TODO: clean this (capp tooling infrastructure)
capp: pre_run
ifneq (${CAPP_NAME},)
	# Recursive make calls
	make distclean -C ${SW_DIR}/boot_rom
	make -C ${SW_DIR}/boot_rom
	make distclean -C ${SW_DIR}/tests/${CAPP_NAME} MAKEFLAGS=$(CAPP_BUILD_OPTS)
	make -C ${PRJ_DIR}/sw/tests/${CAPP_NAME} MAKEFLAGS=$(CAPP_BUILD_OPTS) \
	PROGRAM_CFLAGS=$(PROGRAM_CFLAGS)

	# Copy outputs over to run area
	cp $(SW_DIR)/boot_rom/boot_rom.vmem ${RUN_DIR}/rom.vmem
	cp ${SW_DIR}/tests/${CAPP_NAME}/${CAPP_NAME}.vmem ${RUN_DIR}/main.vmem
	cp ${SW_DIR}/tests/${CAPP_NAME}/${CAPP_NAME}.dis ${RUN_DIR}/main.dis
	cp ${SW_DIR}/tests/${CAPP_NAME}/${CAPP_NAME}.map ${RUN_DIR}/main.map

endif

simulate: capp
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
	pre_run \
	simulate \
	post_run \
	run_result
