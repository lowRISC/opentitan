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

sw_build: pre_run
ifneq (${SW_NAME},)
	# NOTE: Pass -f, since we're going to be re-building everything every time,
	# anyways.
	cd $(PROJ_ROOT) && \
	BUILD_ROOT=$(SW_BUILD_DIR)/meson $(PROJ_ROOT)/meson_init.sh -f
	# NOTE: We're using the fpga platform for now, because there is no
	# such thing as a DV platform yet (nor does any code do anything
	# special for DV yet).
	ninja -C $(SW_BUILD_DIR)/meson/build-out/sw/fpga all

	mkdir -p $(SW_BUILD_DIR)/sw $(SW_BUILD_DIR)/rom
	cp $(SW_BUILD_DIR)/meson/build-bin/sw/device/fpga/boot_rom/boot_rom.vmem \
		$(SW_BUILD_DIR)/rom/rom.vmem
	cp $(SW_BUILD_DIR)/meson/build-bin/sw/device/fpga/$(SW_DIR)/$(SW_NAME).vmem \
		$(SW_BUILD_DIR)/sw/sw.vmem
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
