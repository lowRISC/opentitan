####################################################################################################
## Copyright lowRISC contributors.                                                                ##
## Licensed under the Apache License, Version 2.0, see LICENSE for details.                       ##
## SPDX-License-Identifier: Apache-2.0                                                            ##
####################################################################################################
.DEFAULLT_GOAL := all

all: build run

########################
## RAL target         ##
########################
ral:
ifneq (${skip_gen_ral_pkg},1)
	mkdir -p ${gen_ral_pkg_dir} && \
	${gen_ral_pkg_cmd} ${gen_ral_pkg_opts}
endif


###############################
## sim build and run targets ##
###############################
build: compile_result

pre_compile:
	@echo "[make]: pre_compile"
	mkdir -p ${build_dir} && env > ${build_dir}/env_vars

gen_sv_flist: pre_compile ral
	@echo "[make]: gen_sv_flist"
	cd ${build_dir} && ${sv_flist_gen_cmd} ${sv_flist_gen_opts}

compile: gen_sv_flist
	@echo "[make]: compile"
	cd ${sv_flist_gen_dir} && ${build_cmd} ${build_opts}

post_compile: compile
	@echo "[make]: post_compile"

compile_result: post_compile
	@echo "[make]: compile_result"

run: run_result

pre_run:
	@echo "[make]: pre_run"
	mkdir -p ${run_dir} && env > ${run_dir}/env_vars

sw_build: pre_run
	@echo "[make]: sw_build"
ifneq (${sw_name},)
	$(error "sw_build target is not supported yet")
endif

simulate: sw_build
	@echo "[make]: simulate"
	cd ${run_dir} && ${run_cmd} ${run_opts}

post_run: simulate
	@echo "[make]: post_run"

run_result: post_run
	@echo "[make]: run_result"

#######################
## Load waves target ##
#######################
debug_waves:
	${debug_waves_cmd} ${debug_waves_opts}

############################
## coverage rated targets ##
############################
cov_merge:
	# TODO: add script to merge coverage in scratch scope

# open coverage tool to review and create report or exclusion file
cov_analyze:
	cd ${scratch_path} && ${cov_analyze_cmd} ${cov_analyze_opts}

# generate coverage report directly
cov_report:
	cd ${scratch_path} && ${cov_report} ${cov_report_opts}

clean:
	echo "[make]: clean"
	rm -rf ${scratch_root}/${dut}/*

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
