# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

.DEFAULT_GOAL := all

all: build run

###############################
## sim build and run targets ##
###############################
build: compile_result

prep_tool_srcs:
	@echo "[make]: prep_tool_srcs"
	mkdir -p ${tool_srcs_dir}
	cp -Ru ${tool_srcs} ${tool_srcs_dir}/.

pre_compile:
	@echo "[make]: pre_compile"
	mkdir -p ${build_dir}

gen_sv_flist: pre_compile prep_tool_srcs
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
	mkdir -p ${run_dir}

simulate:
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
# Merge coverage if there are multiple builds.
cov_merge:
	@echo "[make]: cov_merge"
	${cov_merge_cmd} ${cov_merge_opts}

# Open coverage tool to review and create report or exclusion file.
cov_analyze: prep_tool_srcs
	@echo "[make]: cov_analyze"
	${cov_analyze_cmd} ${cov_analyze_opts}

# Generate coverage reports.
cov_report:
	@echo "[make]: cov_report"
	${cov_report_cmd} ${cov_report_opts}

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
