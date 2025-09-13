# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

export SHELL  := /usr/bin/env bash
.DEFAULT_GOAL := all

LOCK_ROOT_DIR ?= flock --timeout 3600 ${proj_root} --command

all: build run

###############################
## sim build and run targets ##
###############################
build: build_result

pre_build:
	@echo -e "\n[make]: pre_build"
	mkdir -p ${build_dir}
ifneq (${pre_build_cmds},)
	# pre_build_cmds are likely changing the in-tree sources. We hence use FLOCK
	# utility to prevent multiple builds that may be running in parallel from
	# stepping on each other. TODO: Enforce the list of pre_build_cmds is
	# identical across all build modes.
	${LOCK_ROOT_DIR} "cd ${build_dir} && ${pre_build_cmds}"
endif

gen_sv_flist: pre_build
	@echo -e "\n[make]: gen_sv_flist"
ifneq (${sv_flist_gen_cmd},)
	cd ${build_dir} && ${sv_flist_gen_cmd} ${sv_flist_gen_opts}
endif

do_build: gen_sv_flist
	@echo -e "\n[make]: build"
	cd ${sv_flist_gen_dir} && ${build_cmd} ${build_opts}

post_build: do_build
	@echo -e "\n[make]: post_build"
ifneq (${post_build_cmds},)
	cd ${build_dir} && ${post_build_cmds}
endif

build_result: post_build
	@echo -e "\n[make]: build_result"

run: run_result

pre_run:
	@echo -e "\n[make]: pre_run"
	mkdir -p ${run_dir}
ifneq (${pre_run_cmds},)
	cd ${run_dir} && ${pre_run_cmds}
endif

sw_build: pre_run
	@echo -e "\n[make]: sw_build"
ifneq (${sw_images},)
	cd ${proj_root} && ${sw_build_cmd} --build-seed=${build_seed}
endif

simulate: sw_build
	@echo -e "\n[make]: simulate"
	cd ${run_dir} && ${run_cmd} ${run_opts}

post_run: simulate
	@echo -e "\n[make]: post_run"
ifneq (${post_run_cmds},)
	cd ${run_dir} && ${post_run_cmds}
endif

run_result: post_run
	@echo -e "\n[make]: run_result"

#######################
## Load waves target ##
#######################
debug_waves:
	${debug_waves_cmd} ${debug_waves_opts}

############################
## coverage rated targets ##
############################
cov_unr_build: gen_sv_flist
	@echo -e "\n[make]: cov_unr_build"
	cd ${sv_flist_gen_dir} && ${cov_unr_build_cmd} ${cov_unr_build_opts}

cov_unr_vcs: cov_unr_build
	@echo -e "\n[make]: cov_unr"
	cd ${sv_flist_gen_dir} && ${cov_unr_run_cmd} ${cov_unr_run_opts}

cov_unr_xcelium:
	@echo -e "\n[make]: cov_unr"
	mkdir -p ${cov_unr_dir}
	cd ${cov_unr_dir} && ${cov_unr_run_cmd} ${cov_unr_run_opts}

cov_unr_merge:
	@echo -e "\n[make]: cov_unr_merge"
	cd ${cov_unr_dir} && ${job_prefix} ${cov_merge_cmd} -init ${cov_unr_dir}/jgproject/sessionLogs/session_0/unr_imc_coverage_merge.cmd

ifeq (${SIMULATOR}, xcelium)
  cov_unr: cov_unr_xcelium cov_unr_merge
else
  cov_unr: cov_unr_vcs
endif

# Merge coverage if there are multiple builds.
cov_merge:
	@echo -e "\n[make]: cov_merge"
	${job_prefix} ${cov_merge_cmd} ${cov_merge_opts}

# Generate coverage reports.
cov_report:
	@echo -e "\n[make]: cov_report"
	${cov_report_cmd} ${cov_report_opts}

# Open coverage tool to review and create report or exclusion file.
cov_analyze:
	@echo -e "\n[make]: cov_analyze"
	${cov_analyze_cmd} ${cov_analyze_opts}

.PHONY: build \
	pre_build \
	gen_sv_flist \
	do_build \
	post_build \
	build_result \
	run \
	pre_run \
	sw_build \
	simulate \
	post_run \
	run_result \
	debug_waves \
	cov_merge \
	cov_analyze \
	cov_report
