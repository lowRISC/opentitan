# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Common dvsim 'flow_makefile' for OpenTitan simulation flows
#
# The special phony targets 'build' and 'run' in this makefile are invoked by the dvsim
# tool to execute the build and run phases respectively. Arbitrary other targets/rules
# can be created in support of running the two overarching simulation phases, and
# any project constituent sim_cfg .hjson files can be used to define new variables which
# are then substituted into the rules defined here.
#
# Aside from the (hopefully-obvious) pre_ and post_ targets used here, OpenTitan defines
# the following targets
# - gen_sv_flist
#     Generates the filelists (.f) used by EDA tools to build the testbench / simulation
#     environment using FuseSoC. FuseSoC is a package manager and a build system for HDL,
#     but in this configuration it is being used primarily as a package manager.
# - sw_build
#     Build any binary images to be loaded into simulation memory models, typically by
#     compiling application software using the Bazel build system.

.DEFAULT_GOAL := all

.PHONY: all build run
all: build run
build: build_result
run: run_result

.PHONY: \
	###############
	# Build-Phase #
	###############
	pre_build \
	gen_sv_flist \         # Generate filelist using FuseSoC
	do_build \             # Build the testbench / testbench executable
	post_build \
	build_result \
	#############
	# Run-Phase #
	#############
	pre_run \
	sw_build \             # Build simulation software / binary images using Bazel
	simulate \             # Run the simulation
	post_run \
	run_result \
	############
	# Coverage #
	############
	cov_unr_build \
	cov_unr_vcs \
	cov_unr_xcelium \
	cov_unr_merge \
	cov_unr \
	cov_merge \            # Merge coverage if there are multiple builds
	cov_analyze \          # Open coverage tool to review and create report or exclusion file
	cov_report             # Generate coverage reports

export SHELL  := /bin/bash

LOCK_ROOT_DIR ?= flock --timeout 3600 ${proj_root} --command

###############
# Build-Phase #
################################################################################

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

#############
# Run-Phase #
################################################################################

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

############
# Coverage #
################################################################################

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

cov_merge:
	@echo -e "\n[make]: cov_merge"
	${job_prefix} ${cov_merge_cmd} ${cov_merge_opts}

cov_report:
	@echo -e "\n[make]: cov_report"
	${cov_report_cmd} ${cov_report_opts}

cov_analyze:
	@echo -e "\n[make]: cov_analyze"
	${cov_analyze_cmd} ${cov_analyze_opts}
