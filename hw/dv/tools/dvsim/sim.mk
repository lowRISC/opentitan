# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

export SHELL  := /bin/bash
.DEFAULT_GOAL := all

LOCK_ROOT_DIR ?= flock --timeout 3600 ${proj_root} --command

all: build run

###############################
## sim build and run targets ##
###############################
build: build_result

pre_build:
	@echo "[make]: pre_build"
	mkdir -p ${build_dir}
ifneq (${pre_build_cmds},)
	# pre_build_cmds are likely changing the in-tree sources. We hence use FLOCK
        # utility to prevent multiple builds that may be running in parallel from
        # stepping on each other. TODO: Enforce the list of pre_build_cmds is
        # identical across all build modes.
	${LOCK_ROOT_DIR} "cd ${build_dir} && ${pre_build_cmds}"
endif

gen_sv_flist: pre_build
	@echo "[make]: gen_sv_flist"
ifneq (${sv_flist_gen_cmd},)
	cd ${build_dir} && ${sv_flist_gen_cmd} ${sv_flist_gen_opts}
endif

do_build: gen_sv_flist
	@echo "[make]: build"
	cd ${sv_flist_gen_dir} && ${build_cmd} ${build_opts}

post_build: do_build
	@echo "[make]: post_build"
ifneq (${post_build_cmds},)
	cd ${build_dir} && ${post_build_cmds}
endif

build_result: post_build
	@echo "[make]: build_result"

run: run_result

pre_run:
	@echo "[make]: pre_run"
	mkdir -p ${run_dir}
ifneq (${pre_run_cmds},)
	cd ${run_dir} && ${pre_run_cmds}
endif

sw_build: pre_run
	@echo "[make]: sw_build"
ifneq (${sw_images},)
	# Loop through the list of sw_images and invoke Bazel on each.
	# `sw_images` is a space-separated list of tests to be built into an image.
	# Optionally, each item in the list can have additional metadata / flags using
	# the delimiter ':'. The format is as follows:
	# <Bazel label>:<index>:<flag1>:<flag2>
	#
	# If one delimiter is detected, then the full string is considered to be the
	# <Bazel label>. If two delimiters are detected, then it must be <Bazel label>
	# followed by <index>. The <flag> is considered optional.
	#
	# After the images are built, we use `bazel cquery ...` to locate the built
	# software artifacts so they can be copied to the test bench run directory.
	# We only copy device SW images, and do not copy host-side artifacts (like
	# opentitantool) that are also dependencies of the Bazel test target that
	# encode the software image targets.
	set -e; \
	for sw_image in ${sw_images}; do \
		if [[ -z $$sw_image ]]; then \
			echo "ERROR: SW image \"$$sw_image\" is malformed."; \
			echo "Expected format: <Bazel label>:<index>:<optional-flags>."; \
			exit 1; \
		fi; \
		prebuilt_path=`echo $$sw_image | cut -d: -f 1`; \
		bazel_target=`echo $$sw_image | cut -d: -f 2`; \
		index=`echo $$sw_image | cut -d: -f 3`; \
		flags=(`echo $$sw_image | cut -d: -f 4- --output-delimiter " "`); \
		bazel_label="`echo $$sw_image | cut -d: -f 1-2`"; \
		if [[ $${index} != 4 ]]; then \
			bazel_label="$${bazel_label}_$${sw_build_device}"; \
			bazel_cquery="labels(data, $${bazel_label}) union labels(srcs, $${bazel_label})"; \
		else \
			bazel_cquery="$${bazel_label}"; \
		fi; \
		cd ${proj_root}; \
		if [[ $${flags[@]} =~ "prebuilt" ]]; then \
			echo "SW image \"$$bazel_label\" is prebuilt - copying sources."; \
			cp ${proj_root}/$${prebuilt_path} $${run_dir}/`basename $${prebuilt_path}`; \
		else \
			echo "Building SW image \"$${bazel_label}\"."; \
			bazel_opts="${sw_build_opts} --define DISABLE_VERILATOR_BUILD=true"; \
			bazel_opts+=" --//hw/ip/otp_ctrl/data:img_seed=${seed}"; \
			if [[ "${build_seed}" != "None" ]]; then \
				bazel_opts+=" --//hw/ip/otp_ctrl/data:otp_seed=${build_seed}"; \
			fi; \
			if [[ -z $${BAZEL_PYTHON_WHEELS_REPO} ]]; then \
				echo "Building \"$${bazel_label}\" on network connected machine."; \
				bazel_cmd="./bazelisk.sh"; \
			else \
				echo "Building \"$${bazel_label}\" on air-gapped machine."; \
				bazel_opts+=" --define SPECIFY_BINDGEN_LIBSTDCXX=true"; \
				bazel_opts+=" --distdir=$${BAZEL_DISTDIR} --repository_cache=$${BAZEL_CACHE}"; \
				bazel_cmd="bazel"; \
			fi; \
			echo "Building with command: $${bazel_cmd} build $${bazel_opts} $${bazel_label}"; \
			$${bazel_cmd} build $${bazel_opts} $${bazel_label}; \
			for dep in $$($${bazel_cmd} cquery \
				$${bazel_cquery} \
				--ui_event_filters=-info \
				--noshow_progress \
				--output=starlark); do \
				if [[ $$dep != //hw* ]] && [[ $$dep != //util* ]] && [[ $$dep != //sw/host* ]]; then \
					for artifact in $$($${bazel_cmd} cquery $${dep} \
						--ui_event_filters=-info \
						--noshow_progress \
						--output=starlark \
						--starlark:expr="\"\\n\".join([f.path for f in target.files.to_list()])"); do \
						cp -f $${artifact} $${run_dir}/$$(basename $${artifact}); \
						if [[ $$artifact == *.scr.vmem ]]; then \
							cp -f "$$(echo $${artifact} | cut -d. -f 1).elf" \
								$${run_dir}/$$(basename "$${artifact%.*.scr.vmem}.elf"); \
						fi; \
					done; \
				fi; \
			done; \
		fi; \
	done;
endif

simulate: sw_build
	@echo "[make]: simulate"
	cd ${run_dir} && ${run_cmd} ${run_opts}

post_run: simulate
	@echo "[make]: post_run"
ifneq (${post_run_cmds},)
	cd ${run_dir} && ${post_run_cmds}
endif

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
cov_unr_build: gen_sv_flist
	@echo "[make]: cov_unr_build"
	cd ${sv_flist_gen_dir} && ${cov_unr_build_cmd} ${cov_unr_build_opts}

cov_unr_vcs: cov_unr_build
	@echo "[make]: cov_unr"
	cd ${sv_flist_gen_dir} && ${cov_unr_run_cmd} ${cov_unr_run_opts}

cov_unr_xcelium:
	@echo "[make]: cov_unr"
	mkdir -p ${cov_unr_dir}
	cd ${cov_unr_dir} && ${cov_unr_run_cmd} ${cov_unr_run_opts}

cov_unr_merge:
	cd ${cov_unr_dir} && ${job_prefix} ${cov_merge_cmd} -init ${cov_unr_dir}/jgproject/sessionLogs/session_0/unr_imc_coverage_merge.cmd

ifeq (${SIMULATOR}, xcelium)
  cov_unr: cov_unr_xcelium cov_unr_merge
else
  cov_unr: cov_unr_vcs
endif

# Merge coverage if there are multiple builds.
cov_merge:
	@echo "[make]: cov_merge"
	${job_prefix} ${cov_merge_cmd} ${cov_merge_opts}

# Generate coverage reports.
cov_report:
	@echo "[make]: cov_report"
	${cov_report_cmd} ${cov_report_opts}

# Open coverage tool to review and create report or exclusion file.
cov_analyze:
	@echo "[make]: cov_analyze"
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
