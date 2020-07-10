# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
.DEFAULT_GOAL := all

all: build

###################
## build targets ##
###################
build: compile_result

pre_compile:
	@echo "[make]: pre_compile"
	mkdir -p ${build_dir} && env | sort > ${build_dir}/env_vars
	mkdir -p ${tool_srcs_dir}
	-cp -Ru ${tool_srcs} ${tool_srcs_dir}

compile: pre_compile
	@echo "[make]: compile"
	# we check the status in the parse script below
	-cd ${build_dir} && ${build_cmd} ${build_opts} 2>&1 | tee ${build_log}

post_compile: compile
	@echo "[make]: post_compile"

# Parse out result
compile_result: post_compile
	@echo "[make]: compile_result"
	${report_cmd} ${report_opts}

.PHONY: build \
	run \
	pre_compile \
	compile \
	post_compile \
	compile_result
