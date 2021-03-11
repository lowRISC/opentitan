# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

export SHELL	:= /bin/bash
.DEFAULT_GOAL := all

all: build

###################
## build targets ##
###################
build: build_result

pre_build:
	@echo "[make]: pre_build"
	mkdir -p ${build_dir}
ifneq (${pre_build_cmds},)
	cd ${build_dir} && ${pre_build_cmds}
endif

do_build: pre_build
	@echo "[make]: do_build"
	-cd ${build_dir} && ${build_cmd} ${build_opts} 2>&1 | tee ${build_log}

post_build: do_build
	@echo "[make]: post_build"
ifneq (${post_build_cmds},)
	cd ${build_dir} && ${post_build_cmds}
endif

build_result: post_build
	@echo "[make]: build_result"
	${report_cmd} ${report_opts}

.PHONY: build \
        pre_build \
        do_build \
        post_build \
        build_result
