# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

.PHONY: all
all: lint

# We need a directory to build stuff and use the "otbn/otbnsim" namespace
# in the top-level build-bin directory.
repo-top := ../../../..
build-dir := $(repo-top)/build-bin/otbn/otbnsim

$(build-dir):
	mkdir -p $@

pycode := $(wildcard *.py)

$(build-dir)/lint.stamp: $(pycode) | $(build-dir)
	mypy --strict $(pycode)
	touch $@

.PHONY: lint
lint: $(build-dir)/lint.stamp
