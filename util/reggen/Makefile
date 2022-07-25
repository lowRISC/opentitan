# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

.PHONY: all
all: lint

# We need a directory to build stuff and use the "util/reggen" namespace
# in the top-level build-bin directory.
repo-top := ../..
build-dir := $(repo-top)/build-bin/util/reggen

$(build-dir):
	mkdir -p $@

# Reggen code that doesn't yet have typing annotations
mypy-excls := gen_json.py gen_selfdoc.py

py-files := $(filter-out $(mypy-excls),$(wildcard *.py))

$(build-dir)/mypy.stamp: $(py-files) | $(build-dir)
	mypy --strict --config $(repo-top)/mypy.ini $^
	touch $@

.PHONY: lint
lint: $(build-dir)/mypy.stamp
