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

py-scripts := otbnsim.py standalone.py
py-files   := $(wildcard *.py otbnsim/*.py)
py-libs    := $(filter-out $(py-scripts),$(py-files))

lint-stamps := $(foreach scr,$(py-scripts),$(build-dir)/$(scr).stamp)

$(lint-stamps): $(build-dir)/%.stamp: % $(py-libs)
	env MYPYPATH="$$MYPYPATH:../../util" mypy --strict $< $(py-libs)
	touch $@

.PHONY: lint
lint: $(lint-stamps)
