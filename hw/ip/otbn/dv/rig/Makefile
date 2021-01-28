# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

.PHONY: all
all: lint

# We need a directory to build stuff and use the "otbn/rig" namespace
# in the top-level build-bin directory.
repo-top := ../../../..
build-dir := $(repo-top)/build-bin/otbn/rig
cs-build-dir := $(build-dir)/code-snippets
lint-build-dir := $(build-dir)/lint

$(build-dir) $(lint-build-dir):
	mkdir -p $@

pylibs := $(wildcard ../../util/shared/*.py rig/*.py rig/gens/*.py)
pyscripts := otbn-rig

lint-stamps := $(foreach s,$(pyscripts),$(lint-build-dir)/$(s).stamp)
$(lint-build-dir)/%.stamp: % $(pylibs) | $(lint-build-dir)
	env MYPYPATH=../../util:$$MYPYPATH \
	  mypy --strict $<
	touch $@

.PHONY: lint
lint: $(lint-stamps)
