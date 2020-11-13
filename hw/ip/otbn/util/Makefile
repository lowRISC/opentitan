# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

.PHONY: all
all: lint asm-check

# We need a directory to build stuff and use the "otbn/util" namespace
# in the top-level build-bin directory.
repo-top := ../../../..
build-dir := $(repo-top)/build-bin/otbn/util
cs-build-dir := $(build-dir)/code-snippets
lint-build-dir := $(build-dir)/lint

$(build-dir) $(lint-build-dir):
	mkdir -p $@

pylibs := $(wildcard shared/*.py)
pyscripts := yaml_to_doc.py otbn-as otbn-ld otbn-objdump otbn-rig

lint-stamps := $(foreach s,$(pyscripts),$(lint-build-dir)/$(s).stamp)
$(lint-build-dir)/%.stamp: % $(pylibs) | $(lint-build-dir)
	mypy --strict $< $(pylibs)
	touch $@

# For otbn-rig's stamp file, add extra dependencies on the Python code
# in ./rig.
$(lint-build-dir)/otbn-rig.stamp: $(wildcard rig/*.py rig/gens/*.py)

.PHONY: lint
lint: $(lint-stamps)

$(lint-targets): lint-%:
	mypy --strict $* $(pylibs)

# Target that assembles and links each of the code snippets to make
# sure the toolchain is in a reasonable shape.

otbn-code-snippets-obj-dir := $(cs-build-dir)
otbn-code-snippets-bin-dir := $(cs-build-dir)
otbn-code-snippets-util-dir  := .

include $(repo-top)/sw/otbn/code-snippets/rules.mk

.PHONY: asm-check
asm-check: $(otbn-code-snippets-elfs)

.PHONY: clean
clean:
	rm -rf $(build-dir)
