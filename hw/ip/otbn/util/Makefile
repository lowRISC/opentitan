# Copyright lowRISC contributors (OpenTitan project).
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

pylibs := $(wildcard shared/*.py docs/*.py)
pyscripts := yaml_to_doc.py otbn_as.py otbn_ld.py otbn_objdump.py docs/md_isrs.py

lint-stamps := $(foreach s,$(pyscripts),$(lint-build-dir)/$(s).stamp)
$(lint-build-dir)/%.stamp: % $(pylibs) | $(lint-build-dir)
	mypy --strict --config-file=mypy.ini $<
	mkdir -p $(@D)
	touch $@

.PHONY: lint
lint: $(lint-stamps)
