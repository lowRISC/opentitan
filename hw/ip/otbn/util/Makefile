# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

.PHONY: all
all: lint asm-sanity

# We need a directory to build stuff and use the "otbn/util" namespace
# in the top-level build-bin directory.
repo-top := ../../../..
build-dir := $(repo-top)/build-bin/otbn/util
cs-build-dir := $(build-dir)/code-snippets
lint-build-dir := $(build-dir)/lint

$(build-dir) $(cs-build-dir) $(lint-build-dir):
	mkdir -p $@

pylibs := $(wildcard shared/*.py)
pyscripts := yaml_to_doc.py otbn-as otbn-ld otbn-objdump otbn-rig

lint-stamps := $(foreach s,$(pyscripts),$(lint-build-dir)/$(s).stamp)
$(lint-build-dir)/%.stamp: % $(pylibs) | $(lint-build-dir)
	mypy --strict $< $(pylibs)
	touch $@

# For otbn-rig's stamp file, add extra dependencies on the Python code
# in ./rig.
$(lint-build-dir)/otbn-rig.stamp: $(wildcard rig/*.py)

.PHONY: lint
lint: $(lint-stamps)

$(lint-targets): lint-%:
	mypy --strict $* $(pylibs)

# Sanity check target that assembles and (trivially) links each of
# the code snippets.
asm-snippets := $(notdir $(wildcard $(repo-top)/sw/otbn/code-snippets/*.S))

asm-objects := $(addprefix $(cs-build-dir)/,$(asm-snippets:%.S=%.o))
linked-elfs := $(addprefix $(cs-build-dir)/,$(asm-snippets:%.S=%))

# Firstly, assemble them
$(asm-objects): $(cs-build-dir)/%.o: \
  $(repo-top)/sw/otbn/code-snippets/%.S otbn-as $(pylibs) | $(cs-build-dir)
	./otbn-as -o $@ $<

# Then link them
$(linked-elfs): $(cs-build-dir)/%: \
  $(cs-build-dir)/%.o otbn-ld $(pylibs)
	./otbn-ld -o $@ $<

.PHONY: asm-sanity
asm-sanity: $(linked-elfs)

.PHONY: clean
clean:
	rm -rf $(build-dir)
