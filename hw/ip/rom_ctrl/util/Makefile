# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

.PHONY: all
all: lint

# We need a directory to build stuff and use the "rom_ctrl/util" namespace
# in the top-level build-out directory.
repo-top := ../../../..
build-dir := $(repo-top)/build-out/otbn/util
lint-build-dir := $(build-dir)/lint

$(build-dir) $(lint-build-dir):
	mkdir -p $@

pyscripts := scramble_image.py
pylibs := $(filter-out $(pyscripts),$(wildcard *.py))

lint-stamps := $(foreach s,$(pyscripts),$(lint-build-dir)/$(s).stamp)
$(lint-build-dir)/%.stamp: % $(pylibs) | $(lint-build-dir)
	PYTHONPATH=$(repo-top) mypy --strict $< $(pylibs)
	touch $@

.PHONY: lint
lint: $(lint-stamps)

.PHONY: clean
clean:
	rm -rf $(build-dir)
