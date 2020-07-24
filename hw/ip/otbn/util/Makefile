# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

pylibs := insn_yaml.py mem_layout.py
pyscripts := yaml_to_doc.py otbn-as otbn-ld otbn-objdump

.PHONY: all
all: lint asm-sanity

lint-targets := $(addprefix lint-,$(pyscripts))
.PHONY: lint $(lint-targets)
lint: $(lint-targets)

$(lint-targets): lint-%:
	mypy --strict $* $(pylibs)


asm-snippets := $(notdir $(wildcard ../code-snippets/*.S))

asm-sanity-targets := $(addprefix asm-check-,$(asm-snippets))

$(asm-sanity-targets): asm-check-%: ../code-snippets/%
	./otbn-as $< -o /dev/null

.PHONY: asm-sanity $(asm-sanity-targets)
asm-sanity: $(asm-sanity-targets)
