# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

pylibs := insn_yaml.py
pyscripts := yaml_to_doc.py otbn-as otbn-ld

.PHONY: all
all: lint

lint-targets := $(addprefix lint-,$(pyscripts))
.PHONY: lint $(lint-targets)
lint: $(lint-targets)

$(lint-targets): lint-%:
	mypy --strict $*
