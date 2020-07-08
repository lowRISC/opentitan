# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

pyfiles := insn_yaml.py yaml_to_doc.py

.PHONY: lint
lint: $(pyfiles)
	mypy --strict $(pyfiles)
