# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

define get-metadata-variable
    env PYTHONPATH=$(PYTHONPATH) python3 ./scripts/metadata.py \
    --op "print_field" \
    --dir-metadata $(METADATA-DIR) \
    --field $(1)
endef
define get-meta
    $(shell $(call get-metadata-variable,$(1)))
endef

# This is how you can get variables from the python metadata easily...
# testvar := $(call get-meta,"ibex_root")
