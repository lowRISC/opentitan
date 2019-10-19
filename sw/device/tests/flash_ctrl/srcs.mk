# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

SW_NAME       ?= flash_test

# list srcs for each test
ifeq ($(SW_NAME), flash_test)
  SW_SRCS     += $(SW_DIR)/flash_test.c
endif
