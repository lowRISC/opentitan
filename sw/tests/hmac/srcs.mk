# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

SW_NAME       ?= sha256_test

# list srcs for each test
ifeq ($(SW_NAME), sha256_test)
  SW_SRCS     += $(SW_DIR)/sha256_test.c
  SW_SRCS     += $(SW_ROOT_DIR)/lib/hw_sha256.c
endif
