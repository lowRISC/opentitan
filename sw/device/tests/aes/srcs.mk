# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

SW_NAME       ?= aes_test

# list srcs for each test
ifeq ($(SW_NAME), aes_test)
  SW_SRCS     += $(SW_DIR)/aes_test.c
  SW_SRCS     += $(SW_ROOT_DIR)/lib/aes.c
endif
