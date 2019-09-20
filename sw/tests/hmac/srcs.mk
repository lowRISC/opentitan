# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

SW_NAME       ?= sha256_test
INCS          += -I$(SW_ROOT_DIR)/vendor

# list srcs for each test
ifeq ($(SW_NAME), sha256_test)
  SW_SRCS     += $(SW_DIR)/sha256_test.c
  SW_SRCS     += $(LIB_DIR)/hw_sha256.c
endif
