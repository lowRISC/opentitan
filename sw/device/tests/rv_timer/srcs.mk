# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

SW_NAME       ?= rv_timer_test

# list srcs for each test
ifeq ($(SW_NAME), rv_timer_test)
  SW_SRCS     += $(SW_DIR)/rv_timer_test.c
endif
