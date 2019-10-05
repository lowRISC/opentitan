# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

UTIL_DIR            ?= $(SW_ROOT_DIR)/util
MSG_FLOW_DIR        ?= $(UTIL_DIR)/msg_$(MSG_FLOW)
INCS                += -I$(UTIL_DIR) -I$(MSG_FLOW_DIR)

LIB_UTIL_LOC_SRCS   += msg_print.c

LIB_SRCS            += $(addprefix $(UTIL_DIR)/, $(LIB_UTIL_LOC_SRCS))
