# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

EXT_COMMON_DIR        ?= $(SW_ROOT_DIR)/device/exts/common
INCS                  += -I$(EXT_COMMON_DIR)

EXT_COMMON_LOC_SRCS   +=

EXT_SRCS              += $(addprefix $(EXT_COMMON_DIR)/, $(EXT_COMMON_LOC_SRCS))
