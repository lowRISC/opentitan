# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

COREMARK_DIR     = $(SW_ROOT_DIR)/vendor/$(SW_NAME)
COREMARK_PORT    = $(SW_ROOT_DIR)/$(SW_DIR)/top_earlgrey
STANDALONE_SW   := 1
STANDALONE_CMD   = $(MAKE) $(IMG_OUTPUTS) -C $(COREMARK_DIR) \
                     PORT_DIR=$(COREMARK_PORT) \
                     SW_DIR=$(SW_DIR) \
                     SW_ROOT_DIR=$(SW_ROOT_DIR) \
                     SW_BUILD_DIR=$(SW_BUILD_DIR) \
                     MAKEFLAGS=$(MAKEFLAGS)
