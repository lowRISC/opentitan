# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

SW_NAME       ?= boot_rom
SW_SRCS       += $(SW_DIR)/bootstrap.c $(SW_DIR)/boot_rom.c $(LIB_DIR)/hw_sha256.c
INCS          += -I$(SW_ROOT_DIR)/vendor

# overrides
CRT_SRCS      := $(SW_DIR)/crt0.S
LINKER_SCRIPT := $(SW_DIR)/rom_link.ld
