# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Generate a baremetal application for the microcontroller

NAME          = boot_rom
SRCS          = bootstrap.c boot_rom.c
LINKER_SCRIPT = rom_link.ld
CRT_SRCS      =
EXT_ASMS      = crt0.S

PROGRAM_DIR := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))
SW_DIR      := $(PROGRAM_DIR)/..

include ${PROGRAM_DIR}/../exts/common/options.mk
include ${PROGRAM_DIR}/../exts/common/common.mk
