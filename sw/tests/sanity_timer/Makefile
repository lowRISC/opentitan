# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Generate a baremetal application for the microcontroller

NAME         = sanity_timer
SRCS         = sanity_timer.c
PROGRAM_DIR := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))

include ${PROGRAM_DIR}/../../exts/common/options.mk
include ${PROGRAM_DIR}/../../exts/common/common.mk
