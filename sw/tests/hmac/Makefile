# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Generate a baremetal application for the microcontroller

NAME         = sha256_test
SRCS         = sha256_test.c
PROGRAM_DIR := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))

include ${PROGRAM_DIR}/../../exts/common/options.mk
include ${PROGRAM_DIR}/../../exts/common/common.mk
