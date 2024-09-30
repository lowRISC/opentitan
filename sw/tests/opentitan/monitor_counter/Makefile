# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Generate a baremetal application

# Name of the program $(PROGRAM).c will be added as a source file
PROGRAM = monitor_counter
PROGRAM_DIR := $(shell dirname $(realpath $(lastword $(MAKEFILE_LIST))))
# Any extra source files to include in the build. Use the upper case .S
# extension for assembly files

utils_dir = $(PROGRAM_DIR)/inc/
directories = drivers/inc drivers/src string_lib/inc string_lib/src 
EXTRA_SRCS = $(foreach d, $(directories), -I$(utils_dir)$d)

include ${PROGRAM_DIR}/../common/common.mk
