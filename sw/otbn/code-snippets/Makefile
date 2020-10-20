# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

#####################################################################
#
# THIS IS A TEMPORARY SOLUTION
#
# Eventually, the software team is going to have a Meson-based flow
# for building OTBN software. When that exists, this code will go
# away.
#
#####################################################################

# A Makefile for assembling and linking the code snippets. By default,
# the rules generate outputs in build-bin/sw/otbn/build-subdir.
#
# This is a thin wrapper around ./rules.mk. To customise exactly what
# gets built where, include rules.mk in your own Makefile (see
# documentation there) and set the otbn-code-snippets-* variables
# appropriately.
#

.PHONY: all
all: build

repo-top  := ../../..

obj-dir := $(firstword $(OBJ_DIR) $(repo-top)/build-out)
bin-dir := $(firstword $(BIN_DIR) $(repo-top)/build-bin)
build-subdir := sw/otbn/code-snippets

otbn-code-snippets-obj-dir := $(obj-dir)/$(build-subdir)
otbn-code-snippets-bin-dir := $(bin-dir)/$(build-subdir)
otbn-code-snippets-util-dir  := $(repo-top)/hw/ip/otbn/util

code-snippets-path := $(dir $(realpath $(lastword $(MAKEFILE_LIST))))
include $(code-snippets-path)rules.mk

.PHONY: build
build: $(otbn-code-snippets-elfs)
