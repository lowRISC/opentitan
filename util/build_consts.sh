#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This file provides common definitions for build output locations in the
# OpenTitan repository; scripts that wish to use it should |source| it at their
# start.
#
# OpenTitan has two build directories:
# - $OBJ_DIR, which contains all outputs and intermediates of the build
#   process, with an unstable directory structure.
# - $BIN_DIR, which contains "executable" outputs of the build process, such as
#   binaries, tests, and bitstreams. It has a stable directory structure.
#
# $OBJ_DIR and $BIN_DIR are the subdirectories build-out and build-bin of
# $BUILD_ROOT, which can be configured to any desired directory. Build artifacts
# can be cleaned out by running |rm -rf $BUILD_ROOT/build-*|.

# We cannot rely on the location of this file for anything, since it is meant to
# be sourced, not executed. As such, we use git to compute $REPO_TOP.
readonly REPO_TOP="$(git rev-parse --show-toplevel)"
BUILD_ROOT="${BUILD_ROOT:-"$REPO_TOP"}"

readonly OBJ_DIR="$BUILD_ROOT/build-out"
readonly BIN_DIR="$BUILD_ROOT/build-bin"

# PLATFORMS is an array of all of the "device platforms" which OpenTitan
# software can be built for. These include:
# - 'sim-verilator', i.e., Verilator.
# - 'fpga', i.e., a NexysVideo FPGA board.
readonly PLATFORMS=(
  'sim-verilator'
  'fpga'
)

# sw_obj_dir takes a platform name as an argument and produces a path to a
# subdirectory of $OBJ_DIR where its build action artifacts should be written.
#
# The output of this function should be considered scratch space and not stable.
function sw_obj_dir() {
  echo "$OBJ_DIR/sw/$1"
}

# sw_bin_dir takes a platform name as an argument and produces a path to the
# subdirectory of $BIN_DIR where its completed build outputs should be written.
function sw_bin_dir() {
  echo "$BIN_DIR/sw/device/$1"
}

# $HOST_BIN_DIR is a subdirectory of $BIN_DIR where host build outputs (i.e.,
# compiled programs that should run on a host workstation or server) should be
# written.
HOST_BIN_DIR="$BIN_DIR/sw/host"
