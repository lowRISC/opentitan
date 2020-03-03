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
#
# This file also provides $OT_VERSION, which can be embedded in artifacts as a
# timestamp. If a git repo is present, it will be computed from that, or else
# will be an arbitrary string.

# Since this file is intended to be sourced, we can't use |$0| to get our
# bearings. However, the bash-specific $BASH_SOURCE works perfectly fine.
if [[ -n "$BASH_SOURCE" ]]; then
  readonly REPO_TOP="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
else
  echo "Non-bash shells are currently not supported." >&2
  exit 1
fi

OT_GIT_VERSION="$(git describe --always 2>/dev/null)"
if [[ -n "$OT_GIT_VERSION" ]]; then
  readonly OT_VERSION="opentitan-$OT_GIT_VERSION"
else
  readonly OT_VERSION="opentitan-<unknown>"
fi

BUILD_ROOT="${BUILD_ROOT:-"$REPO_TOP"}"
readonly OBJ_DIR="$BUILD_ROOT/build-out"
readonly BIN_DIR="$BUILD_ROOT/build-bin"

# $DEV_BIN_DIR is a subdirectory of $BIN_DIR where device build outputs (i.e.,
# compiled programs that should run on the OpenTitan SoC) should be written.
DEV_BIN_DIR="$BIN_DIR/sw/device"

# $HOST_BIN_DIR is a subdirectory of $BIN_DIR where host build outputs (i.e.,
# compiled programs that should run on a host workstation or server) should be
# written.
HOST_BIN_DIR="$BIN_DIR/sw/host"

# $TOCK_SYMLINK is the symlink used when referencing a local checkout of tock to
# build from.
TOCK_SYMLINK="$REPO_TOP/sw/device/tock/tock_local"
