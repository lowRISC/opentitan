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
  export REPO_TOP
else
  echo "Non-bash shells are currently not supported." >&2
  exit 1
fi

export OT_GIT_VERSION="$(git describe --always 2>/dev/null)"
if [[ -n "$OT_GIT_VERSION" ]]; then
  readonly OT_VERSION="opentitan-$OT_GIT_VERSION"
else
  readonly OT_VERSION="opentitan-<unknown>"
fi
export OT_VERSION

export BUILD_ROOT="${BUILD_ROOT:-"$REPO_TOP"}"
readonly OBJ_DIR="$BUILD_ROOT/build-out"
export OBJ_DIR
readonly BIN_DIR="$BUILD_ROOT/build-bin"
export BIN_DIR

# $TOCK_SYMLINK is the symlink used when referencing a local checkout of tock to
# build from.
export TOCK_SYMLINK="$REPO_TOP/sw/device/tock/tock_local"
