#!/usr/bin/env bash
#
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

FILES=(@@FILES@@)

if ! cd "$BUILD_WORKSPACE_DIRECTORY"; then
    echo "Unable to change to workspace (BUILD_WORKSPACE_DIRECTORY: ${BUILD_WORKSPACE_DIRECTORY})"
    exit 1
fi

for F in "${FILES[@]}"; do
    bazel run @@CARGO_RAZE@@ -- --manifest-path="$BUILD_WORKSPACE_DIRECTORY/$F" "$@"
done
