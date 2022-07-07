#!/usr/bin/env bash
#
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

if [[ $# == 0 ]]; then
    ARGS=("//...")
else
    ARGS=("$@")
fi

if ! cd "$BUILD_WORKSPACE_DIRECTORY"; then
    echo "Unable to change to workspace (BUILD_WORKSPACE_DIRECTORY: ${BUILD_WORKSPACE_DIRECTORY})"
    exit 1
fi

bazel coverage "${ARGS[@]}"
genhtml -o bazel-out/_coverage/ bazel-out/_coverage/_coverage_report.dat
echo "Coverage report: file://$(pwd)/bazel-out/_coverage/index.html"
