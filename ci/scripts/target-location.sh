#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Use Bazel to query for the location of targets instead of searching

set -e
REPO=$(dirname "$0")/../..

$REPO/bazelisk.sh cquery $1 --output starlark --starlark:file=$REPO/rules/output.cquery 2>/dev/null
