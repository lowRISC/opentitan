#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# A shell script for executing rust-based tests for functional and e2e tests.
# The test runner should be passed in as the first argument.

set -e

if [ -z "$TEST_HARNESS" ]; then
    echo "TEST_HARNESS variable needs to be specified."
    exit 1
fi

readonly REPO_TOP="$TEST_SRCDIR/$TEST_WORKSPACE"
echo Invoking test: "${TEST_HARNESS}" "$@"
RUST_BACKTRACE=1 ${TEST_HARNESS} "$@"
