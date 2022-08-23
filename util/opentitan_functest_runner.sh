#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# A shell script for executing rust-based tests for functional and e2e tests,
# especially for harnesses built atop opentitanlib.
#
# There are three components that make up the harness invocation:
#   - test harness
#   - arguments
#   - test commands
#
# The test harness is invoked with arguments first, then the test commands.
# The test harness and test commands are both passed in by environment variables.
# Note that bazel passes user-specified test_arg arguments as arguments to this
# script, and because the user-specified test_arg arguments come after the bazel
# rule's arguments, they can override the ones coming from the bazel rule.
# Thus, the test harness and test script represent portions of the invocation
# that cannot be overridden, but the arguments in the middle can.

set -e

if [ -z "$TEST_HARNESS" ]; then
    echo "TEST_HARNESS variable needs to be specified."
    exit 1
fi

# eval the environment variable string to break up the components and have bash
# interpret quotes and other special characters in arguments. This happens
# during the invocation line.
eval "TEST_CMDS_ARRAY=( ${TEST_CMDS} )"

echo Invoking test: "${TEST_HARNESS}" "$@" "${TEST_CMDS_ARRAY[@]}"
RUST_BACKTRACE=1 ${TEST_HARNESS} "$@" "${TEST_CMDS_ARRAY[@]}"
