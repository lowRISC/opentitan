#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Print a special GitHub command to create a group in the log's output:
# https://docs.github.com/en/actions/writing-workflows/choosing-what-your-workflow-does/workflow-commands-for-github-actions#grouping-log-lines
#
# Test variables are documented here:
# https://bazel.build/reference/test-encyclopedia
if [ -z "$TEST_RUN_NUMBER" ]; then
    RUN_NR=""
else
    RUN_NR="(Run $TEST_RUN_NUMBER)"
fi

function cleanup {
    echo "::endgroup::"
}

echo "::group::$TEST_TARGET $RUN_NR"
# NOTE Even if the command fails, we still want to continue to print
# the endgroup command.
trap cleanup SIGINT SIGTERM EXIT
"$@"
