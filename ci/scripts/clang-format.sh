#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# A wrapper around clang-format, used for CI.
#
# Expects a single argument, which is the pull request's target branch
# (usually "master").

set -e

if [ $# != 1 ]; then
    echo >&2 "Usage: clang-format.sh <tgt-branch>"
    exit 1
fi
tgt_branch="$1"

merge_base="$(git merge-base origin/$tgt_branch HEAD)" || {
    echo >&2 "Failed to find fork point for origin/$tgt_branch."
    exit 1
}
echo "Running C/C++ lint checks on files changed since $merge_base"

trap 'echo "code failed clang_format_check fix with ./bazelisk.sh run //quality:clang_format_fix"' ERR

set -o pipefail
(for F in $(git diff --name-only "$merge_base" -- "*.cpp" "*.cc" "*.c" "*.h" ':!*/vendor/*'); do
    echo "--test_arg=\"$F\""
done) | \
    xargs -r ./bazelisk.sh test //quality:clang_format_check --test_output=streamed
