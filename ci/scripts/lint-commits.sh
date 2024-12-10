#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# A wrapper around lint_commits.py, used for CI.
#
# Expects a single argument, which is the pull request's target branch
# (usually "master").

if [ $# != 1 ]; then
    echo >&2 "Usage: lint-commits.sh <tgt-branch>"
    exit 1
fi
tgt_branch="$1"

merge_base="$(git merge-base origin/$tgt_branch HEAD)" || {
    echo >&2 "Failed to find fork point for origin/$tgt_branch."
    exit 1
}
echo "Checking commit messages since $merge_base"

# Notes:
# * Merge commits are not checked. We always use rebases instead of
#   merges to keep a linear history, which makes merge commits disappear
#   ultimately, making them only a CI artifact which should not be
#   checked.
util/lint_commits.py \
  --no-merges \
  --error-msg-prefix="::error::" \
  --warning-msg-prefix="::warning::" \
  "$merge_base"..HEAD
