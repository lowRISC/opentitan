#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# A wrapper around fix_include_guard.py, used for CI.
#
# Expects a single argument, which is the pull request's target branch
# (usually "master").

set -e

if [ $# != 1 ]; then
    echo >&2 "Usage: include-guard.sh <tgt-branch>"
    exit 1
fi
tgt_branch="$1"

merge_base="$(git merge-base origin/$tgt_branch HEAD)" || {
    echo >&2 "Failed to find fork point for origin/$tgt_branch."
    exit 1
}
echo "Checking header guards on headers changed since $merge_base"

set -o pipefail
git diff --name-only --diff-filter=ACMRTUXB "$merge_base" -- \
  "*.h" ':!*/vendor/*' | \
    xargs -r util/fix_include_guard.py --dry-run || {
    echo -n "##vso[task.logissue type=error]"
    echo "Include guard check failed. Please run util/fix_include_guard.py on the above files."
    exit 1
}
