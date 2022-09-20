#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# A wrapper around fix_whitespace.py, used for CI.
#
# Expects a single argument, which is the pull request's target branch
# (usually "master").

set -e

if [ $# != 1 ]; then
    echo >&2 "Usage: whitespace.sh <tgt-branch>"
    exit 1
fi
tgt_branch="$1"

merge_base="$(git merge-base origin/$tgt_branch HEAD)" || {
    echo >&2 "Failed to find fork point for origin/$tgt_branch."
    exit 1
}
echo "Checking whitespace on files changed since $merge_base"

set -o pipefail
git diff --name-only --diff-filter=ACMRTUXB "$merge_base" -- \
        ':!third_party/rust/crates/*' \
        ':!*/vendor/*' | \
    xargs -r util/fix_trailing_whitespace.py --dry-run || {
    echo -n "##vso[task.logissue type=error]"
    echo "Whitespace check failed. Please run util/fix_trailing_whitespace.py on the above files."
    exit 1
}
