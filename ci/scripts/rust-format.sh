#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# A wrapper around rustfmt, used for CI.
#
# Expects a single argument, which is the pull request's target branch
# (usually "master").

set -e

if [ $# != 1 ]; then
    echo >&2 "Usage: rust-format.sh <tgt-branch>"
    exit 1
fi
tgt_branch="$1"

merge_base="$(git merge-base origin/$tgt_branch HEAD)" || {
    echo >&2 "Failed to find fork point for origin/$tgt_branch."
    exit 1
}
echo "Running Rust lint checks on files changed since $merge_base"

set -o pipefail
git diff -z --name-only --diff-filter=ACMRTUXB "$merge_base" -- "*.rs" ':!*/vendor/*' | \
    xargs -0 -r rustfmt --check || {
    echo -n "##vso[task.logissue type=error]"
    echo "Rust lint failed."
    exit 1
}
