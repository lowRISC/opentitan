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
echo "Checking if Rust files have changed since $merge_base"

trap 'echo "code failed rustfmt_check fix with ./bazelisk.sh run //quality:rustfmt_fix"' ERR

set -o pipefail
if ! git diff --quiet $merge_base -- "*.rs" ':!*/vendor/*'; then
    echo "Rust files changed, running Rust lint checks"
    ./bazelisk.sh test //quality:rustfmt_check --test_output=streamed
else
    echo "Rust files unchanged, skipping Rust lint checks"
fi
