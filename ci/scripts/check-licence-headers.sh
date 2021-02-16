#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# A wrapper around licence-checker.py, used for CI.
#
# Expects a single argument, which is the pull request's target branch
# (usually "master").

set -e

if [ $# != 1 ]; then
    echo >&2 "Usage: check-licence-headers.sh <tgt-branch>"
    exit 1
fi
tgt_branch="$1"

merge_base="$(git merge-base origin/$tgt_branch HEAD)" || {
    echo >&2 "Failed to find fork point for origin/$tgt_branch."
    exit 1
}
echo "Checking licence headers on files changed since $merge_base"

lc_script=util/lowrisc_misc-linters/licence-checker/licence-checker.py
lc_cmd="$lc_script --config util/licence-checker.hjson"

# Ask git for a list of null-separated names of changed files and pipe
# those through to the licence checker using xargs. Setting pipefail
# ensures that we'll see an error if the git diff command fails for
# some reason.
set -o pipefail
git diff -z --name-only --diff-filter=ACMRTUXB "$merge_base" | \
    xargs -r -0 $lc_cmd || {

    echo >&2 -n "##vso[task.logissue type=error]"
    echo >&2 "Licence header check failed."
    exit 1
}
