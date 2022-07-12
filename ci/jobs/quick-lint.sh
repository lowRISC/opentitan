#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# A wrapper that duplicates the code for the quick lint job in
# azure-pipelines.yml. The two should be kept in sync.
#
# This doesn't install dependencies, but should otherwise behave the
# same as what CI would do on a pull request.
#
# These tasks should ideally take less than a minute each

set -e

case $# in
    0)
        tgt_branch=master
        ;;
    1)
        tgt_branch="$1"
        shift
        ;;
    *)
        echo >&2 "Usage: quick-lint.sh [<tgt-branch>]"
        exit 1
esac

echo "### Display environment information"
ci/scripts/show-env.sh

echo -e "\n### Check commit metadata"
ci/scripts/lint-commits.sh $tgt_branch

echo -e "\n### Check Licence Headers"
ci/scripts/check-licence-headers.sh $tgt_branch

echo -e "\n### Check executable bits"
ci/scripts/exec-check.sh

echo -e "\n### Check for non-ASCII characters in source code"
ci/scripts/check-ascii.sh

echo -e "\n### Run Python lint (flake8)"
ci/scripts/python-lint.sh $tgt_branch || {
    echo "(ignoring python lint errors)"
}

echo -e "\n### Run Python lint (mypy)"
ci/scripts/mypy.sh $tgt_branch

echo -e "\n### Use clang-format to check C/C++ coding style"
ci/scripts/clang-format.sh $tgt_branch

echo -e "\n### Check formatting on header guards"
ci/scripts/include-guard.sh $tgt_branch

echo -e "\n### Use rustfmt to check Rust coding style"
ci/scripts/rust-format.sh $tgt_branch

echo -e "\n### Run shellcheck on all shell scripts"
ci/scripts/run-shellcheck.sh

echo -e "\n### Render documentation"
ci/scripts/build-docs.sh

echo -e "\n### Render landing site"
ci/scripts/build-site.sh

echo -e "\n### Check what kinds of changes the PR contains"
ci/scripts/get-build-type.sh $tgt_branch PullRequest
