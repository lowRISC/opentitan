#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# A wrapper around lintpy.py, used for CI.
#
# Expects a single argument, which is the pull request's target branch
# (usually "master").

set -e

if [ $# != 1 ]; then
    echo >&2 "Usage: python-lint.sh <tgt-branch>"
    exit 1
fi
tgt_branch="$1"

merge_base="$(git merge-base origin/$tgt_branch HEAD)" || {
    echo >&2 "Failed to find fork point for origin/$tgt_branch."
    exit 1
}
echo "Linting python code changed since $merge_base"

ignored_subtrees=(
    "*/vendor/"
    util/lowrisc_misc-linters
)

pathspec_args=("*.py")
for st in "${ignored_subtrees[@]}"; do
    # This generates an argument like :!/FOO*, that tells git to
    # ignore every path matching the glob /FOO*. See the description
    # of pathspecs in gitglossary(7) for more information.
    pathspec_args+=(':!/'"$st"'*')
done

lintpy_cmd="util/lintpy.py --tools flake8 -f"

# Ask git for a list of null-separated names of changed files that
# don't appear in an ignored directory. Pipe those through to the
# licence checker using xargs. Setting pipefail ensures that we'll see
# an error if the git diff command fails for some reason.
set -o pipefail
git diff -z --name-only --diff-filter=ACMRTUXB "$merge_base" -- \
  "${pathspec_args[@]}" | \
    xargs -0 -r $lintpy_cmd || {
    echo -n "##vso[task.logissue type=error]"
    echo "Python lint failed."
    exit 1
}
