#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Set various Azure Pipelines variables to figure out what the build
# type should be. These are used to control what downstream CI tasks
# get run.

set -e

if [ $# != 2 ]; then
    echo >&2 "Usage: get-build-type.sh <tgt-branch> <build-reason>"
    exit 1
fi
tgt_branch="$1"
build_reason="$2"

only_doc_changes=0
only_dv_changes=0
has_otbn_changes=1
if [[ "$build_reason" = "PullRequest" ]]; then
    # Conservative way of checking for documentation-only and OTBN changes.
    # Only relevant for pipelines triggered from pull requests
    merge_base="$(git merge-base HEAD origin/$tgt_branch)" || {
        echo >&2 "Failed to find fork point for origin/$tgt_branch."
        exit 1
    }
    echo "Considering changes since $merge_base"

    echo "Checking for changes in this PR other than to .md files"
    # If git diff fails, this means that there were some changes to
    # files other than documentation. Otherwise, there are not.
    git diff --quiet "$merge_base" -- ':!*.md' && only_doc_changes=1 || true
    if [[ $only_doc_changes -eq 1 ]]; then
        echo "PR is only doc changes"
    else
        echo "PR contains non doc changes"
    fi

    echo "Checking for non-DV changes in this PR"
    git diff --quiet "$merge_base" -- ':!*/dv/*' && only_dv_changes=1 || true
    if [[ $only_dv_changes -eq 1 ]]; then
        echo "PR is only DV changes"
    else
        echo "PR contains non-DV changes"
    fi

    # Check if any changes were made to OTBN-related files (hardware,
    # software or tooling). This command is "the other way around"
    # from the docs and DV commands above. It fails if there are any
    # OTBN changes and succeeds otherwise.
    echo "Checking if any OTBN changes are in this pull request"
    git diff --quiet "$merge_base" -- '*/otbn/*' && has_otbn_changes=0
    if [[ $has_otbn_changes -eq 1 ]]; then
        echo "PR contains OTBN changes"
    else
        echo "PR doesn't contain OTBN changes"
    fi
fi
echo "##vso[task.setvariable variable=onlyDocChanges;isOutput=true]${only_doc_changes}"
echo "##vso[task.setvariable variable=onlyDvChanges;isOutput=true]${only_dv_changes}"
echo "##vso[task.setvariable variable=hasOTBNChanges;isOutput=true]${has_otbn_changes}"
