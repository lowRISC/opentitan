#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Check vendored repositories are up to date

set -e

# Snapshot the set of untracked files before re-vendoring. A plain
# `git diff --exit-code` only detects changes to *tracked* files, so it misses
# vendored output that is not committed -- most notably an obsolete
# *.vendor.hjson whose target directory is no longer part of the repo (e.g. a
# dependency since moved to a Bazel http_archive). Re-vendoring recreates such a
# directory as *untracked*, which would otherwise slip through silently.
untracked_before="$(git status --porcelain --untracked-files=all)"

# Here we look for all *.vendor.hjson files in the repo and re-vendor them.
#
# We exclude the following:
# - Any in 'hw/vendor/lowrisc_ibex', because that directory is vendored.
find . \
     -not \( -path './hw/vendor/lowrisc_ibex' -prune \) \
     -name '*.vendor.hjson' -print0 | \
    xargs -0 -n1 util/vendor.py --verbose || {

    echo >&2 "Failed to run vendor script"
    exit 1
}

untracked_after="$(git status --porcelain --untracked-files=all)"

if ! git diff --exit-code || [ "$untracked_before" != "$untracked_after" ]; then
    echo >&2 "::error::Vendored repositories not up-to-date. Run util/vendor.py to fix,"
    echo >&2 "and delete any obsolete *.vendor.hjson whose target is now sourced elsewhere."
    exit 1
fi
