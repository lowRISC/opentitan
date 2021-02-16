#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Check vendored repositories are up to date

set -e

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

git diff --exit-code || {
    echo >&2 -n "##vso[task.logissue type=error]"
    echo >&2 "Vendored repositories not up-to-date. Run util/vendor.py to fix."
    exit 1
}
