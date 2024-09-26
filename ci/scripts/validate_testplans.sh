#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Use a JSON schema to validate the testplan hjson files have the correct structure.

set -e

dirs_with_testplan_files=(
    "hw/top_earlgrey/data"
    "hw/top_earlgrey/data/ip"
)
testplan_schema="hw/lint/sival_testplan_schema.hjson"

for dir in "${dirs_with_testplan_files[@]}"; do
    echo "Validating testplans under $dir:"
    util/validate_testplans.py --dir "$dir" --schema "$testplan_schema" || {
        echo -n "##vso[task.logissue type=error]"
        echo "Failed testplan validation in ${dir}."
        echo "::error::Failed testplan validation in ${dir}."
        exit 1
    }
done

exit 0
