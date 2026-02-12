#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Checks the coutermeasures for a given top from its hjson file.

set -e

if [ $# != 1 ]; then
    echo >&2 "Usage: check-countermeasures.sh <toplevel-name>"
    exit 1
fi
hjson_file="hw/top_$1/data/top_$1.hjson"
if [ ! -f ${hjson_file} ]; then
    echo >&2 "Missing hjson file for $1: expected file ${hjson_file} not found."
    echo >&2 "  For example, use \"earlgrey\" for top_earlgrey.hjson."
    exit 1
fi
hjson_seed_file="hw/top_$1/data/top_$1_seed.testing.hjson"
if [ ! -f ${hjson_seed_file} ]; then
    echo >&2 "Missing hjson file for $1: expected file ${hjson_seed_file} not found."
    echo >&2 "  For example, use \"earlgrey\" for top_earlgrey_seed.testing.hjson."
    exit 1
fi

./util/topgen.py -t ${hjson_file} -s ${hjson_seed_file} --check-cm || {
    echo "::error::Countermeasure check failed."
    exit 1
}
