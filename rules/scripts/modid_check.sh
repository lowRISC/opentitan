#!/usr/bin/env bash
#
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
set -e

# Arguments:
# - path to opentitantool
# - output file to create
# - (one or more) elf files to check
if [ $# -lt 3 ]; then
    echo "This script needs at least 3 arguments"
    exit 42
fi
ott="$1"
out_file="$2"
# forget first two arguments so we can access elf files
shift 2

# run tool, capture output to avoid polutting the CI log
if ! "$ott" status lint "$@" >"$out_file" 2>&1; then
    if ! cat "$out_file"; then
        echo "Unable to print the output log, something is very wrong"
        exit 43
    fi
    exit 1
fi
