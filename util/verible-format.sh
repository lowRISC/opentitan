#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# this script runs the verible formatter on all system verilog
# files under hw/{ip,vendor,top_earlgrey}
#
# make sure to invoke this tool from the project root.
#
# NOTE: this operates in-place - so make sure to make a backup or
# run this on an experimental branch
#
# TODO: integrate this with Fusesoc and the other linting flows.

NUM_PROCS=8
REPORT_FILE="verible-style-format.rpt"

# this is a precaution in order to prevent accidental
# overwriting of uncomitted changes
git add -u

# get all system verilog files and pipe through style formatter
find hw/{ip,vendor,top_earlgrey} -type f -name "*.sv" -o -name "*.svh" | \
    xargs -n 1 -P $NUM_PROCS /tools/verible/verilog_format               \
    --inplace

# report changed files
git status                  | \
    grep modified           | \
    grep dv                 | \
    awk -F ' ' '{print $2}' | \
    tee $REPORT_FILE
