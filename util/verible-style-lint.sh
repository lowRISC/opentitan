#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# this script runs the verible style linte on all system verilog
# files under hw/{ip,vendor,top_earlgrey}
#
# TODO: integrate this with Fusesoc and the other linting flows.

NUM_PROCS=8
REPORT_FILE="verible-style-lint.rpt"
EXCLUDED_RULES="-macro-name-style"

# get all system verilog files and pipe through style linter
find hw/{ip,vendor,top_earlgrey} -type f -name "*.sv" -o -name "*.svh" |  \
    xargs -n 1 -P $NUM_PROCS /tools/verible/verilog_lint                  \
    --rules=$EXCLUDED_RULES                                               \
    | tee $REPORT_FILE
