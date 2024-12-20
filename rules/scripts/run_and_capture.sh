#!/usr/bin/env bash
#
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#

# Run the program and redirect the stdout and stderr to given files
"$@" >"$RUN_CAPTURE_STDOUT" 2>"$RUN_CAPTURE_STDERR"
res=$?
if [ $res -ne 0 ]; then
    cat "$RUN_CAPTURE_STDERR" >&2
    echo "see stdout in $RUN_CAPTURE_STDOUT" >&2
    echo "see stderr in $RUN_CAPTURE_STDERR" >&2
fi
exit $res
