#!/usr/bin/env bash
#
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
set -e

# Run the program and redirect the stdout and stderr to given files
if ! "$@" >$RUN_CAPTURE_STDOUT 2>$RUN_CAPTURE_STDERR; then
    echo "$1 failed" >&2
    echo "see stdout in $RUN_CAPTURE_STDOUT" >&2
    echo "see stderr in $RUN_CAPTURE_STDERR" >&2
fi
