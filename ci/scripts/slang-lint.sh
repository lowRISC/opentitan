#!/usr/bin/env bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# A wrapper around slang lint and elaboration, used for CI.
#
# Expects one argument:
# 1. The top name (earlgrey, darjeeling, englishbreakfast)
#    englishbreakfast is skipped upstream in cat_slang pending an RTL fix;
#    this script will error if called with a top that has no lint cfg file.

set -e

if [ $# != 1 ]; then
    echo >&2 "Usage: slang-lint.sh <top>"
    echo >&2 "  top: earlgrey, darjeeling, or englishbreakfast"
    exit 1
fi
top="$1"

dvsim_cfg="hw/top_${top}/lint/top_${top}_lint_cfgs.hjson"

# Check if the lint configuration file exists
if [ ! -f "$dvsim_cfg" ]; then
    echo >&2 "Lint configuration file not found: $dvsim_cfg"
    echo >&2 "Make sure the top '$top' supports slang linting"
    exit 1
fi

# DVSIM_MAX_PARALLEL constrains how many tasks dvsim will try to
# run in parallel. If it hasn't already been set, set it to be the
# number of CPUs on the machine.
if [ -n "$DVSIM_MAX_PARALLEL" ]; then
    mp=$DVSIM_MAX_PARALLEL
else
    mp=$(nproc)
fi

env DVSIM_MAX_PARALLEL="$mp" \
  dvsim --tool=slang "$dvsim_cfg" || {
    echo "::error::"\
        "Slang lint of RTL sources failed for top '${top}'." \
        "Run 'dvsim -t slang ${dvsim_cfg}' and fix all errors."
    exit 1
}
