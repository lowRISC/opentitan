#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# A wrapper around Verible lint, used for CI.
#
# Expects two arguments:
# 1. The lint flavour (rtl, dv, fpv)
# 2. The top name (earlgrey, darjeeling, englishbreakfast)

set -e

if [ $# != 2 ]; then
    echo >&2 "Usage: verible-lint.sh <flavour> <top>"
    echo >&2 "  flavour: rtl, dv, or fpv"
    echo >&2 "  top: earlgrey, darjeeling, or englishbreakfast"
    exit 1
fi
flavour="$1"
top="$2"

case "$flavour" in
    rtl)
        human_desc=design
        dvsim_cfg="hw/top_${top}/lint/top_${top}_lint_cfgs.hjson"
        ;;

    dv)
        human_desc=DV
        dvsim_cfg="hw/top_${top}/lint/top_${top}_dv_lint_cfgs.hjson"
        ;;
    fpv)
        human_desc=FPV
        dvsim_cfg="hw/top_${top}/lint/top_${top}_fpv_lint_cfgs.hjson"
        ;;

    *)
        echo >&2 "Unknown lint flavour: $flavour"
        echo >&2 "Supported flavours: rtl, dv, fpv"
        exit 1
esac

# Check if the lint configuration file exists
if [ ! -f "$dvsim_cfg" ]; then
    echo >&2 "Lint configuration file not found: $dvsim_cfg"
    echo >&2 "Make sure the top '$top' supports '$flavour' linting"
    exit 1
fi

# DVSIM_MAX_PARALLEL constrains how many tasks dvsim.py will try to
# run in parallel. If it hasn't already been set, set it to be the
# number of CPUs on the machine.
if [ -n "$DVSIM_MAX_PARALLEL" ]; then
    mp=$DVSIM_MAX_PARALLEL
else
    mp=$(nproc)
fi

env DVSIM_MAX_PARALLEL="$mp" \
  util/dvsim/dvsim.py --tool=veriblelint "$dvsim_cfg" || {
    echo "::error::"\
        "Verilog style lint of ${human_desc} sources with Verible failed for top '${top}'." \
        "Run 'util/dvsim/dvsim.py -t veriblelint ${dvsim_cfg}' and fix all errors."
    exit 1
}
