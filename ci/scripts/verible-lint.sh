#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# A wrapper around Verible lint, used for CI.
#
# Expects a single argument, which is the pull request's target branch
# (usually "master").

set -e

if [ $# != 1 ]; then
    echo >&2 "Usage: verible-lint.sh <flavour>"
    exit 1
fi
flavour="$1"

case "$flavour" in
    rtl)
        human_desc=design
        dvsim_cfg=hw/top_earlgrey/lint/top_earlgrey_lint_cfgs.hjson
        ;;

    dv)
        human_desc=DV
        dvsim_cfg=hw/top_earlgrey/lint/top_earlgrey_dv_lint_cfgs.hjson
        ;;
    fpv)
        human_desc=FPV
        dvsim_cfg=hw/top_earlgrey/lint/top_earlgrey_fpv_lint_cfgs.hjson
        ;;

    *)
        echo >&2 "Unknown lint flavour: $flavour"
        exit 1
esac

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
    echo -n "##vso[task.logissue type=error]"
    echo "Verilog style lint of $human_desc sources with Verible failed. Run 'util/dvsim/dvsim.py -t veriblelint $dvsim_cfg' and fix all errors."
    exit 1
}
