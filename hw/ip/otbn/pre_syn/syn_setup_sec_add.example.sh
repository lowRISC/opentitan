#!/usr/bin/env bash

# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Setup IP name and top module.
# When changing the top module, some parameters might not exist and
# tcl/yosys_run_synth.tcl might need to be adjusted accordingly.
export LR_SYNTH_IP_NAME=otbn

case "$TARGET_TYPE" in
  hpc2)        export LR_SYNTH_TOP_MODULE=prim_hpc2_sca_wrapper ;;
  hpc2o)       export LR_SYNTH_TOP_MODULE=prim_hpc2o_sca_wrapper ;;
  hpc3)        export LR_SYNTH_TOP_MODULE=prim_hpc3_sca_wrapper ;;
  hpc3o)       export LR_SYNTH_TOP_MODULE=prim_hpc3o_sca_wrapper ;;
  *)           export LR_SYNTH_TOP_MODULE=prim_hpc3o_sca_wrapper ;;
esac

# Setup cell library path.
# Change the line below to set the path to an appropriate .lib file
# export LR_SYNTH_CELL_LIBRARY_PATH=/path/to/NangateOpenCellLibrary_typical.lib
export LR_SYNTH_CELL_LIBRARY_NAME=nangate
if [ -z "$LR_SYNTH_CELL_LIBRARY_PATH" ]; then
    echo >&2 "You forgot to set LR_SYNTH_CELL_LIBRARY_PATH!";
    exit 1;
fi
if [ ! -f "$LR_SYNTH_CELL_LIBRARY_PATH" ]; then
    echo >&2 "Cannot find cell library $LR_SYNTH_CELL_LIBRARY_PATH";
    echo >&2 "Check your LR_SYNTH_CELL_LIBRARY_PATH variable!";
    exit 1;
fi
if [ -z "$LR_SYNTH_CELL_LIBRARY_NAME" ]; then
    echo >&2 "You forgot to set LR_SYNTH_CELL_LIBRARY_NAME!";
    exit 1;
fi

# Control synthesis flow.
export LR_SYNTH_TIMING_RUN=0
export LR_SYNTH_FLATTEN=1

# For timing runs, hierarchy flattening is needed.
if [[ $LR_SYNTH_TIMING_RUN == 1 ]] && [[ $LR_SYNTH_FLATTEN == 0 ]]; then
    echo >&2 "LR_SYNTH_TIMING_RUN requires LR_SYNTH_FLATTEN!";
    exit 1;
fi

# Output directory
export LR_SYNTH_OUT_DIR_PREFIX="syn_out/${LR_SYNTH_TOP_MODULE}"
LR_SYNTH_OUT_DIR=$(date +"${LR_SYNTH_OUT_DIR_PREFIX}_%Y_%m_%d_%H_%M_%S")
export LR_SYNTH_OUT_DIR
