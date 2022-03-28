#!/bin/bash

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Setup IP name and top module.
# When changing the top module, some parameters might not exist and
# tcl/yosys_run_synth.tcl might need to be adjusted accordingly.
# Known working top modules are: keccak_2share, keccak_round, sha3, kmac
export LR_SYNTH_IP_NAME=kmac
export LR_SYNTH_TOP_MODULE=keccak_2share

# Setup module parameters. The Width is actually 1600 but it can have any value
# in [25, 50, 100, 200, 400, 800, 1600]. We choose 25 instead to get smaller
# netlist thereby speeding up the formal masking verification. Ignored for sha3
# and kmac top modules.
export LR_SYNTH_WIDTH=25
export LR_SYNTH_EN_MASKING=1

# Setup cell library path.
# Change the line below to set the path to an appropriate .lib file
#export LR_SYNTH_CELL_LIBRARY_PATH=/path/to/NangateOpenCellLibrary_typical.lib
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
if [ $# -eq 1 ]; then
    export LR_SYNTH_OUT_DIR=$1
elif [ $# -eq 0 ]; then
    export LR_SYNTH_OUT_DIR_PREFIX="syn_out/${LR_SYNTH_TOP_MODULE}"
    export LR_SYNTH_OUT_DIR=$(date +"${LR_SYNTH_OUT_DIR_PREFIX}_%Y_%m_%d_%H_%M_%S")
else
    echo "Usage $0 [synth_out_dir]"
    exit 1
fi
