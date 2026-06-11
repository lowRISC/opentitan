#!/usr/bin/env bash

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

if [ $# -eq 1 ]; then
  export LR_SYNTH_OUT_DIR=$1
elif [ $# -eq 0 ]; then
  export LR_SYNTH_OUT_DIR_PREFIX="syn_out/ibex"
  LR_SYNTH_OUT_DIR=$(date +"${LR_SYNTH_OUT_DIR_PREFIX}_%d_%m_%Y_%H_%M_%S")
  export LR_SYNTH_OUT_DIR
else
  echo "Usage $0 [synth_out_dir]"
  exit 1
fi

export LR_SYNTH_TIMING_RUN=1
export LR_SYNTH_FLATTEN=1

# When using `nix develop .#syn_shell`, the following are set automatically by
# the shell hook (via nix/syn.nix):
#   LR_SYNTH_CELL_LIBRARY_PATH  (path to NangateOpenCellLibrary_typical.lib)
#   LR_SYNTH_CELL_LIBRARY_NAME  (nangate)
# For non-Nix environments, uncomment and set these manually:
# export LR_SYNTH_CELL_LIBRARY_PATH=/path/to/NangateOpenCellLibrary_typical.lib
# export LR_SYNTH_CELL_LIBRARY_NAME=nangate
