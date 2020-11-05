#!/bin/bash

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This script drives the experimental Ibex synthesis flow. More details can be
# found in README.md

if [ ! -f syn_setup.sh ]; then
  echo "Must provide syn_setup.sh file"
  echo "See example in syn_setup.example.sh and README.md for instructions"
  exit 1
fi

#-------------------------------------------------------------------------
# setup flow variables
#-------------------------------------------------------------------------
source syn_setup.sh

#-------------------------------------------------------------------------
# use sv2v to convert all SystemVerilog files to Verilog
#-------------------------------------------------------------------------

mkdir -p "$LR_SYNTH_OUT_DIR/generated"
mkdir -p "$LR_SYNTH_OUT_DIR/log"
mkdir -p "$LR_SYNTH_OUT_DIR/reports/timing"

for file in ../rtl/*.sv; do
  module=`basename -s .sv $file`
  sv2v \
    --define=SYNTHESIS \
    ../rtl/*_pkg.sv \
    -I../vendor/lowrisc_ip/prim/rtl \
    $file \
    > $LR_SYNTH_OUT_DIR/generated/${module}.v
done

# remove generated *pkg.v files (they are empty files and not needed)
rm -f $LR_SYNTH_OUT_DIR/generated/*_pkg.v

# remove tracer (not needed for synthesis)
rm -f $LR_SYNTH_OUT_DIR/generated/ibex_tracer.v

# remove the FPGA & register-based register file (because we will use the
# latch-based one instead)
rm -f $LR_SYNTH_OUT_DIR/generated/ibex_register_file_ff.v
rm -f $LR_SYNTH_OUT_DIR/generated/ibex_register_file_fpga.v

yosys -c ./tcl/yosys_run_synth.tcl | tee ./$LR_SYNTH_OUT_DIR/log/syn.log

sta ./tcl/sta_run_reports.tcl | tee ./$LR_SYNTH_OUT_DIR/log/sta.log

./translate_timing_rpts.sh

python/get_kge.py $LR_SYNTH_CELL_LIBRARY_PATH $LR_SYNTH_OUT_DIR/reports/area.rpt
