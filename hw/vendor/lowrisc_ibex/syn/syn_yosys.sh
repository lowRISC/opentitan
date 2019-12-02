#!/bin/bash

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This script converts all SystemVerilog RTL files to Verilog and then
# runs Yosys for ibex_core
#
# The following tools are required:
#  - sv2v: SystemVerilog-to-Verilog converter from github.com/zachjs/sv2v
#  - yosys: synthesis tool from github.com/YosysHQ/yosys
#
# Usage:
#   syn_yosys.sh 2>&1 | tee syn.std
#
# Above command generates two files:
#   ibex_core_premap.v  : premap netlist (before mapping it onto std. cells)
#   ibex_core_netlist.v : final netlist

# TODO: below should be replaced by elegant fusesoc commands

#-------------------------------------------------------------------------
# use sv2v to convert all SystemVerilog files to Verilog
#-------------------------------------------------------------------------
rm -Rf syn_out
mkdir syn_out

for file in ../rtl/*.sv; do
  module=`basename -s .sv $file`
  sv2v \
    --define=SYNTHESIS \
    ../rtl/*_pkg.sv \
    $file \
    > syn_out/${module}.v

  # TODO: eventually remove below hack. It removes "unsigned" from params
  # because Yosys doesn't support unsigned parameters
  sed -i 's/parameter unsigned/parameter/g'   syn_out/${module}.v
  sed -i 's/localparam unsigned/localparam/g' syn_out/${module}.v
done

# remove generated *pkg.v files (they are empty files and not needed)
rm -f syn_out/*_pkg.v

# remove the latch-based register file (because we will use the
# flop-based one instead)
rm -f syn_out/ibex_register_file_latch.v

#-------------------------------------------------------------------------
# run yosys
#-------------------------------------------------------------------------
yosys syn.ys -l syn.log
