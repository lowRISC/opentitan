#!/bin/bash

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This script converts all SystemVerilog RTL files to Verilog and then
# runs Yosys.
#
# The following tools are required:
#  - sv2v: SystemVerilog-to-Verilog converter from github.com/zachjs/sv2v
#  - yosys: synthesis tool from github.com/YosysHQ/yosys
#
# Usage:
#   syn_yosys.sh 2>&1 | tee syn.std

#-------------------------------------------------------------------------
# use fusesoc to generate file list
#-------------------------------------------------------------------------
\rm -Rf build
fusesoc --cores-root .. sim --build-only formal > /dev/null 2>&1

# copy all files into directory "syn_out"
\rm -Rf syn_out
mkdir syn_out
cp build/formal_0/src/*/*/*.sv build/formal_0/src/*/*/*/*.sv syn_out

#-------------------------------------------------------------------------
# convert all RTL files to Verilog
#-------------------------------------------------------------------------
cd syn_out

for file in *.sv; do
  module=`basename -s .sv $file`
  echo $file
  sv2v --define=VERILATOR --oneunit *_pkg.sv prim_assert.sv $file > ${module}.v

  # TODO: eventually remove below hack. It removes "unsigned" from params
  # because Yosys doesn't support unsigned parameters
  sed -i 's/parameter unsigned/parameter/g' ${module}.v
  sed -i 's/localparam unsigned/localparam/g' ${module}.v
done

# remove *pkg.v files (they are empty files and not needed)
\rm -Rf *_pkg.v

#-------------------------------------------------------------------------
# run yosys
#-------------------------------------------------------------------------

# for now, read in each verilog file into Yosys and only output errors
# and warnings
for file in *.v; do
  yosys -QTqp "read_verilog ${file}"
done

cd -

# TODOs:
#  - add LEC to check if generated Verilog is equivalent to original SV
#  - add full yosys synthesis for all modules
#  - add final LEC check (RTL-versus-netlist)
