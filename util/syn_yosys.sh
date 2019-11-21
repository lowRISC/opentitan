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
# use fusesoc to generate files and file list
#-------------------------------------------------------------------------
\rm -Rf build
fusesoc --cores-root .. run --target=sim --setup --build formal > /dev/null 2>&1

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
  sv2v --define=VERILATOR --define=SYNTHESIS *_pkg.sv prim_assert.sv $file > ${module}.v

  # TODO: eventually remove below hack. It removes "unsigned" from params
  # because Yosys doesn't support unsigned parameters
  sed -i 's/parameter unsigned/parameter/g' ${module}.v
  sed -i 's/localparam unsigned/localparam/g' ${module}.v
done

# remove *pkg.v files (they are empty files and not needed)
\rm -Rf *_pkg.v

#-------------------------------------------------------------------------
# run LEC (generarted Verilog vs. original SystemVerilog)
#-------------------------------------------------------------------------
printf "\n\nLEC RESULTS:\n"
cd ../../hw/formal
for file in ../../util/syn_out/*.v; do
  module=`basename -s .v $file`
  lec_sv2v ../../util/syn_out $module > /dev/null 2>&1

  # summarize results
  result=`grep "Compare Results" lec_${module}.log`
  if [ $? -ne 0 ]; then
    result="CRASH"
  else
    result=`echo $result | awk '{ print $4 }'`
  fi
  printf "%-25s %s\n" $module $result
done
cd -

#-------------------------------------------------------------------------
# run yosys
#-------------------------------------------------------------------------
printf "\n\nYosys:\n"

# for now, read in each Verilog file into Yosys and only output errors
# and warnings
for file in *.v; do
  yosys -QTqp "read_verilog ${file}"
done

# TODOs:
#  - add full yosys synthesis for all modules
#  - add final LEC check (RTL-versus-netlist)
