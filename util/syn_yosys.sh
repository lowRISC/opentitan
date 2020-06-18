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
fusesoc --cores-root .. run --target=syn --setup lowrisc:systems:top_earlgrey

# copy all files into directory "syn_out"
\rm -Rf syn_out
mkdir syn_out
cp \
  build/lowrisc_systems_top_earlgrey_0.1/src/*/*.sv \
  build/lowrisc_systems_top_earlgrey_0.1/src/*/*/*.sv \
  build/lowrisc_systems_top_earlgrey_0.1/src/*/*/*/*.sv \
  syn_out
cd syn_out

# not synthesizable
\rm prim_pad_wrapper.sv
\rm prim_generic_pad_wrapper.sv

# not used for synthesis
\rm pins_if.sv
\rm tlul_assert.sv
\rm tlul_assert_multiple.sv

# match filename to module name
mv ibex_register_file{_ff,}.sv

# prim_util_memload.sv is only meant to be included within a module
mv prim_util_memload.sv{,h}
sed -i.delete.bak -e "s/prim_util_memload\.sv/prim_util_memload.svh/" *.sv
rm *.delete.bak  # some sed implementations require backup extensions

#-------------------------------------------------------------------------
# convert all RTL files to Verilog
#-------------------------------------------------------------------------
printf "\n\nsv2v:\n"
sv2v -DSYNTHESIS *.sv > combined.v
# split files up
modules=`cat combined.v | grep "^module" | sed -e "s/^module //" | sed -e "s/ (//"`
echo "$modules" > modules.txt  # for debugging
for module in $modules; do
  sed -n "/^module $module /,/^endmodule/p" < combined.v > $module.v
done
rm combined.v

#-------------------------------------------------------------------------
# run LEC (generarted Verilog vs. original SystemVerilog)
#-------------------------------------------------------------------------
printf "\n\nLEC RESULTS:\n"
cd ../../hw/formal
for file in ../../util/syn_out/*.v; do
  module=`basename -s .v $file`
  ./lec_sv2v ../../util/syn_out $module > /dev/null 2>&1

  # summarize results
  result=`grep "Compare Results" lec_${module}.log 2>&1`
  if [ $? -ne 0 ]; then
    result="CRASH"
  else
    result=`echo $result | awk '{ print $4 }'`
  fi
  printf "%-35s %s\n" $module $result
done
cd -

#-------------------------------------------------------------------------
# run yosys
#-------------------------------------------------------------------------
printf "\n\nYosys:\n"
yosys -QTqp "
read_verilog *.v;
hierarchy -check -top top_earlgrey;
synth_xilinx;
write_blif out.blif;
write_edif out.edif;
write_json out.json;
"

# TODOs:
#  - add full yosys synthesis for all modules
#  - add final LEC check (RTL-versus-netlist)
