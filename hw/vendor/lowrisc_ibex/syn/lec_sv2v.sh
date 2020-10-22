#!/bin/bash

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This script converts all SystemVerilog RTL files to Verilog
# using sv2v and then runs LEC (Cadence Conformal) to check if
# the generated Verilog is logically equivalent to the original
# SystemVerilog.  A similar script is used in OpenTitan, any updates 
# or fixes here may need to be reflected in the OpenTitan script as well
# https://github.com/lowRISC/opentitan/blob/master/util/syn_yosys.sh
#
# The following tools are required:
#  - sv2v: SystemVerilog-to-Verilog converter from github.com/zachjs/sv2v
#  - Cadence Conformal
#
# Usage:
#   ./lec_sv2v.sh |& tee lec.log

#-------------------------------------------------------------------------
# use fusesoc to generate files and file list
#-------------------------------------------------------------------------
rm -Rf build lec_out
fusesoc --cores-root .. run --tool=icarus --target=lint \
  --setup "lowrisc:ibex:ibex_core" > /dev/null 2>&1

# copy all files to lec_out
mkdir lec_out
cp build/*/src/*/*.sv build/*/src/*/*/*.sv lec_out
cd lec_out

# copy file list and remove incdir, RVFI define, and sim-file
egrep -v 'incdir|RVFI|simulator_ctrl' ../build/*/*/*.scr > flist_gold

# remove all hierarchical paths
sed -i 's!.*/!!' flist_gold

# generate revised flist by replacing '.sv' by '.v' and removing packages
sed 's/.sv/.v/' flist_gold | grep -v "_pkg.v" > flist_rev

#-------------------------------------------------------------------------
# convert all RTL files to Verilog using sv2v
#-------------------------------------------------------------------------
printf "\nSV2V ERRORS:\n"

for file in *.sv; do
  module=`basename -s .sv $file`
  sv2v --define=SYNTHESIS *_pkg.sv prim_assert.sv $file > ${module}.v
done

# remove *pkg.v files (they are empty files and not needed)
rm -f *_pkg.v prim_assert.v prim_util_memload.v

# overwrite the prim_clock_gating modules with the module from ../rtl
cp ../rtl/prim_clock_gating.v .
cp ../rtl/prim_clock_gating.v prim_clock_gating.sv

#-------------------------------------------------------------------------
# run LEC (generated Verilog vs. original SystemVerilog)
#-------------------------------------------------------------------------
printf "\n\nLEC RESULTS:\n"

for file in *.v; do
  export LEC_TOP=`basename -s .v $file`

  # run Conformal LEC
  lec -xl -nogui -nobanner \
    -dofile  ../lec_sv2v.do \
    -logfile lec_${LEC_TOP}.log \
    <<< "exit -force" > /dev/null 2>&1

  # summarize results
  check=`grep "Compare Results" lec_${LEC_TOP}.log`
  if [ $? -ne 0 ]; then
    result="CRASH"
  else
    result=`echo $check | awk '{ print $4 }'`
  fi
  printf "%-25s %s\n" $LEC_TOP $result
done
