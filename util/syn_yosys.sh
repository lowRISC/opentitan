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
#  - Cadence Conformal
#
# Usage:
#   ./syn_yosys.sh 2>&1 | tee syn.std

#-------------------------------------------------------------------------
# use fusesoc to generate files and file list
#-------------------------------------------------------------------------
\rm -Rf build syn_out
fusesoc --cores-root .. run --target=syn \
  --setup lowrisc:systems:top_earlgrey > /dev/null 2>&1

# copy all files into directory "syn_out"
mkdir syn_out
cp \
  build/*/src/*/*.sv* \
  build/*/src/*/*/*.sv* \
  build/*/src/*/*/*/*.sv* \
  syn_out
cd syn_out || exit

# copy file list, remove incdir and pins_if, and flatten pathnames
grep -Ev 'incdir|pins_if' ../build/*/*/*.scr | sed 's!.*/!!' > flist_gold

# generate revised flist by replacing '.sv' by '.v' and removing packages
sed -e 's/.sv/.v/g' flist_gold | grep -v "_pkg.v" > flist_rev

#-------------------------------------------------------------------------
# convert all RTL files to Verilog
#-------------------------------------------------------------------------

printf "\nSV2V VERSION:\n"
sv2v --version

printf "\nSV2V ERRORS:\n"

# drive strengths are not supported by Yosys
sed -i.bak -e "s/VERILATOR/SYNTHESIS/" prim_generic_pad_wrapper.sv

rm *.sv.bak

sv2v -DSYNTHESIS *.sv +RTS -N4 > combined.v
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

# all of top_earlgrey's submodules
declare -a modules=(
  "rv_dm"
  "spi_device"
  "usbdev"
  "flash_ctrl"
  "tlul_adapter_sram"
  "prim_rom_adv"
  "prim_ram_1p_adv"
  "uart"
  "gpio"
  "aes"
  "hmac"
  "pinmux"
  "alert_handler"
  "pwrmgr"
  "rstmgr"
  "clkmgr"
  "rv_timer"
  "rv_plic"
  "rv_core_ibex"
  "xbar_main"
  "xbar_peri"
  "flash_phy"
)

# TODO: top_earlgrey appears to be too large for verification under the currrent
# setup. Consider adding verification using `hier_compare`.

for module in "${modules[@]}"; do
  export LEC_TOP="$module"

  # run Conformal LEC
  lec -xl -nogui -nobanner \
    -dofile  ../../hw/formal/lec_sv2v.do \
    -logfile lec_${module}.log \
    <<< "exit -force" > /dev/null 2>&1

  # summarize results
  result=`grep "Compare Results" lec_${module}.log 2>&1`
  if [ $? -ne 0 ]; then
    result="CRASH"
  else
    result=`echo $result | awk '{ print $4 }'`
  fi
  printf "%-25s %s\n" $module $result
done

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
