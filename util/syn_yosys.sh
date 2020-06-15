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
#   ./syn_yosys.sh |& tee syn.std

#-------------------------------------------------------------------------
# use fusesoc to generate files and file list
#-------------------------------------------------------------------------
rm -Rf build syn_out

fusesoc --cores-root .. run --tool=icarus --target=syn \
  --setup "lowrisc:systems:top_earlgrey" > /dev/null 2>&1

# copy all files into directory "syn_out"
mkdir syn_out
cp build/*/src/*/*.sv* build/*/src/*/*/*.sv* build/*/src/*/*/*/*.sv* syn_out
cd syn_out

# copy file list and remove incdir lines
grep -v incdir ../build/*/*/*.scr > flist_gold

# remove all hierarchical paths
sed -i 's!.*/!!' flist_gold

# generate revised flist by replacing '.sv' by '.v' and removing packages
sed 's/.sv/.v/g' flist_gold | grep -v "_pkg.v" > flist_rev

#-------------------------------------------------------------------------
# convert all RTL files to Verilog
#-------------------------------------------------------------------------

# hack SystemVerilog files to avoid SV2V and/or LEC issues
# TODO: eventually remove these hacks

# 1) Setting ByteAccess = 0 for tlul_adapter_sram.sv doesn't work. This
# hack changes the functionality so needs fixing
sed -i 's/\.ByteAccess(0)/\.ByteAccess(1)/g' *.sv
sed -i 's/\.ByteAccess  (0)/\.ByteAccess(1)/g' *.sv

# 2) Replace "inside" experessions
sed -i 's/state_q inside {Read, WaitReadValid}/((state_q == Read) || (state_q == WaitReadValid))/' dmi_jtag.sv
sed -i 's/k inside {TckIdx, TmsIdx, TrstIdx, SrstIdx, TdiIdx, TdoIdx}/(k==TckIdx)||(k==TmsIdx)||(k==TrstIdx)||(k==SrstIdx)||(k==TdiIdx)||(k==TdoIdx)/' jtag_mux.sv
sed -i 's/(csr_op_i inside {CSR_OP_WRITE,/((csr_op_i==CSR_OP_WRITE)||(csr_op_i==CSR_OP_SET)||(csr_op_i==CSR_OP_CLEAR));/' ibex_cs_registers.sv
sed -i 's/    CSR_OP_SET,//' ibex_cs_registers.sv
sed -i 's/    CSR_OP_CLEAR});//' ibex_cs_registers.sv
sed -i "s/logic'(tl_i\.a_opcode inside {PutFullData, PutPartialData})/((tl_i\.a_opcode == PutFullData) || (tl_i\.a_opcode == PutFullData))/" tlul_adapter_sram.sv

# 3) Replace "inside" for dm_csrs.sv and dm_mem.sv. This hack changes
# the functionality so needs fixing
sed -i 's/) inside/)/g' dm_csrs.sv
sed -i 's/\[(dm::Data0):DataEnd\]:/dm::Data0:/g' dm_csrs.sv
sed -i 's/\[(dm::ProgBuf0):ProgBufEnd\]:/dm::ProgBuf0:/g' dm_csrs.sv
sed -i 's/inside//g' dm_mem.sv
sed -i 's/\[(dm::DataAddr):DataEndAddr\]:/dm::DataAddr:/' dm_mem.sv
sed -i 's/\[DataBaseAddr:DataEndAddr\]:/DataBaseAddr:/' dm_mem.sv
sed -i 's/\[ProgBufBaseAddr:ProgBufEndAddr\]:/ProgBufBaseAddr:/' dm_mem.sv
sed -i 's/\[AbstractCmdBaseAddr:AbstractCmdEndAddr\]:/AbstractCmdBaseAddr:/' dm_mem.sv
sed -i 's/\[FlagsBaseAddr:FlagsEndAddr\]:/FlagsBaseAddr:/' dm_mem.sv

printf "\nSV2V VERSION:\n"
sv2v --version

printf "\nSV2V ERRORS:\n"
for file in *.sv; do
  module=`basename -s .sv $file`
  sv2v --define=SYNTHESIS *_pkg.sv prim_assert.sv $file > ${module}.v
done

# postprocess generated Verilog to fix some more sv2v issues:
# TODO: remove below hacks eventually
sed -i "s/1'sb0/'d0/g" *.v
sed -i "s/1'sb1/-'sd1/g" *.v
sed -i 's/parameter ResetValue/parameter [0:0] ResetValue/' prim_flop_2sync.v

# remove *pkg.v files (they are empty files and not needed for Verilog)
\rm -Rf *_pkg.v

#-------------------------------------------------------------------------
# run LEC (generarted Verilog vs. original SystemVerilog)
#-------------------------------------------------------------------------
printf "\n\nLEC RESULTS:\n"

# top_earlgrey and all its submodules
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
  "padctrl"
  "alert_handler"
  "pwrmgr"
  "rstmgr"
  "clkmgr"
  "nmi_gen"
  "rv_timer"
  "rv_plic"
  "rv_core_ibex"
  "xbar_main"
  "xbar_peri"
  "flash_phy"
  "top_earlgrey"
)

# uncomment below two lines if you want to run LEC on all modules
# for file in *.v; do
#   export LEC_TOP=`basename -s .v $file`

for module in "${modules[@]}"; do
  export LEC_TOP="$module"

  # run Conformal LEC
  lec -xl -nogui -nobanner \
    -dofile  ../../hw/formal/lec_sv2v.do \
    -logfile lec_${LEC_TOP}.log \
    <<< "exit -force" > /dev/null 2>&1

  # summarize results
  result=`grep "Compare Results" lec_${LEC_TOP}.log`
  if [ $? -ne 0 ]; then
    result="CRASH"
  else
    result=`echo $result | awk '{ print $4 }'`
  fi
  printf "%-25s %s\n" $LEC_TOP $result
done

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
