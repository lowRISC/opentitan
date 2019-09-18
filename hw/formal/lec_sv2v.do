// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// dofile for LEC script lec_sv2v

//-----------------------------------------------------------------
// read in golden (SystemVerilog) and revised (Verilog)
//-----------------------------------------------------------------

// black box all instantiated modules (so only top-module is used)
set undefined cell black_box

// read golden design
read design -golden -sv09 \
  $LEC_DIR/prim_assert.sv \
  $LEC_DIR/top_pkg.sv \
  $LEC_DIR/tlul_pkg.sv \
  $LEC_DIR/*_pkg.sv \
  $LEC_DIR/$LEC_TOP.sv

// read revised design
read design -revised -verilog \
  $LEC_DIR/$LEC_TOP.v

//-----------------------------------------------------------------
// pre-LEC reports
//-----------------------------------------------------------------
report design data
report black box
report module

//-----------------------------------------------------------------
// compare
//-----------------------------------------------------------------
set system mode lec
map key points
set parallel option -threads 4
analyze datapath -merge -verbose -effort ultra
add compare point -all
set compare effort ultra
compare -threads 4
analyze abort -compare

//-----------------------------------------------------------------
// reports
//-----------------------------------------------------------------
report compare data -class nonequivalent -class abort -class notcompared
report verification -verbose
report statistics
usage

exit -force
