// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// dofile for LEC script lec_sv2v

//-----------------------------------------------------------------
// read in golden (SystemVerilog) and revised (Verilog)
//-----------------------------------------------------------------

// black box all instantiated modules (so only top-module is used)
set undefined cell black_box

// flatten module ports for comparison
set naming rule -mdportflatten

// Some of the prim_generic_ modules are instantiated using SystemVerilog
// wildcard port bindings. These wildcard bindings are elaborated during
// conversion. For the comparison to work, we need to read the signature of
// these modules, but we still want to treat them as black boxes.
add notranslate filepathnames $LEC_DIR/prim_*.*

// ensure the module under test is not blackboxed
add notranslate filepathnames $LEC_DIR/$LEC_TOP.*
del notranslate filepathnames $LEC_DIR/$LEC_TOP.*

// read golden design
read design -golden -sv12 \
  $LEC_DIR/top_pkg.sv \
  $LEC_DIR/tlul_pkg.sv \
  $LEC_DIR/*_pkg.sv \
  $LEC_DIR/prim_*.sv \
  $LEC_DIR/$LEC_TOP.sv

// read revised design
read design -revised -verilog \
  $LEC_DIR/prim_*.v \
  $LEC_DIR/$LEC_TOP.v

// force comparison of the desired module
set root module $LEC_TOP -both

//-----------------------------------------------------------------
// pre-LEC reports
//-----------------------------------------------------------------
report design data
report black box
report module

//-----------------------------------------------------------------
// compare
//-----------------------------------------------------------------
set mapping method -noname
set system mode lec
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
