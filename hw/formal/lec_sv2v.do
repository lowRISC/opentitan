// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// dofile for LEC script lec_sv2v

//-------------------------------------------------------------------------
// read in golden (SystemVerilog) and revised (Verilog)
//-------------------------------------------------------------------------
set parallel option -threads 8

// map all multi-dimensional ports (including structs) onto 1-dim. ports
set naming rule -mdportflatten

read design -golden -sv12 -f flist_gold -rootonly -root $LEC_TOP
read design -revised -ve  -f flist_rev  -rootonly -root $LEC_TOP

//-------------------------------------------------------------------------
// pre-LEC reports
//-------------------------------------------------------------------------
report rule check -verbose
report design data
report black box
report module

//-------------------------------------------------------------------------
// compare
//-------------------------------------------------------------------------
set mapping method -name_effort low
set system mode lec
report unmapped points

add compare point -all
compare -threads 8 -noneq_stop 1
analyze abort -compare

//-------------------------------------------------------------------------
// reports
//-------------------------------------------------------------------------
report compare data -class nonequivalent -class abort -class notcompared
report verification -verbose
report statistics
usage

exit -force
