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

read design -golden -sv09 -f flist_gold -rootonly -root $LEC_TOP
read design -revised -sys -f flist_rev  -rootonly -root $LEC_TOP
// TODO: instead of using switch -sys (for old SystemVerilog,
// older than sv2009) we should use -ve (for Verilog). But
// currently that doesn't work because sv2v doesn't translate
// .* port connections. Is that an sv2v bug?

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
set system mode lec

// map key points and I/O ports: because Verilog only supports
// 1-dimensional I/O ports, convert all multi-dim. ports to 1-dim.
set mapping method -nets -mem -unreach
map key points
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
