// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// dofile for LEC script rtl_diff

//-----------------------------------------------------------------
// read in golden and revised
//-----------------------------------------------------------------
read library -sv09 -f formal_0.scr

// read golden design
read design -golden -sv09 \
  ../../../../ip/prim/rtl/prim_assert.sv \
  ../../../../top_earlgrey/rtl/*_pkg.sv \
  ../../../../ip/*/rtl/*_pkg.sv \
  ../../../../vendor/*/*/*_pkg.sv \
  $LEC_GOLDEN

// read revised design
read design -revised -sv09 \
  ../../../../ip/prim/rtl/prim_assert.sv \
  ../../../../top_earlgrey/rtl/*_pkg.sv \
  ../../../../ip/*/rtl/*_pkg.sv \
  ../../../../vendor/*/*/*_pkg.sv \
  $LEC_REVISED

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
