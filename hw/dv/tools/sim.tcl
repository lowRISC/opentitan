# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Common TCL script invoked at run-time by the simulator.
# VCS syntax: -ucli -do <this file>
# Xcelium syntax: -input <this file>

set dv_root ""
if {[info exists ::env(dv_root)]} {
  set dv_root "$::env(dv_root)"
} else {
  puts "ERROR: Script run without dv_root environment variable."
  quit
}

# Dumping waves in specific hierarchies.
#
# By default, if wave dumping is enabled, all hierarchies of the top level testbench are dumped.
# For large designs, this may slow down the simulation considerably. To bypass this and only enable
# waves in specific hierarchies, set the dump_tb_top flag to 0 (i.e. uncomment the line below), and
# specify the paths to dump on line 32.
# set dump_tb_top 0

source "${dv_root}/tools/common.tcl"
source "${dv_root}/tools/waves.tcl"

global waves
global simulator
global tb_top

# Dumping waves in specific hierarchies (example):
# wavedumpScope $waves $simulator tb.dut.foo.bar 12
# wavedumpScope $waves $simulator tb.dut.baz 0

if {$simulator eq "xcelium"} {
  puts "INFO: The following assertions are permamently disabled:"
  assertion -list -depth all -multiline -permoff $tb_top
}

# In GUI mode, let the user take control of running the simulation.
global gui
if {$gui == 0} {
  run
  if {$simulator eq "xcelium"} {
    # Xcelium provides a `finish` tcl command instead of `quit`. The argument '2' enables the
    # logging of additional resource usage information.
    finish 2
  } else {
    quit
  }
}
