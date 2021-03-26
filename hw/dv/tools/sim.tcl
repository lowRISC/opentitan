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

source "${dv_root}/tools/common.tcl"
source "${dv_root}/tools/waves.tcl"

# In GUI mode, let the user take control of running the simulation.
global gui
if {$gui == 0} {
  run
  quit
}
