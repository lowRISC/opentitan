# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Common TCL script invoked at run-time by the simulator.
# VCS syntax: -ucli -do <this file>
# Xcelium syntax: -input <this file>

set tool_srcs_dir ""
if {[info exists ::env(TOOL_SRCS_DIR)]} {
  set tool_srcs_dir "$::env(TOOL_SRCS_DIR)"
} else {
  puts "ERROR: Script run without TOOL_SRCS_DIR environment variable."
  quit
}

source "${tool_srcs_dir}/common.tcl"
source "${tool_srcs_dir}/waves.tcl"

run
quit
