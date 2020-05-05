# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# TCL file invoked from xcelium simulations at run-time using this: -input <this file>

# Get some environment variables we need.
set en_waves 0
set tool_srcs_dir ""
if {[info exists ::env(EN_WAVES)]} {
    set en_waves "$::env(EN_WAVES)"
}
if {[info exists ::env(TOOL_SRCS_DIR)]} {
    set tool_srcs_dir "$::env(TOOL_SRCS_DIR)"
} else {
    puts "ERROR: tool script run without TOOL_SRCS_DIR environment variable."
    quit
}

# If wave dumping is enabled, run waves.tcl
if {"$en_waves" == 1} {
    source "${tool_srcs_dir}/waves.tcl"
}

run
quit
