# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

################################################################################
#
# Default TCL script passed to the RTL simulator at run-time to drive the simulation.
# e.g.
#     VCS: -ucli -do <this file>
# Xcelium: -input <this file>
#
# This default script has the following features, controlled by a set of environment
# variables..
# - Open a default waveform database
# - Dump waveforms from a single heirarchy, by default the testbench top (i.e. everything)
# - Supports interactive simulations (i.e. gui mode) by returning early to reliquish control
# - Run the simulation to completion and exits
#
# These features are configured by a set of global-scoped variables, which have default
# values but can take new values from all-uppercase environment variables of the same name.
# The following variables are supported:
#
# - simulator(SIMULATOR) mandatory    ""        RTL Simulator to use
# - waves(WAVES)         optional     "none"    Waveform format for waveform dumping, opens a default database
# - gui(GUI)             optional     0         Return early for user control in a GUI context
# - tb_top(TB_TOP)       optional     "tb"      Top-level module in simulation (typically the testbench)
#
# The sourced .tcl files may assume the existence of these variables in the global scope.
################################################################################

# First, locate the 'dv_root' directory, from which we can import any associated
# .tcl libraries and common routines.
# Alternate top level .tcl scripts can use the same variable to import any common
# project Tcl code they may wish to make use of.
if {[info exists ::env(dv_root)]} {set dv_root "$::env(dv_root)"} \
else {puts "ERROR: Script run without dv_root environment variable."; exit}

# Helper procedure libraries
source "$dv_root/tools/tcl/procs.tcl"
source "$dv_root/tools/tcl/procs_waves.tcl"
source "$dv_root/tools/tcl/procs_run.tcl"

# Set the following global TCL variables with default values, optionally overriding
# them with values from uppercase Environment Variables.
set simulator ""
set waves "none"
set gui 0
set tb_top "tb"
setViaUpcaseEnvVarElseError simulator
setViaUpcaseEnvVar waves
setViaUpcaseEnvVar gui
setViaUpcaseEnvVarElseWarning tb_top "WARNING: TB_TOP environment variable not set - assuming '$tb_top' as the top-level testbench hierarchy."

# Default Waveform Dumping
# If waves are enabled (i.e. $waves != "none"), enable the default waveform dump, which:
# - Opens a default database
# - Probes all waves (infinite depth) from the scope $tb_top
if {$waves ne "none"} {
  set scope $tb_top
  source "$dv_root/tools/tcl/capture_single_waves_scope.tcl"
}

# Import any simulator-specific TCL
if {$simulator eq "xcelium"} {source "$dv_root/tools/xcelium/sim.tcl"}

# In GUI mode, return from this file now, resuming user-control of the simulator's TCLSH.
if {$gui == 1} {return;}

# Now we are ready to run the simulation.
run_to_completion_and_exit
