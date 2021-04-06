# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# clear previous settings
clear -all

source $env(COMMON_MSG_TCL_PATH)

if {$env(COV) == 1} {
  check_cov -init -model {branch statement functional} \
  -enable_prove_based_proof_core
}
#-------------------------------------------------------------------------
# read design
#-------------------------------------------------------------------------

# only one scr file exists in this folder
analyze -sv09                 \
  +define+FPV_ON              \
  -f [glob *.scr]

# Black-box assistant will blackbox the modules which are not needed by looking at
# the connectivity csv.
blackbox_assistant -config -connectivity_Map $env(CSV_PATH)

# This is jg work-around when black-boxing with inout ports
set_port_direction_handling coercion_weak_bbox

elaborate -top $env(DUT_TOP)

# Currently only for top_earlgrey
if {$env(DUT_TOP) == "top_earlgrey"} {
  clock clk_main_i
  clock clk_io_i
  clock clk_usb_i
  clock clk_aon_i
  reset -expr {rst_ni}
}

#-------------------------------------------------------------------------
# configure proofgrid
#-------------------------------------------------------------------------
set_proofgrid_mode local
set_proofgrid_per_engine_max_local_jobs 2

# Uncomment below 2 lines when using LSF:
# set_proofgrid_mode lsf
# set_proofgrid_per_engine_max_jobs 16

check_conn -load $env(CSV_PATH)

#-------------------------------------------------------------------------
# prove all assertions & report
#-------------------------------------------------------------------------
# time limit set to 2 hours
prove -task Connectivity -time_limit 2h
report -task Connectivity

#-------------------------------------------------------------------------
# check coverage and report
#-------------------------------------------------------------------------
if {$env(COV) == 1} {
  check_cov -measure -time_limit 2h
  check_cov -report -type all -no_return -report_file cover.html \
      -html -force -exclude { reset waived }
}
