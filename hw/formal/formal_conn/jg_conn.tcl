# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# clear previous settings
clear -all

# We use parameter instead of localparam in packages to allow redefinition
# at elaboration time.
# Disabling the warning
# "parameter declared inside package XXX shall be treated as localparam".
set_message -disable VERI-2418

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
blackbox_assistant -config -connectivity_Map ../../../top_earlgrey_conn.csv

elaborate -top $env(FPV_TOP)

clock IO_CLK
reset -expr {!IO_RST_N}

#-------------------------------------------------------------------------
# configure proofgrid
#-------------------------------------------------------------------------
set_proofgrid_per_engine_max_local_jobs 2

# Uncomment below 2 lines when using LSF:
# set_proofgrid_mode lsf
# set_proofgrid_per_engine_max_jobs 16

check_conn -load ../../../top_earlgrey_conn.csv
#-------------------------------------------------------------------------
# prove all assertions & report
#-------------------------------------------------------------------------
# time limit set to 2 hours
prove -task Connectivity -time_limit 1h
report -task Connectivity

#-------------------------------------------------------------------------
# check coverage and report
#-------------------------------------------------------------------------
if {$env(COV) == 1} {
  check_cov -measure
  check_cov -report -type all -no_return -report_file cover.html \
      -html -force -exclude { reset waived }
}

