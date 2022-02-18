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

set conn_csvs [regexp -all -inline {[^\s\']+} $env(CONN_CSVS)]
if {$conn_csvs eq ""} {
  puts "ERROR: CONN_CSVS environment variable is empty."
  quit
}

#-------------------------------------------------------------------------
# read design
#-------------------------------------------------------------------------

# only one scr file exists in this folder
# Blackbox ast related modules to avoid compile errors.
analyze -sv09     \
  +define+FPV_ON  \
  -f [glob *.scr] \
  -bbox_m aon_osc \
  -bbox_m io_osc  \
  -bbox_m sys_osc \
  -bbox_m usb_osc

# Black-box assistant will blackbox the modules which are not needed by looking at
# the connectivity csv.
blackbox_assistant -config -connectivity_map $conn_csvs

# This is jg work-around when black-boxing with inout ports
set_port_direction_handling coercion_weak_bbox

elaborate -top $env(DUT_TOP)

# Add this assumption to avoid a false functional loop.
assume -env {top_earlgrey.u_pinmux_aon.reg2hw.mio_pad_sleep_status == '1}

# Currently only for top_earlgrey
# Because in JasperGold we can only drive primary inputs. We put a stopat to aovid clock input
# from being driven internally.
if {$env(DUT_TOP) == "chip_earlgrey_asic"} {
  stopat -env IOC6
  clock IOC6
  reset -expr {POR_N}
}

#-------------------------------------------------------------------------
# configure proofgrid
#-------------------------------------------------------------------------
set_proofgrid_mode local
set_proofgrid_per_engine_max_local_jobs 16

# Uncomment below 2 lines when using LSF:
# set_proofgrid_mode lsf
# set_proofgrid_per_engine_max_jobs 16

foreach i $conn_csvs {
  puts [format "Processing connectivity file %s" $i]
  check_conn -load $i
}

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
