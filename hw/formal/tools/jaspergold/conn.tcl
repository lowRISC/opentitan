# Copyright lowRISC contributors (OpenTitan project).
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
if {$env(BBOX_CMD) eq "" } {
  analyze -sv09 \
    +define+SYNTHESIS+$env(FPV_DEFINES) \
    -f [glob *.scr]
} else {
  analyze -sv09 \
    +define+SYNTHESIS+$env(FPV_DEFINES) \
    -bbox_m $env(BBOX_CMD) \
    -f [glob *.scr]
}

# analyze additional/overwrite design modules in CS
if {[info exists ::env(EXT_CS_DES_FILES_TCL)]} {
  source $env(EXT_CS_DES_FILES_TCL)
}


# Black-box assistant will blackbox the modules which are not needed by looking at
# the connectivity csv.
blackbox_assistant -config -connectivity_map $conn_csvs

# This is jg work-around when black-boxing with inout ports
set_port_direction_handling coercion_weak_bbox

elaborate -top $env(DUT_TOP)

# Currently only for top_earlgrey
if {$env(DUT_TOP) == "chip_earlgrey_asic"} {
  # Because in JasperGold we can only drive primary inputs, we put a stopat to
  # avoid the clock and reset inputs from being driven internally. Any logic
  # driving these signals is not included in the analysis. This includes e.g.:
  # - The disablement of the AST external clock input on IOC6. This is an MIO.
  # - The pull-up functionality on the power-on reset input pin which is
  #   enabled by default.
  stopat -env IOC6
  clock IOC6
  stopat -env POR_N
  reset -expr {POR_N}
  # Add this assumption to avoid a false functional loop.
  assume -env {top_earlgrey.u_pinmux_aon.reg2hw.mio_pad_sleep_status == '1}
  # Add this assumption to avoid signal inversion in the pad wrappers.
  assume -env {top_earlgrey.u_pinmux_aon.dio_pad_attr_q == '0}

  # run additional assume commands for foundry implementation if needed
  if {[info exists ::env(PARTNER_TCL)]} {
    source $env(PARTNER_TCL)
  }

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
