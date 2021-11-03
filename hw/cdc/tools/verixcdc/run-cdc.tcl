# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

#####################
##  PREPARE FLOW   ##
#####################

proc get_env_var {name} {
  if {[info exists ::env($name)]} {
    set val "[set ::env([set name])]"
    puts "::env($name) = $val"
    return $val
  } else {
    puts "ERROR: Script run without $name environment variable."
    quit
  }
}

set FOUNDRY_ROOT       [get_env_var "FOUNDRY_ROOT"]
set SV_FLIST           [get_env_var "SV_FLIST"]
set BUILD_DIR          [get_env_var "BUILD_DIR"]
set DUT                [get_env_var "DUT"]
set CONSTRAINT         [get_env_var "CONSTRAINT"]
set FOUNDRY_CONSTRAINT [get_env_var "FOUNDRY_CONSTRAINT"]
set PARAMS             [get_env_var "PARAMS"]
set CDC_WAIVER_FILE    [get_env_var "CDC_WAIVER_FILE"]
set ENV_FILE           [get_env_var "ENV_FILE"]

# Used to disable some SDC constructs that are not needed by CDC.
set IS_CDC_RUN 1

########################
## Library Setup      ##
########################

# if the foundry root is specified, some more library setup is needed.
if {$FOUNDRY_ROOT != ""} {
  # TODO: add lib setup tcl file here
  # this PRIM_DEFAULT_IMPL selects the appropriate technology by defining
  # PRIM_DEFAULT_IMPL=prim_pkg::Impl<tech identifier>
  # PRIM_DEFAULT_IMPL is set inside the library setup script
  set DEFINE "PRIM_DEFAULT_IMPL=${PRIM_DEFAULT_IMPL}+${PRIM_STD_CELL_VARIANT}"
  source "${FOUNDRY_ROOT}/cdc/verixcdc/setup.tcl"
} else {
  set DEFINE ""
}

########################
## Configure CDC Tool ##
########################

# TODO: potentially more settings are needed.
# set ri_enable_sva false
set ri_create_outputs_in_create_env true
set ri_print_module_nand2_counts true
# enable analysis of large arrays
set ri_max_total_range_bits 100000

#########################
## Analyze & Elaborate ##
#########################

if {$DEFINE != ""} {
  analyze -sverilog +define+${DEFINE} -f ${SV_FLIST}
} else {
  analyze -sverilog -f ${SV_FLIST}
}

if {$PARAMS != ""} {
  elaborate -params "$PARAMS" $DUT
} else {
  elaborate $DUT
}

#########################
## Apply Constraints   ##
#########################

read_sdc $CONSTRAINT
if {$FOUNDRY_CONSTRAINT != ""} {
  read_sdc $FOUNDRY_CONSTRAINT
}

############################
## Apply Environment File ##
############################

if {$ENV_FILE != ""} {
  read_env $ENV_FILE
}

#########################
## Run CDC             ##
#########################

analyze_intent
verify_cdc

#########################
## Read in Waivers     ##
#########################

source $CDC_WAIVER_FILE

#########################
## Write out report    ##
#########################

report_policy -verbose -skip_empty_summary_status -compat -output vcdc.rpt ALL
