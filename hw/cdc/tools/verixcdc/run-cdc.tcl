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
set CDC_WAIVER_DIR     [file dirname $CDC_WAIVER_FILE]
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

# TODO(#11492): Fix the issue of CDC delay
if {$DEFINE != ""} {
  analyze -sverilog +define+${DEFINE} +define+AST_BYPASS_CLK -f ${SV_FLIST}
} else {
  analyze -sverilog  +define+AST_BYPASS_CLK -f ${SV_FLIST}
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
## Top Modules         ##
#########################
# TODO: modules are used after elaboration. If a module is instantiated
# multiple times, the module name should be uniquified name.
# Due to this, uart, i2c, spi_host reports are not correct.
set modules {
  spi_device
  kmac
  hmac
  uart
  gpio
  spi_host
  flash_ctrl
  alert_handler
  otp_ctrl
  lc_ctrl
  pwrmgr
  clkmgr
  rstmgr
  keymgr
  csrng
  entropy_src
  aes
  rom_ctrl
}

#########################
## Read in Waivers     ##
#########################

source $CDC_WAIVER_FILE

#########################
## Write out report    ##
#########################

report_policy -verbose -skip_empty_summary_status -compat -output vcdc.rpt ALL

file mkdir ../REPORT/

foreach mod $modules {
  report_policy -verbose -skip_empty_summary_status -compat -output ../REPORT/vcdc.$mod.rpt -module $mod {NEW TO_BE_FIXED DEFERRED}
}

# Report waived in a separate file
report_policy -verbose -skip_empty_summary_status -compat -output ../REPORT/vcdc.rpt {NEW TO_BE_FIXED DEFERRED}
report_policy -verbose -skip_empty_summary_status -compat -output ../REPORT/vcdc.waived.rpt {WAIVED}

# report_messages -output verix_cdc.rpt

# Clock report
report_clock_domains -flops -output ../REPORT/clocks.flops.rpt
report_clock_matrix -output ../REPORT/clocks.matrix.rpt
