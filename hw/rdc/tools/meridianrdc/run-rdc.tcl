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

set FOUNDRY_ROOT        [get_env_var "FOUNDRY_ROOT"]
set SV_FLIST            [get_env_var "SV_FLIST"]
set BUILD_DIR           [get_env_var "BUILD_DIR"]
set DUT                 [get_env_var "DUT"]
set CONSTRAINT          [get_env_var "CONSTRAINT"]
set FOUNDRY_CONSTRAINT  [get_env_var "FOUNDRY_CONSTRAINT"]
set PARAMS              [get_env_var "PARAMS"]
set RDC_WAIVER_FILE     [get_env_var "RDC_WAIVER_FILE"]
set RDC_WAIVER_DIR      [file dirname $RDC_WAIVER_FILE]
set ENV_FILE            [get_env_var "ENV_FILE"]
set RESET_SCENARIO_FILE [get_env_var "RESET_SCENARIO_FILE"]

# WAVES is optional
set WAVES ""
if {[info exists ::env(WAVES)]} {
  set WAVES "$::env(WAVES)"
  puts "::env(WAVES) = ${WAVES}"
}

# Used to disable some SDC constructs that are not needed by RDC.
# Reusing IS_CDC_RUN
set IS_CDC_RUN 1

########################
## Library Setup      ##
########################

# if the foundry root is specified, some more library setup is needed.
# Reusing CDC setup
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
## Configure RDC Tool ##
########################

# TODO: potentially more settings are needed.
# set ri_enable_sva false
set ri_create_outputs_in_create_env true
set ri_print_module_nand2_counts true
# enable analysis of large arrays
set ri_max_total_range_bits 100000
set ri_rdc_stop_at_clock_path_in_obs_analysis true
set ri_rdc_no_observability_on_clock_nodes true

#Dump waveforms for all violations
switch $WAVES {
  "" {
  }

  "vcd" {
    set ri_max_number_of_reset_scenario_vcds all
    set ri_write_all_nodes_in_vcd_for_reset_scenario true
  }

  default {
    puts "ERROR: Unknown wave format: ${WAVES}"
    quit
  }
}

#########################
## Analyze & Elaborate ##
#########################

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

#################################
## Define Common Synchronizers ##
#################################

# -force:      Force suppression of E_RST_METASTABILITY violation going to this
#              cell
# -supress_rf: Force suppression of E_RST_METASTABILITY violation going
#              "through" this cell
set_rdc_user_defined_sync_cell -force prim_flop_2sync \
  -comment "async reset then 2FF @ CLK"

#########################
## Apply Constraints   ##
#########################

# Create Scenario for each constraint
create_scenario { sdc env }

set envs env_from_public_sdc.env

read_sdc -scenario sdc -output_env $envs $CONSTRAINT

if {$FOUNDRY_CONSTRAINT != ""} {
  lappend envs env_from_foundry_sdc.env
  read_sdc -scenario sdc -output_env [lindex $envs 1] $FOUNDRY_CONSTRAINT
}

############################
## Apply Environment File ##
############################

# default scenario to env
current_scenario env

if {$ENV_FILE != ""} {
  lappend envs $ENV_FILE
}

read_env $envs

#########################
## Analyze + Scenario  ##
#########################

analyze_intent

create_set_reset_scenario_script -output reset_scenarios.tcl -primary

# Import hand-edited reset scenario file
if {$RESET_SCENARIO_FILE != ""} {
  source $RESET_SCENARIO_FILE
} else {
  source reset_scenarios.tcl
}

#########################
## Run RDC             ##
#########################

verify_rdc

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
  edn
}

#########################
## Read in Waivers     ##
#########################

if {[file exists $RDC_WAIVER_FILE]} {
  source $RDC_WAIVER_FILE
}

#########################
## Write out report    ##
#########################

report_policy -verbose -skip_empty_summary_status -compat -output mrdc.rpt ALL

file mkdir ../REPORT/

foreach mod $modules {
  # Find unique modules
  set umods [get_all_modules $mod]
  set umods_length [llength $umods]

  puts "Generating Policy Reports for $mod ( $umods ) ..."

  if {$umods_length == 1} {
    # Just report as original module
    report_policy -verbose -skip_empty_summary_status -compat   \
      -output ../REPORT/mrdc.$mod.rpt -module [lindex $umods 0] \
      {NEW TO_BE_FIXED DEFERRED}
  } else {
    # Report file name is increamental index not uniquified module name
    set idx 0
    foreach umod $umods {
      report_policy -verbose -skip_empty_summary_status -compat \
        -output ../REPORT/mrdc.$mod_$idx.rpt -module $umod      \
        {NEW TO_BE_FIXED DEFERRED}
      incr idx 1
    }
  }
}

# Report waived in a separate file
report_policy -verbose -skip_empty_summary_status -compat -output ../REPORT/mrdc.new.rpt {NEW}
report_policy -verbose -skip_empty_summary_status -compat -output ../REPORT/mrdc.waived.rpt {WAIVED}

# report_messages -output mrdc.rpt
