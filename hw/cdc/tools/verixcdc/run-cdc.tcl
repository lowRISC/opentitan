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
set USER_ENV_FILE      [get_env_var "USER_ENV_FILE"]
set AST_LIB            [get_env_var "AST_LIB"]

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
set ri_max_total_range_bits 20
set ri_prefer_liberty true

############################
## Apply Liberty File ##

read_liberty $AST_LIB -db_dir ./RI_compiled_libs/verix_libs
############################

#########################
## Analyze & Elaborate ##
#########################

if {$DEFINE != ""} {
  analyze -sverilog +define+${DEFINE}  -f ${SV_FLIST}
} else {
  analyze -sverilog   -f ${SV_FLIST}
}

# TODO(#13197): two flops are accessing the same memory cells
# prim_generic_ram_2p is not recognized as a CDC module by the tool
# So, it's black-boxed while waiting for a tool patch
if {$PARAMS != ""} {
  elaborate -params "$PARAMS" $DUT -black_box prim_generic_ram_2p
} else {
  elaborate $DUT -black_box prim_generic_ram_2p
}
#################################
## Define Common Synchronizers ##
#################################

# Glitch Free Mux
# WARNING!!! prim_clock_mux2 is not a glitch free mux
#set_user_glitch_free_muxes -name opentitan_clock_mux prim_generic_clock_mux2
#set_user_glitch_free_muxes -name opentitan_glitchfree_mux prim_generic_clock_glitchfree_mux2

# 2FF synchronizer.
# TODO: Process dependent module name later
set prim_2ff_modules {}

# Find every derivated modules from 2FF synchronizer
foreach mod [get_all_modules prim_flop_2sync] {
  lappend prim_2ff_modules $mod
  puts "Adding to list prim_2ff_modules: $mod"
}

set_user_cntl_synchronizer -name opentitan_2ff $prim_2ff_modules

# Pulse synchronizer

# Req/Ack synchronizer


# TODO: These should not be hardcoded here, instead, we need to create another variable called CDC_CONSTRAINT
# where a top could specifically suppli this
#
# The following paths ignore data integrity errors that are directly generated on the async fifo data
# The path is as follows: asycn_fifo.rdata_o -> data integrity check -> a_valid
# There are two such paths: One path is a the error pin directly into ibex, and the other is ibex's internal check
set async_fifo_data [get_pins -of_objects [get_cells -hier * -filter {ref_name == prim_fifo_async}] -filter {name =~ rdata_o*}]
set_ignore_cdc_paths -name async_fifo_to_ibex_data_err -through_signal $async_fifo_data -through_signal [get_pins top_earlgrey/u_rv_core_ibex/u_core/data_err_i]
set_ignore_cdc_paths -name async_fifo_to_ibex_ecc_err -through_signal $async_fifo_data -through_signal [get_pins top_earlgrey/u_rv_core_ibex/u_core/u_ibex_core/load_store_unit_i/load_resp_intg_err_o]

# these paths are to ignore new errors due to recent design change in #15766
# input rspfifo rd_port is qualified so we can assume its output on main_clk domain
set_ignore_cdc_paths -name async_fifo_to_ibex -through_signal $async_fifo_data -through_signal [get_pins top_earlgrey/u_rv_core_ibex/u_core/data_rdata_i]
set_ignore_cdc_paths -name async_fifo_to_ibex -through_signal $async_fifo_data -through_signal [get_pins top_earlgrey/u_rv_core_ibex/u_core/data_rdata_intg_i]

# The following paths ignore valid qualification using the response data
# In the socketm1 module, the returned ID is used to pick which of the original source made the request
# CDC sees this as rdata directly affecting the control, but the control signal should already dictate whether the rdata is safe to use.
set_ignore_cdc_paths -name async_fifo_to_ibex_ivalid -through_signal $async_fifo_data -through_signal [get_pins top_earlgrey/u_rv_core_ibex/u_core/instr_rvalid_i]
set_ignore_cdc_paths -name async_fifo_to_ibex_dvalid -through_signal $async_fifo_data -through_signal [get_pins top_earlgrey/u_rv_core_ibex/u_core/data_rvalid_i]
#set_ignore_cdc_paths -name async_fifo_to_sync_fifo -through_signal $async_fifo_data -through_signal [get_pins top_earlgrey.u_xbar_main.u_s1n_57.fifo_h.rspfifo.gen_normal_fifo/data_rvalid_i]
#set_ignore_cdc_paths  -from_signal {SPI_DEV_D0} -to_signal {SPI_HOST_D0}
#set_ignore_cdc_paths  -from_signal {SPI_DEV_D1} -to_signal {SPI_HOST_D1}
#set_ignore_cdc_paths  -from_signal {SPI_DEV_D2} -to_signal {SPI_HOST_D2}
#set_ignore_cdc_paths  -from_signal {SPI_DEV_D3} -to_signal {SPI_HOST_D3}
#set_ignore_cdc_paths  -from_signal {SPI_DEV_CS_L} -to_signal {SPI_HOST_CS_L}

# CDC between tlul_fifo_async and regs : ignored
set tlul_async_data [get_pins -of_objects [get_cells -hier * -filter {ref_name == tlul_fifo_async}] -filter {name =~ tl_d_o*}]
set_ignore_cdc_paths -name tlul_async_fifo_err -through_signal $tlul_async_data -through_signal [get_pins {top_earlgrey/*/u_reg/u_io_*meas_ctrl_shadowed_cdc/src_we_i}]
#########################
## Apply Constraints   ##
#########################

#read_sdc $CONSTRAINT
create_scenario {sdc env}
current_scenario sdc
read_sdc  $CONSTRAINT  -output_env constraints.sdc.env
current_scenario env
read_env constraints.sdc.env
touch $USER_ENV_FILE
read_env $USER_ENV_FILE

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

#analyze_intent
analyze_intent -disable_auto_intent_generation
report_policy {ALL} -output setup_checks.rpt -compat -verbose

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
  edn
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
  # Find unique modules
  set umods [get_all_modules $mod]
  set umods_length [llength $umods]

  puts "Generating Policy Reports for $mod ( $umods ) ..."

  if {$umods_length == 1} {
    # Just report as original module
    report_policy -verbose -skip_empty_summary_status -compat   \
      -output ../REPORT/vcdc.$mod.rpt -module [lindex $umods 0] \
      {NEW TO_BE_FIXED DEFERRED}
  } else {
    # Report file name is increamental index not uniquified module name
    set idx 0
    foreach umod $umods {
      report_policy -verbose -skip_empty_summary_status -compat \
        -output ../REPORT/vcdc.$mod_$idx.rpt -module $umod      \
        {NEW TO_BE_FIXED DEFERRED}
      incr idx 1
    }
  }
}

# Report waived in a separate file
report_policy -verbose -skip_empty_summary_status -compat -output ../REPORT/vcdc.new.rpt {NEW}
report_policy -verbose -skip_empty_summary_status -compat -output ../REPORT/vcdc.waived.rpt {WAIVED}

# report_messages -output verix_cdc.rpt

# Clock report
report_clock_domains -flops -output ../REPORT/clocks.flops.rpt
report_clock_matrix -output ../REPORT/clocks.matrix.rpt
