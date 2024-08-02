# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Script to run MeridianCDC analysis (specific to OpenTitan but independent of the top-level design)

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

set FOUNDRY_ROOT        ""
set SV_FLIST            [get_env_var "SV_FLIST"]
set BUILD_DIR           [get_env_var "BUILD_DIR"]
set DUT                 [get_env_var "DUT"]
set CONSTRAINT          [get_env_var "CONSTRAINT"]
set PARAMS              [get_env_var "PARAMS"]
set CDC_WAIVER_FILE     [get_env_var "CDC_WAIVER_FILE"]
set CDC_WAIVER_DIR      [file dirname $CDC_WAIVER_FILE]
set ENV_FILE            [get_env_var "ENV_FILE"]

# Used to disable some SDC constructs that are not needed by CDC.
set IS_CDC_RUN 1

# TODO(#24208): Increasing the `ri_max_total_range_bits` setting as below can help removing
# black-box expressions, but it requires > 256 GiB of RAM, which is probably not available on
# typical workstations.  We might want to enable this based on an environment variable.
# set ri_max_total_range_bits 20

# Analyze RTL code.
set DEFINE ""
if {$DEFINE != ""} {
  analyze -sverilog +define+${DEFINE} -f ${SV_FLIST}
} else {
  analyze -sverilog -f ${SV_FLIST}
}

# Black-boxing prim_clock_div, prim_clock_gating, and prim_flash because each of them has a
# tech-specific implementation, so analyzing RTL that won't be used on the chip is meaningless and
# without this black box, MeridianCDC reports conflicts between how the design drives derived clocks
# and how derived clocks are specified in the SDC.
# TODO(#24208): ast_clks_byp should not be black-boxed, however.
set BLACK_BOX_MODULES [list \
  ast_clks_byp \
  prim_clock_div \
  prim_clock_gating \
  prim_flash \
]

# Elaborate design.
if {$PARAMS != ""} {
  elaborate -params "$PARAMS" -black_box $BLACK_BOX_MODULES $DUT
} else {
  elaborate -black_box $BLACK_BOX_MODULES $DUT
}

# Define clock and reset synchronizer modules.
set_user_cntl_synchronizer -name ot_cntl_synchronizer prim_flop_2sync
set_user_reset_synchronizer -name ot_reset_synchronizer prim_rst_sync

# Create and load ENV file from SDC.
create_scenario { sdc env }
set envs env_from_public_sdc.env
read_sdc -scenario sdc -output_env $envs $CONSTRAINT
current_scenario env
read_env $envs

# Create and load OpenTitan generic ENV file.
set OT_ENV_FILE tmp.ot.env
catch {rm $OT_ENV_FILE}
set outfile [open $OT_ENV_FILE w]
## For `prim_fifo_async`, derive clock domain of `rdata_o` from `rvalid_o`.
puts $outfile "set_data_clock_domain rdata_o -module prim_fifo_async -derived_from rvalid_o"
close $outfile
read_env $OT_ENV_FILE

# Load design-specific ENV file.
touch $ENV_FILE
read_env $ENV_FILE

# Analyze the intents of the design.
analyze_intent

# Create directory for reports (if it doesn't exist already).
set REPORT_DIR reports
file mkdir $REPORT_DIR

# Report setup check results.
report_policy {ALL} -verbose -output $REPORT_DIR/setup_checks.rpt

# Run CDC verification.
verify_cdc

# Load CDC waiver file.
if {[string length $CDC_WAIVER_FILE] != 0} {
  source $CDC_WAIVER_FILE
}

# Report CDC results.
report_policy {ALL} -skip_empty_summary_status -verbose -output $REPORT_DIR/cdc.rpt
report_policy {NEW} -skip_empty_summary_status -verbose -output $REPORT_DIR/cdc.new.rpt
report_policy {WAIVED} -skip_empty_summary_status -verbose -output $REPORT_DIR/cdc.waived.rpt

# Report clock domains.
report_clock_domains -flops -output $REPORT_DIR/clocks.flops.rpt
report_clock_matrix -output $REPORT_DIR/clocks.matrix.rpt
