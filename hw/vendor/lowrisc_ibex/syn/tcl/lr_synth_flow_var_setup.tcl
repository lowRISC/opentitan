# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

puts "=================== Flow Vars ==================="

set_flow_var cell_library_path "cmos_cells.lib" "Path to cell library"
set_flow_var top_module "ibex_core" "top module"
set_flow_var out_dir "syn_out" "Output directory for synthesis"
set_flow_var pre_map_out "./${lr_synth_out_dir}/generated/${lr_synth_top_module}.pre_map.v" "Pre-mapping netlist out"
set_flow_var netlist_out "./${lr_synth_out_dir}/generated/${lr_synth_top_module}_netlist.v" "netlist out"
set_flow_var config_file "${lr_synth_top_module}_lr_synth_conf.tcl" "Synth config file"
set_flow_var rpt_out "./${lr_synth_out_dir}/reports" "Report output directory"
set_flow_bool_var flatten 1 "flatten"
set_flow_bool_var timing_run 0 "timing run"
set_flow_bool_var ibex_branch_target_alu 0 "Enable branch target ALU in Ibex"
set_flow_bool_var ibex_writeback_stage 0 "Enable writeback stage in Ibex"
set_flow_var ibex_bitmanip 0 "Bitmanip extenion setting for Ibex (see ibex_pkg::rv32b_e for permitted values. Enum names are not supported in Yosys.)"
set_flow_var ibex_multiplier 2 "Multiplier extension setting for Ibex (see ibex_pkg::rv32m_e for permitted values. Enum names are not supported in Yosys.)"
set_flow_var ibex_regfile 2 "Register file implementation selection for Ibex (see ibex_pkg::regfile_e for permitted values. Enum names are not supported in Yosys.)"

source $lr_synth_config_file

if { $lr_synth_timing_run } {
  set_flow_var cell_library_name "nangate" "Name of cell library"
  #set_flow_var sdc_file "${top_module}.sdc" "SDC file"
  set_flow_var sdc_file_in "${lr_synth_top_module}.${lr_synth_cell_library_name}.sdc" "Input SDC file"
  set_flow_var abc_sdc_file_in "${lr_synth_top_module}_abc.${lr_synth_cell_library_name}.sdc" "Input SDC file for ABC"

  set sdc_file_out_default [string range $lr_synth_sdc_file_in 0 [expr [string last ".sdc" $lr_synth_sdc_file_in] - 1]]
  set sdc_file_out_default "./${lr_synth_out_dir}/generated/$sdc_file_out_default.out.sdc"
  set_flow_var sdc_file_out $sdc_file_out_default "Output SDC file"

  set sta_netlist_out_default [string range $lr_synth_netlist_out 0 [expr [string last ".v" $lr_synth_netlist_out] - 1]]
  set sta_netlist_out_default "$sta_netlist_out_default.sta.v"
  set_flow_var sta_netlist_out $sta_netlist_out_default "STA netlist out"
  set_flow_var sta_paths_per_group 1000 "STA paths reported per group"
  set_flow_var sta_overall_paths 1000 "STA paths reported in overall report"
  puts "clock period: $lr_synth_clk_period ps"

  if { $lr_synth_abc_clk_uprate > $lr_synth_clk_period } {
    puts "WARNING: abc_clk_uprate must be less than clk_period otherwise ABC will be given a negative clk period"
  }

}

puts "================================================="
