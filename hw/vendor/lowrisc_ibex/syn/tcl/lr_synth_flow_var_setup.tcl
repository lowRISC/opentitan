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

source $lr_synth_config_file

if { $lr_synth_timing_run } {
  set_flow_var cell_library_name "nangate" "Name of cell library"
  #set_flow_var sdc_file "${top_module}.sdc" "SDC file"
  set_flow_var sdc_file_in "${lr_synth_top_module}.${lr_synth_cell_library_name}.sdc" "Input SDC file"
  set flop_in_pin_default "*/D"
  set flop_out_pin_default "*/Q"

  # STA needs to know start and end points for identifying reg2reg paths. These
  # can vary depending upon the library used
  if { [string first "nangate" $lr_synth_cell_library_name] == 0 } {
    set flop_in_pin_default "*/D"
    set flop_out_pin_default "*/CK"
  }

  set_flow_var flop_in_pin $flop_in_pin_default "In pin to flop for reg2reg path extraction"
  set_flow_var flop_out_pin $flop_out_pin_default "Out pin from flop for reg2reg path extraction"

  set sdc_file_out_default [string range $lr_synth_sdc_file_in 0 [expr [string last ".sdc" $lr_synth_sdc_file_in] - 1]]
  set sdc_file_out_default "./${lr_synth_out_dir}/generated/$sdc_file_out_default.out.sdc"
  set_flow_var sdc_file_out $sdc_file_out_default "Output SDC file"

  set sta_netlist_out_default [string range $lr_synth_netlist_out 0 [expr [string last ".v" $lr_synth_netlist_out] - 1]]
  set sta_netlist_out_default "$sta_netlist_out_default.sta.v"
  set_flow_var sta_netlist_out $sta_netlist_out_default "STA netlist out"
  set_flow_var sta_paths_per_group 100 "STA paths reported per group"
  set_flow_var sta_overall_paths 1000 "STA paths reported in overall report"
  puts "clock period: $lr_synth_clk_period ps"
}

puts "================================================="
