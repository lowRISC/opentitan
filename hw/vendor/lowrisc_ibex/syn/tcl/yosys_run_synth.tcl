# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

source ./tcl/yosys_common.tcl

if { $lr_synth_flatten } {
  set flatten_opt "-flatten"
} else {
  set flatten_opt ""
}

if { $lr_synth_timing_run } {
  write_sdc_out $lr_synth_sdc_file_in $lr_synth_sdc_file_out
}

yosys "read -sv ./rtl/prim_clock_gating.v $lr_synth_out_dir/generated/*.v"
yosys "synth $flatten_opt -top $lr_synth_top_module"
yosys "opt -purge"

yosys "write_verilog $lr_synth_pre_map_out"

yosys "dfflibmap -liberty $lr_synth_cell_library_path"
yosys "opt"

if { $lr_synth_timing_run } {
  yosys "abc -liberty $lr_synth_cell_library_path -constr $lr_synth_sdc_file_out -D $lr_synth_clk_period"
} else {
  yosys "abc -liberty $lr_synth_cell_library_path"
}

yosys "clean"
yosys "write_verilog $lr_synth_netlist_out"

if { $lr_synth_timing_run } {
  # Produce netlist that OpenSTA can use
  yosys "setundef -zero"
  yosys "splitnets"

  yosys "write_verilog -noattr -noexpr -nohex -nodec $lr_synth_sta_netlist_out"
}

yosys "check"
yosys "log ======== Yosys Stat Report ========"
yosys "tee -o $lr_synth_out_dir/reports/area.rpt stat -liberty $lr_synth_cell_library_path"
yosys "log ====== End Yosys Stat Report ======"

