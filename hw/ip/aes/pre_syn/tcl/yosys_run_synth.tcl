# Copyright lowRISC contributors (OpenTitan project).
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

yosys "read_verilog -sv $lr_synth_out_dir/generated/*.v"

# Set top-module parameters.
# When synthesizing a sub module such as an individual S-Box, some parameters might not exist.
# You can use
#    yosys "chparam -list $lr_synth_top_module"
# To print the available parameters.
if { $lr_synth_top_module != "aes_sbox" && $lr_synth_top_module != "aes_sub_bytes" && $lr_synth_top_module != "aes_reduced_round"} {
  yosys "chparam -set AES192Enable $lr_synth_aes_192_enable $lr_synth_top_module"
  yosys "chparam -set SecMasking $lr_synth_sec_masking $lr_synth_top_module"
}
yosys "chparam -set SecSBoxImpl $lr_synth_sec_s_box_impl $lr_synth_top_module"

# Remap Xilinx Vivado "dont_touch" attributes to Yosys "keep" attributes.
yosys "attrmap -tocase keep -imap dont_touch=\"yes\" keep=1 -imap dont_touch=\"no\" keep=0 -remove keep=0"

# Place keep_hierarchy contraints on relevant modules to prevent aggressive synthesis optimzations
# across the boundaries of these modules.
yosys "hierarchy -check -top $lr_synth_top_module"
yosys "setattr -mod -set keep_hierarchy 1 *prim_xilinx*"
yosys "setattr -mod -set keep_hierarchy 1 *aes_*_fsm_p*"
yosys "setattr -mod -set keep_hierarchy 1 *aes_*_fsm_n*"
yosys "setattr -mod -set keep_hierarchy 1 *aes_sel_buf_chk*"

# Synthesize.
yosys "synth -nofsm $flatten_opt -top $lr_synth_top_module"
yosys "opt -purge"

yosys "write_verilog $lr_synth_pre_map_out"

# Remove keep_hierarchy constraints before writing out the netlist for Alma as it doesn't like
# these constraints.
yosys "setattr -mod -set keep_hierarchy 0 *prim_xilinx*"
yosys "setattr -mod -set keep_hierarchy 0 *aes_*_fsm_p*"
yosys "setattr -mod -set keep_hierarchy 0 *aes_*_fsm_n*"
yosys "setattr -mod -set keep_hierarchy 0 *aes_sel_buf_chk*"

yosys "write_verilog $lr_synth_alma_out"

# Re-add keep_hierarchy constraints for further synthesis steps.
yosys "setattr -mod -set keep_hierarchy 1 *prim_xilinx*"
yosys "setattr -mod -set keep_hierarchy 1 *aes_*_fsm_p*"
yosys "setattr -mod -set keep_hierarchy 1 *aes_*_fsm_n*"
yosys "setattr -mod -set keep_hierarchy 1 *aes_sel_buf_chk*"

yosys "dfflibmap -liberty $lr_synth_cell_library_path"
yosys "opt"

set yosys_abc_clk_period [expr $lr_synth_clk_period - $lr_synth_abc_clk_uprate]

if { $lr_synth_timing_run } {
  yosys "abc -liberty $lr_synth_cell_library_path -constr $lr_synth_abc_sdc_file_in -D $yosys_abc_clk_period"
} else {
  yosys "abc -liberty $lr_synth_cell_library_path"
}

# Remove keep_hierarchy constraints before the final flattening step. We're done optimizing.
yosys "setattr -mod -set keep_hierarchy 0 *prim_xilinx*"
yosys "setattr -mod -set keep_hierarchy 0 *aes_*_fsm_p*"
yosys "setattr -mod -set keep_hierarchy 0 *aes_*_fsm_n*"
yosys "setattr -mod -set keep_hierarchy 0 *aes_sel_buf_chk*"

# Final flattening.
if { $lr_synth_flatten } {
  yosys "flatten"
}

yosys "clean -purge"
yosys "write_verilog $lr_synth_netlist_out"

if { $lr_synth_timing_run } {
  # Produce netlist that OpenSTA can use
  yosys "setundef -zero"
  yosys "splitnets"
  yosys "clean"
  yosys "write_verilog -noattr -noexpr -nohex -nodec $lr_synth_sta_netlist_out"
}

yosys "check"
yosys "log ======== Yosys Stat Report ========"
yosys "tee -o $lr_synth_out_dir/reports/area.rpt stat -liberty $lr_synth_cell_library_path"
yosys "log ====== End Yosys Stat Report ======"
