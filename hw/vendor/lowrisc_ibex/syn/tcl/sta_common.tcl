# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

source ./tcl/flow_utils.tcl
source ./tcl/lr_synth_flow_var_setup.tcl

source ./tcl/sta_utils.tcl

print_lr_synth_banner
print_opensta_banner

read_liberty $lr_synth_cell_library_path
read_verilog $lr_synth_sta_netlist_out
link_design $lr_synth_top_module

read_sdc $lr_synth_sdc_file_out

