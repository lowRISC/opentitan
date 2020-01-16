# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

source ./tcl/sta_common.tcl

set overall_rpt_file "${lr_synth_rpt_out}/timing/overall"
timing_report $lr_synth_clk_input $overall_rpt_file $lr_synth_sta_overall_paths

set lr_synth_path_group_list [list]

setup_path_groups $lr_synth_inputs $lr_synth_outputs lr_synth_path_group_list

foreach path_group $lr_synth_path_group_list {
  puts $path_group
  set path_group_rpt_file "${lr_synth_rpt_out}/timing/$path_group"
  timing_report $path_group $path_group_rpt_file $lr_synth_sta_paths_per_group
}

exit

