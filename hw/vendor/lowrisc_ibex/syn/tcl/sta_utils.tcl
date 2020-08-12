# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

proc setup_path_groups {input_list output_list path_group_list_name} {
  upvar $path_group_list_name path_group_list

  set flops_in [all_registers -edge_triggered -data_pins]
  set flops_out [all_registers -edge_triggered -clock_pins]
  group_path -name reg2reg -from $flops_out -to $flops_in
  lappend path_group_list reg2reg

  foreach output $output_list {
    set output_name [lindex $output 0]
    lappend outputs_list [get_ports $output_name]
  }
  group_path -name reg2out -from $flops_out -to $outputs_list
  lappend path_group_list reg2out

  foreach input $input_list {
    set input_name [lindex $input 0]
    lappend inputs_list [get_ports $input_name]
  }
  group_path -name in2reg -from $inputs_list -to $flops_in
  lappend path_group_list in2reg

  group_path -name in2out -from $inputs_list -to $outputs_list
  lappend path_group_list in2out

}

proc timing_report {path_group rpt_out path_count} {
  set sta_report_out_filename "${rpt_out}.rpt"
  set sta_csv_out_filename "${rpt_out}.csv.rpt"

  puts "Reporting $path_group to $sta_report_out_filename and $sta_csv_out_filename"
  report_checks -group_count $path_count -path_group $path_group > $sta_report_out_filename

  set paths [find_timing_paths -group_count $path_count -path_group $path_group]
  set sta_csv_out [open $sta_csv_out_filename "w"]

  foreach path $paths {
    set startpoint_name [get_name [get_property $path startpoint]]
    set endpoint_name [get_name [get_property $path endpoint]]
    set slack [get_property $path slack]
    puts $sta_csv_out [format "$startpoint_name,$endpoint_name,%.4f" $slack]
  }

  close $sta_csv_out
}

