# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

proc setup_path_groups {input_list output_list path_group_list_name} {
  upvar $path_group_list_name path_group_list

  foreach output $output_list {
    set output_name [lindex $output 0]
    set output_ports [get_ports $output_name]
    set path_group_name "x2out_${output_name}"
    group_path -name $path_group_name -to $output_ports
    lappend path_group_list $path_group_name
  }

  foreach input $input_list {
    set input_name [lindex $input 0]
    set input_ports [get_ports $input_name]
    set path_group_name "in2x_${input_name}"
    group_path -name $path_group_name -from $input_ports
    lappend path_group_list $path_group_name
  }

  global lr_synth_flop_in_pin
  global lr_synth_flop_out_pin

  set flops_in [get_pins $lr_synth_flop_in_pin]
  set flops_out [get_pins $lr_synth_flop_out_pin]

  group_path -name "reg2reg" -to $flops_in -from $flops_out
  lappend path_group_list "reg2reg"
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

