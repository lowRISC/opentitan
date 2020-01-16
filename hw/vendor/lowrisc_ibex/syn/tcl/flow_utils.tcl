# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

proc print_lr_synth_banner {} {
puts { _                  ______  _____  _____  _____  }
puts {| |                 | ___ \|_   _|/  ___|/  __ \ }
puts {| |  ___  __      __| |_/ /  | |  \ `--. | /  \/ }
puts {| | / _ \ \ \ /\ / /|    /   | |   `--. \| |     }
puts {| || (_) | \ V  V / | |\ \  _| |_ /\__/ /| \__/\ }
puts {|_| \___/   \_/\_/  \_| \_| \___/ \____/  \____/ }
puts {                                                 }
puts {                                                 }
puts {                            _    _               }
puts {                           | |  | |              }
puts {         ___  _   _  _ __  | |_ | |__            }
puts {        / __|| | | || '_ \ | __|| '_ \           }
puts {        \__ \| |_| || | | || |_ | | | |          }
puts {        |___/ \__, ||_| |_| \__||_| |_|          }
puts {               __/ |                             }
puts {              |___/                              }
puts {}
puts {******  o p e n   t o   t h e   c o r e  ******* }
puts {}
}

proc print_yosys_banner {} {
puts {       +---------------------------------+}
puts {       |  _   _   ___   ___  _   _  ___  |}
puts {       | | | | | / _ \ / __|| | | |/ __| |}
puts {       | | |_| || (_) |\__ \| |_| |\__ \ |}
puts {       |  \__, | \___/ |___/ \__, ||___/ |}
puts {       |   __/ |              __/ |      |}
puts {       |  |___/              |___/       |}
puts {       +---------------------------------+}
puts {}
}

proc print_opensta_banner {} {
puts {+--------------------------------------------------+}
puts {|  _____                      _____  _____   ___   |}
puts {| |  _  |                    /  ___||_   _| / _ \  |}
puts {| | | | | _ __    ___  _ __  \ `--.   | |  / /_\ \ |}
puts {| | | | || '_ \  / _ \| '_ \  `--. \  | |  |  _  | |}
puts {| \ \_/ /| |_) ||  __/| | | |/\__/ /  | |  | | | | |}
puts {|  \___/ | .__/  \___||_| |_|\____/   \_/  \_| |_/ |}
puts {|        | |                                       |}
puts {|        |_|                                       |}
puts {+--------------------------------------------------+}
puts {}
}

proc set_flow_var {var_name var_default var_friendly_name} {
  global lr_synth_flow_var_quiet

  set var_name "lr_synth_${var_name}"
  global $var_name
  set env_var_name [string toupper $var_name]

  if { [info exists ::env($env_var_name)] } {
    set $var_name $::env($env_var_name)
    puts "$var_friendly_name: $::env($env_var_name)"
  } else {
    set $var_name $var_default
    puts "$var_friendly_name: $var_default (default)"
  }
}

proc set_flow_bool_var {var_name var_default var_friendly_name} {
  global lr_synth_flow_var_quiet

  set var_name "lr_synth_${var_name}"
  global $var_name
  set env_var_name [string toupper $var_name]

  if { [info exists ::env($env_var_name)] } {
    if { $::env($env_var_name) } {
      set $var_name 1
    } else {
      set $var_name 0
    }
  } else {
    set $var_name $var_default
  }

  if { [set $var_name] } {
    puts "$var_friendly_name: Enabled"
  } else {
    puts "$var_friendly_name: Disabled"
  }
}

proc write_sdc_out {sdc_file_in sdc_file_out} {
  global lr_synth_clk_period
  global lr_synth_clk_input
  global lr_synth_outputs
  global lr_synth_inputs

  set sdc_out [open $sdc_file_out "w"]
  set sdc_in  [open $sdc_file_in "r"]

  set sdc_in_contents [read $sdc_in]
  puts $sdc_out $sdc_in_contents

  puts $sdc_out "#============ Auto-generated from config ============"

  set clk_period_ns [expr $lr_synth_clk_period / 1000.0]
  puts $sdc_out "create_clock -name $lr_synth_clk_input -period $clk_period_ns {$lr_synth_clk_input}"

  foreach output $lr_synth_outputs {
    set output_constraint [lindex $output 1]
    set output_constraint [expr (1.0 - ($output_constraint / 100.0)) * $clk_period_ns]
    puts $sdc_out "set_output_delay -clock $lr_synth_clk_input $output_constraint [lindex $output 0]"
  }

  foreach input $lr_synth_inputs {
    set input_constraint [lindex $input 1]
    set input_constraint [expr ($input_constraint / 100.0) * $clk_period_ns]
    puts $sdc_out "set_input_delay -clock $lr_synth_clk_input $input_constraint [lindex $input 0]"
  }

  close $sdc_out
  close $sdc_in
}
