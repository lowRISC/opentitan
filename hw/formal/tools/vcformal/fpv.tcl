# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

#-------------------------------------------------------------------------
# Extract bind module information
#-------------------------------------------------------------------------

# Read filelist
set f [open [glob *.scr]]
set lines [split [read $f] \n]
close $f
#echo $lines

# Check if filelist contains "_bind"
set matches [lsearch -all -inline -glob $lines *_bind*]
#echo $matches
set lm [llength $matches]
#echo $lm

if { $lm == 0 } {
  # No bind file
  set bind_exist 0
  set bind_module_name ""
} elseif { $lm == 1 } {
  # Read bind file
  set f2 [open $matches]
  set lines [split [read $f2] \n]
  close $f2
#  echo $lines
  # Check if file contains "module"
  set module_line [lsearch -all -inline -glob $lines *module*]
#  echo $module_line
  set lml [llength $module_line]
#  echo $lml
  if { $lml == 2 } {
    # Pair module-endmodule found
    set bind_exist 1
    set bind_module_name [string trimright [lindex [regexp -all -inline {\S+} [lindex $module_line 0] ] 1] ";"]
#    echo $bind_module_name
  } else {
    # Only two instances of "module" expected --> Should not come here --> Ignore bind
    set bind_exist -2
    set bind_module_name "err-module-name"
  }
} else {
  # More than one bind file --> Should not come here --> Ignore bind
  set bind_exist -1
  set bind_module_name "err-bind-detect"
}
echo "${env(DUT_TOP)}, ${bind_exist} , ${bind_module_name}, -, -, -"

#-------------------------------------------------------------------------
# Set up VC Formal
#-------------------------------------------------------------------------
# Set App mode
set_fml_appmode FPV

# Set message levels for errors, warnings, etc.
source $env(COMMON_MSG_TCL_PATH)
source $env(COMMON_RPT_TCL_PATH)

#-------------------------------------------------------------------------
# Read and compile design
#-------------------------------------------------------------------------
# Do not define SYNTHESIS macro by default
set_app_var define_synthesis_macro false

# Analyze design files
analyze -format sverilog -vcs "+define+FPV_ON -assert svaext \
  -f [glob *.scr]"

# Compile design with or without bind module
if {$bind_exist == 1} {
  elaborate -sva $env(DUT_TOP) -vcs "$bind_module_name"
} else {
  elaborate -sva $env(DUT_TOP)
}

# TODO: CHECK IF ELABORATION COMPLETED SUCCESSFULLY?

# TODO: DO WE KEEP THIS?
set num_ast [ sizeof_collection [ get_props -usage assert ] ]
set num_asm [ sizeof_collection [ get_props -usage assume ] ]
set num_cov [ sizeof_collection [ get_props -usage cover ] ]
echo "${env(DUT_TOP)}, ${bind_exist} , ${bind_module_name}, ${num_ast},  ${num_asm},  ${num_cov}"

# Blackbox arrays of size 4320 and above
set_abstractions -construct {array=4320}
report_abstractions -list

#-------------------------------------------------------------------------
# Specify clock(s), reset(s), and input/clock associations
#-------------------------------------------------------------------------

# Specify clocks and reset conditions (use "-sense low" for active-low reset)
# Note: The TL-UL protocol checker tlul_assert.sv operates on the negedge clock;
#   VC Formal will use system clock twice as fast for verification thus requiring
#   input/clock associations
#
# TODO: Create each DUT_TOP's individual config file with clocks, resets,
#   input/clock associations, and constraints
# (How is it going to look like? Json file?)

if {$env(DUT_TOP) == "aes"} {
  create_clock clk_i -period 100
  create_reset rst_ni -sense low
  create_clock clk_edn_i -period 100
  create_reset rst_edn_ni -sense low
} elseif {$env(DUT_TOP) == "alert_handler"} {
  create_clock clk_i -period 100
  create_reset rst_ni -sense low
  create_clock clk_edn_i -period 100
  create_reset rst_edn_ni -sense low
} elseif {$env(DUT_TOP) == "flash_ctrl"} {
  create_clock clk_i -period 100
  create_reset rst_ni -sense low
  create_clock clk_otp_i -period 100
  create_reset rst_otp_ni -sense low
} elseif {$env(DUT_TOP) == "keymgr"} {
  create_clock clk_i -period 100
  create_reset rst_ni -sense low
  create_clock clk_edn_i -period 100
  create_reset rst_edn_ni -sense low
} elseif {$env(DUT_TOP) == "lc_ctrl"} {
  create_clock clk_i -period 100
  create_reset rst_ni -sense low
  create_clock clk_kmac_i -period 100
  create_reset rst_kmac_ni -sense low
  create_clock jtag_i.tck -period 100
  create_reset jtag_i.trst_n -sense low
  create_reset scan_rst_ni -sense low
} elseif {$env(DUT_TOP) == "otp_ctrl"} {
  create_clock clk_i -period 100
  create_reset rst_ni -sense low
  create_clock clk_edn_i -period 100
  create_reset rst_edn_ni -sense low
} elseif {$env(DUT_TOP) == "otbn"} {
  create_clock clk_i -period 100
  create_reset rst_ni -sense low
  create_clock clk_edn_i -period 100
  create_reset rst_edn_ni -sense low
} elseif {$env(DUT_TOP) == "rv_dm"} {
  create_clock clk_i -period 100
  create_reset rst_ni -sense low
  set_change_at -clock clk_i -posedge {testmode_i unavailable_i tl_d_i tl_h_i}
  create_clock jtag_req_i.tck -period 100
  create_reset jtag_req_i.trst_n -sense low
  set_change_at -clock jtag_req_i.tck -posedge {jtag_req_i.tms jtag_req_i.tdi}
  create_reset scan_rst_ni -sense low
} elseif {$env(DUT_TOP) == "spi_device"} {
  create_clock clk_i -period 100
  create_reset rst_ni -sense low
  set_change_at -clock clk_i -posedge {scanmode_i tl_i}
  create_clock cio_sck_i -period 100
  create_reset cio_csb_i -sense high
  set_change_at -clock cio_sck_i -posedge {cio_csb_i cio_sd_i}
  create_clock scan_clk_i -period 100
  create_reset scan_rst_ni -sense low
} elseif {$env(DUT_TOP) == "sram_ctrl"} {
  create_clock clk_i -period 100
  create_reset rst_ni -sense low
  create_clock clk_otp_i -period 100
  create_reset rst_otp_ni -sense low
} elseif {$env(DUT_TOP) == "usbdev"} {
  create_clock clk_i -period 100
  create_reset rst_ni -sense low
  set_change_at -clock clk_i -posedge {usb_state_debug_i tl_i}
  create_clock clk_aon_i -period 100
  create_reset rst_aon_ni -sense low
  create_clock clk_usb_48mhz_i -period 100
  create_reset rst_usb_48mhz_ni -sense low
  set_change_at -clock clk_usb_48mhz_i -posedge {cio_d_i cio_dp_i cio_dn_i cio_sense_i}
} elseif {$env(DUT_TOP) == "xbar_main"} {
  # TO CHECK WHEN MODULE IS ENABLED
  create_clock clk_main_i -period 100
  create_reset rst_main_ni -sense low
} elseif {$env(DUT_TOP) == "top_earlgrey"} {
  # TO CHECK WHEN MODULE IS ENABLED
  create_clock clk_i -period 100
  create_clock jtag_tck_i -period 100
  create_reset rst_ni -sense low
  create_reset jtag_trst_ni -sense low
} else {
  # General setup
  create_clock clk_i -period 100
  create_reset rst_ni -sense low
  set_change_at -clock clk_i -posedge -default
}

# TODO: DO WE KEEP THIS?
# Check for potential missing clock(s) and reset(s)
echo "$env(DUT_TOP) POST-SETUP Missing Clocks: "
foreach_in_collection lmclk [get_fv_complexity -filter mclk] {
  set cname [get_attribute $lmclk -name name];
  echo "  Name: $cname "
}
echo "$env(DUT_TOP) POST-SETUP Missing Resets: "
foreach_in_collection lmrst [get_fv_complexity -filter mrst] {
  set rname [get_attribute $lmrst -name name];
  echo "  Name: $rname "
}

#-------------------------------------------------------------------------
# Set up assumptions/properties and abstractions for verification
#-------------------------------------------------------------------------
# - Add counter abstract counter abstractions to reduce runtime
# - Disable specific assertions
# - Use assertion as assumption

if {$env(DUT_TOP) == "alert_handler"} {
  # alert_handler ping_timer: timer to count until reaches ping threshold
  set_abstractions -construct {count=1} -using keyvals -filter {name == i_ping_timer.cnt_q}
}
if {$env(DUT_TOP) == "hmac"} {
  # hmac sha2: does not check any calculation results, so 64 rounds of calculation can be abstracted
  set_abstractions -construct {count=1} -using keyvals -filter {name == u_sha2.round}
  # Disable these assertions because they are unreachable when the fifo is WO
  fvdisable -usage assert {*hmac.u_tlul_adapter.u_*fifo.*.depthShallNotExceedParamDepth}
  fvdisable -usage assert {*hmac.u_tlul_adapter.u_*fifo.DataKnown_A}
  fvdisable -usage assert {*hmac.u_tlul_adapter.rvalidHighReqFifoEmpty}
  fvdisable -usage assert {*hmac.u_tlul_adapter.rvalidHighWhenRspFifoFull}
}
if {$env(DUT_TOP) == "flash_ctrl"} {
  # Disable these assertions because they are unreachable when the fifo is WO
  fvdisable -usage assert {*flash_ctrl.u_to_prog_fifo.u_*fifo.depthShallNotExceedParamDepth}
  fvdisable -usage assert {*flash_ctrl.u_to_prog_fifo.u_*fifo.DataKnown_A}
  fvdisable -usage assert {*flash_ctrl.u_to_prog_fifo.rvalidHighReqFifoEmpty}
  fvdisable -usage assert {*flash_ctrl.u_to_prog_fifo.rvalidHighWhenRspFifoFull}
}

# For sram2tlul, input tl_i.a_ready is constrained by below assertion
fvassume {sram2tlul.validNotReady*}

# Input scanmode_i should not be X
fvassume -regexp {^\w*\.scanmodeKnown}
# Notes on above regular expressions: ^ indicates the beginning of the string;
# \w* includes all letters a-z, A-Z, and the underscore, but not the period.
# And \. is for period (with escape). These regular expressions make sure that
# the assume only applies to module_name.tlul_assert_*, but not to
# module_name.submodule.tlul_assert_*

# TODO: What do we do about this?
#
# TODO: If scanmode is set to 0, then JasperGold errors out complaining
# about combo loops, which should be debugged further. For now, below
# lines work around this issue
#if {$env(DUT_TOP) == "top_earlgrey"} {
#  assume {scanmode_i == 1}
#}
if {$env(DUT_TOP) == "top_earlgrey"} {
  set_constant scanmode_i -value 1'b0 -global
}

#-------------------------------------------------------------------------
# Initialize design
#-------------------------------------------------------------------------

# Run design initialization
sim_run -stable
sim_save_reset

# TODO: DO WE REPORT OR DO ANYTHING ABOUT UNINITIALIZED REGISTERS?

#-------------------------------------------------------------------------
# Configure proof setup
#-------------------------------------------------------------------------
# Use command set_grid_usage to configure grid and workers options
# Option "-type [SGE|LSF|RSH|SSH|RTDA]=<# of workers>" specifies the type of grid and the numbers of workers
# Option "-control {<submission commands>}" specifies the exact qsub/bsub string to use for accessing grid resources
# Example: set_grid_usage -type SGE=12 -control { qsub -P <machine name> }
set_grid_usage -type RSH=12

# Set max time limit (default: 12H)
set_fml_var fml_max_time 2H

# Set max mem limit (default: 8GB)
set_fml_var fml_max_mem 8GB

#-------------------------------------------------------------------------
# Check setup and properties
#-------------------------------------------------------------------------

# Check formal verification setup
# Note: It is recommended to run check_fv_setup at least once to check for potential design and setup issues
check_fv_setup -block
report_fv_setup -list

# Check properties
check_fv -block
#report_fv  > ../../../$env(DUT_TOP)_results.txt
#report_fv -xml > ../../../$env(DUT_TOP)_results.xml
report_fv -list
vcf_dvsim_report

#-------------------------------------------------------------------------
# Coverage
#-------------------------------------------------------------------------

# TODO
