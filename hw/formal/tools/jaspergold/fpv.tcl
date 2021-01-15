# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# clear previous settings
clear -all

# We use parameter instead of localparam in packages to allow redefinition
# at elaboration time.
# Disabling the warning
# "parameter declared inside package XXX shall be treated as localparam".
set_message -disable VERI-2418

if {$env(COV) == 1} {
  check_cov -init -model {branch statement functional} \
  -enable_prove_based_proof_core
}
set_task_compile_time_limit 1000s
set_property_compile_time_limit 1000s

#-------------------------------------------------------------------------
# read design
#-------------------------------------------------------------------------

# only one scr file exists in this folder
analyze -sv09                 \
  +define+FPV_ON              \
  -f [glob *.scr]

elaborate -bbox_a 4320 -top $env(FPV_TOP) -enable_sva_isunknown

#-------------------------------------------------------------------------
# specify clock(s) and reset(s)
#-------------------------------------------------------------------------

# select primary clock and reset condition (use ! for active-low reset)
# note: -both_edges is needed below because the TL-UL protocol checker
# tlul_assert.sv operates on the negedge clock
# even clock this sampled at both_edges, input should only change at posedge clock cycle
# TODO: create each FPV_TOP's individual config file

if {$env(FPV_TOP) == "rv_dm"} {
  clock clk_i -both_edges
  clock jtag_req_i.tck
  clock -rate {testmode_i, unavailable_i, tl_d_i, tl_h_i} clk_i
  clock -rate {jtag_req_i.tms, jtag_req_i.tdi} jtag_req_i.tck
  reset -expr {!rst_ni !jtag_req_i.trst_n}

} elseif {$env(FPV_TOP) == "spi_device"} {
  clock clk_i -both_edges
  clock cio_sck_i
  clock -rate {scanmode_i, tl_i} clk_i
  clock -rate {cio_csb_i, cio_sdi_i} cio_sck_i
  reset -expr {!rst_ni cio_csb_i}

} elseif {$env(FPV_TOP) == "usbuart"} {
  clock clk_i -both_edges
  clock clk_usb_48mhz_i
  clock -rate {tl_i, usb_state_debug_i} clk_i
  clock -rate {cio_usb_dp_i, cio_usb_dn_i, cio_usb_sense_i} clk_usb_48mhz_i
  reset -expr {!rst_ni !rst_usb_48mhz_ni}

} elseif {$env(FPV_TOP) == "usbdev"} {
  clock clk_i -both_edges
  clock clk_aon_i
  clock clk_usb_48mhz_i
  clock -rate {tl_i} clk_i
  clock -rate {cio_d_i, cio_dp_i, cio_dn_i, cio_sense_i} clk_usb_48mhz_i
  reset -expr {!rst_ni !rst_aon_ni !rst_usb_48mhz_ni}

  # top_earlgrey is mainly used for connectivity test
} elseif {$env(FPV_TOP) == "top_earlgrey"} {
  clock clk_i -both_edges
  clock jtag_tck_i
  # TODO: check this once pinmux/padring is updated
  clock -rate -default clk_i
  reset -expr {!rst_ni !jtag_trst_ni}

# TODO: work with the block owner and re-define FPV checkings for xbar
# } elseif {$env(FPV_TOP) == "xbar_main"} {
#   clock clk_main_i -both_edges
#   reset -expr {!rst_main_ni}

} else {
  clock clk_i -both_edges
  reset -expr {!rst_ni}
  clock -rate -default clk_i
}

# use counter abstractions to reduce the run time:
# alert_handler ping_timer: timer to count until reaches ping threshold
# hmac sha2: does not check any calculation results, so 64 rounds of calculation can be abstracted
if {$env(FPV_TOP) == "alert_handler"} {
  abstract -counter -env i_ping_timer.cnt_q

} elseif {$env(FPV_TOP) == "hmac"} {
  abstract -counter -env u_sha2.round
  # disable these assertions because they are unreachable when the fifo is WO
  assert -disable {*hmac.u_tlul_adapter.u_*fifo.*.depthShallNotExceedParamDepth}
  assert -disable {*hmac.u_tlul_adapter.u_*fifo.DataKnown_A}
  assert -disable {*hmac.u_tlul_adapter.rvalidHighReqFifoEmpty}
  assert -disable {*hmac.u_tlul_adapter.rvalidHighWhenRspFifoFull}

} elseif {$env(FPV_TOP) == "flash_ctrl"} {
  # disable these assertions because they are unreachable when the fifo is WO
  assert -disable {*flash_ctrl.u_to_prog_fifo.u_*fifo.depthShallNotExceedParamDepth}
  assert -disable {*flash_ctrl.u_to_prog_fifo.u_*fifo.DataKnown_A}
  assert -disable {*flash_ctrl.u_to_prog_fifo.rvalidHighReqFifoEmpty}
  assert -disable {*flash_ctrl.u_to_prog_fifo.rvalidHighWhenRspFifoFull}
}

#-------------------------------------------------------------------------
# assume properties for inputs
#-------------------------------------------------------------------------

# Notes on above regular expressions: ^ indicates the beginning of the string;
# \w* includes all letters a-z, A-Z, and the underscore, but not the period.
# And \. is for period (with escape). These regular expressions make sure that
# the assume only applies to module_name.tlul_assert_*, but not to
# module_name.submodule.tlul_assert_*

# For sram2tlul, input tl_i.a_ready is constrained by below asssertion
assume -from_assert -remove_original {sram2tlul.validNotReady*}

# Input scanmode_i should not be X
assume -from_assert -remove_original -regexp {^\w*\.scanmodeKnown}

# TODO: If scanmode is set to 0, then JasperGold errors out complaining
# about combo loops, which should be debugged further. For now, below
# lines work around this issue
if {$env(FPV_TOP) == "top_earlgrey"} {
  assume {scanmode_i == 1}
}

# run once to check if assumptions have any conflict
if {[info exists ::env(CHECK)]} {
  if {$env(CHECK)} {
    check_assumptions -conflict
    check_assumptions -live
    check_assumptions -dead_end
  }
}

#-------------------------------------------------------------------------
# configure proofgrid
#-------------------------------------------------------------------------

set_proofgrid_per_engine_max_local_jobs 2

# Uncomment below 2 lines when using LSF:
# set_proofgrid_mode lsf
# set_proofgrid_per_engine_max_jobs 16

#-------------------------------------------------------------------------
# prove all assertions & report
#-------------------------------------------------------------------------

# time limit set to 2 hours
get_reset_info -x_value -with_reset_pin
prove -all -time_limit 2h
report

#-------------------------------------------------------------------------
# check coverage and report
#-------------------------------------------------------------------------

if {$env(COV) == 1} {
  check_cov -measure -time_limit 2h
  check_cov -report -force -exclude { reset waived }
  check_cov -report -type all -no_return -report_file cover.html \
      -html -force -exclude { reset waived }
}
