# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# clear previous settings
clear -all

source $env(COMMON_MSG_TCL_PATH)

if {$env(COV) == 1} {
  check_cov -init -model {branch statement functional} \
  -exclude_bind_hierarchies
}

#-------------------------------------------------------------------------
# read design
#-------------------------------------------------------------------------

# only one scr file exists in this folder
analyze -sv09     \
  +define+FPV_ON  \
  -f [glob *.scr]

if {$env(DUT_TOP) == "prim_count_tb"} {
  elaborate -top $env(DUT_TOP) \
            -enable_sva_isunknown \
            -disable_auto_bbox \
            -param OutSelDnCnt $OutSelDnCnt \
            -param CntStyle $CntStyle
} else {
  elaborate -top $env(DUT_TOP) -enable_sva_isunknown -disable_auto_bbox
}

if {$env(STOPATS) ne ""} {
  stopat -env $env(STOPATS)
}

#-------------------------------------------------------------------------
# specify clock(s) and reset(s)
#-------------------------------------------------------------------------

# select primary clock and reset condition (use ! for active-low reset)
# note: -both_edges is needed below because the TL-UL protocol checker
# tlul_assert.sv operates on the negedge clock
# even clock this sampled at both_edges, input should only change at posedge clock cycle
# TODO: create each DUT_TOP's individual config file

if {$env(DUT_TOP) == "rv_dm"} {
  clock clk_i -both_edges
  clock jtag_i.tck
  clock -rate {testmode, unavailable_i, reg_tl_d_i, sba_tl_h_i} clk_i
  clock -rate {jtag_i.tms, jtag_i.tdi} jtag_i.tck
  reset -expr {!rst_ni !jtag_i.trst_n}

} elseif {$env(DUT_TOP) == "spi_device"} {
  clock clk_i -both_edges
  clock cio_sck_i
  clock -rate {scanmode_i, tl_i} clk_i
  clock -rate {cio_csb_i, cio_sd_i} cio_sck_i
  reset -expr {!rst_ni cio_csb_i}

} elseif {$env(DUT_TOP) == "sysrst_ctrl"} {
  clock clk_i -both_edges
  clock clk_aon_i
  clock -rate {tl_i} clk_i
  clock -rate {cio_ac_present_i, cio_ec_rst_l_i, cio_key0_in_i, cio_key1_in_i, cio_key2_in_i, cio_pwrb_in_i, cio_lid_open_i} clk_aon_i
  reset -expr {!rst_ni !rst_aon_ni}

} elseif {$env(DUT_TOP) == "usbuart"} {
  clock clk_i -both_edges
  clock clk_usb_48mhz_i
  clock -rate {tl_i, usb_state_debug_i} clk_i
  clock -rate {cio_usb_dp_i, cio_usb_dn_i, cio_usb_sense_i} clk_usb_48mhz_i
  reset -expr {!rst_ni !rst_usb_48mhz_ni}

} elseif {$env(DUT_TOP) == "usbdev"} {
  clock clk_i -both_edges
  clock clk_aon_i
  clock clk_usb_48mhz_i
  clock -rate {tl_i} clk_i
  clock -rate {cio_d_i, cio_dp_i, cio_dn_i, cio_sense_i} clk_usb_48mhz_i
  reset -expr {!rst_ni !rst_aon_ni !rst_usb_48mhz_ni}

# TODO: work with the block owner and re-define FPV checkings for xbar
# } elseif {$env(DUT_TOP) == "xbar_main"} {
#   clock clk_main_i -both_edges
#   reset -expr {!rst_main_ni}

} elseif {$env(DUT_TOP) == "prim_fifo_async_sram_adapter_tb"} {
  clock clk_wr_i -factor 2
  clock -rate {wvalid_i, wready_o, wdata_i} clk_wr_i
  clock clk_rd_i -factor 3
  clock -rate {rvalid_o, rready_i, rdata_o} clk_rd_i
  reset -expr {!rst_ni}

} elseif {$env(DUT_TOP) == "pinmux_tb"} {
  clock clk_i -both_edges
  clock clk_aon_i -factor 5
  clock -rate -default clk_i
  reset -expr {!rst_ni !rst_aon_ni}
} else {
  clock clk_i -both_edges
  reset -expr {!rst_ni}
  clock -rate -default clk_i
}

# Use counter abstractions to reduce the run time.
if {$env(DUT_TOP) == "alert_handler"} {
  abstract -counter -env \
      {u_ping_timer.u_prim_double_lfsr.gen_double_lfsr[0].u_prim_lfsr.gen_max_len_sva.cnt_q}
  abstract -counter -env \
      {u_ping_timer.u_prim_double_lfsr.gen_double_lfsr[1].u_prim_lfsr.gen_max_len_sva.cnt_q}
  abstract -counter -env {gen_classes[0].u_accu.u_prim_count.gen_cross_cnt_hardening.down_cnt}
  abstract -counter -env {gen_classes[1].u_accu.u_prim_count.gen_cross_cnt_hardening.down_cnt}
  abstract -counter -env {gen_classes[2].u_accu.u_prim_count.gen_cross_cnt_hardening.down_cnt}
  abstract -counter -env {gen_classes[3].u_accu.u_prim_count.gen_cross_cnt_hardening.down_cnt}

} elseif {$env(DUT_TOP) == "hmac"} {
  # SHA2: does not check any calculation results, so 64 rounds of calculation can be abstracted.
  abstract -counter -env u_sha2.round
  # disable these assertions because they are unreachable when the fifo is WO
  assert -disable {*hmac.u_tlul_adapter.u_*fifo.*.depthShallNotExceedParamDepth}
  assert -disable {*hmac.u_tlul_adapter.u_*fifo.DataKnown_A}
  assert -disable {*hmac.u_tlul_adapter.rvalidHighReqFifoEmpty}
  assert -disable {*hmac.u_tlul_adapter.rvalidHighWhenRspFifoFull}

} elseif {$env(DUT_TOP) == "flash_ctrl"} {
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
if {$env(DUT_TOP) == "top_earlgrey"} {
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

# TODO: support the following feature.
# Uncomment "jg_auto_coi_cov_waivers" to automatically waive out COI cover items which cannot
# propagate to "relevant signals" (by default, top instance outputs). If you need to specify
# include/exclude relevant signals manually, run "jg_auto_coi_cov_waivers -help" for more
# options.
# jg_auto_coi_cov_waivers

#-------------------------------------------------------------------------
# configure proofgrid
#-------------------------------------------------------------------------

set_proofgrid_per_engine_max_local_jobs 2

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
