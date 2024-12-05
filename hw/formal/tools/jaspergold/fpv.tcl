# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Environment varibles:
# CHECK: flag to turn on or off conflict and deadloop checks.
# COMMON_MSG_TCL_PATH: string to indicate the path to `jaspergold_common_message_process.tcl` file,
#                      which sets common message configurations.
# COV: flag to turn on or off coverage collection.
# DUT_TOP: string to indicate the top-level module name.
# STOPATS: string to indicate the name of the signal to insert `stopat`.
# TASK: string to collect and prove a subset of assertions that contains these string.
# FPV_DEFINES: string to add additional macro defines during anaylze phase.
# AFTER_LOAD: string with the path to a TCL file that should be sourced after the design and test
#             bench have been loaded. If there is no such file, the variable should be undefined or
#             the string should be empty.

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

# Blackbox prim_count, prim_double_lfsr, and prim_onehot_check to create security countermeasures.
# Blackbox prim_ram_1p and prim_ram_1p_scr to avoid compiling memory blocks.
if {$env(TASK) == "FpvSecCm"} {
  analyze -sv09 \
    +define+FPV_ON \
    +define+FPV_SEC_CM_ON+FPV_ALERT_NO_SIGINT_ERR+$env(FPV_DEFINES) \
    -bbox_m prim_count \
    -bbox_m prim_double_lfsr \
    -bbox_m prim_onehot_check \
    -bbox_m prim_ram_1p \
    -bbox_m prim_ram_1p_scr \
    -f [glob *.scr]
} elseif {($env(DUT_TOP) == "pinmux_tb") || ($env(DUT_TOP) == "pinmux_chip_tb")} {
  analyze -sv09 \
    +define+FPV_ON+$env(FPV_DEFINES) \
    -bbox_m usbdev_aon_wake \
    -f [glob *.scr]
} else {
  analyze -sv09 \
    +define+FPV_ON+$env(FPV_DEFINES) \
    -f [glob *.scr]
}

if {$env(DUT_TOP) == "prim_count_tb"} {
  elaborate -top $env(DUT_TOP) \
            -enable_sva_isunknown \
            -disable_auto_bbox \
            -param ResetValue $ResetValue
} else {
  elaborate -top $env(DUT_TOP) -enable_sva_isunknown -disable_auto_bbox
}

set stopat [regexp -all -inline {[^\s\']+} $env(STOPATS)]
if {$stopat ne ""} {
  stopat -env $stopat
}

if {[info exists ::env(AFTER_LOAD)]} {
    if {$env(AFTER_LOAD) != ""} {
        puts "Running prefix TCL command from $env(AFTER_LOAD)"
        source $env(AFTER_LOAD)
    }
}


#-------------------------------------------------------------------------
# specify clock(s) and reset(s)
#-------------------------------------------------------------------------

# select primary clock and reset condition (use ! for active-low reset)
# note: -both_edges is needed below because the TL-UL protocol checker
# tlul_assert.sv operates on the negedge clock
# even clock this sampled at both_edges, input should only change at posedge clock cycle
# TODO: create each DUT_TOP's individual config file
if {($env(DUT_TOP) == "pinmux_tb") || ($env(DUT_TOP) == "pinmux_chip_tb")} {
  clock clk_i -both_edges
  clock clk_aon_i -factor 5
  clock -rate -default clk_i
  reset -expr {!rst_ni !rst_aon_ni !rst_sys_ni}

} elseif {$env(DUT_TOP) == "prim_fifo_async_sram_adapter_tb"} {
  clock clk_wr_i -factor 2
  clock -rate {wvalid_i, wready_o, wdata_i} clk_wr_i
  clock clk_rd_i -factor 3
  clock -rate {rvalid_o, rready_i, rdata_o} clk_rd_i
  reset -expr {!rst_ni}

} elseif {$env(DUT_TOP) == "pwrmgr"} {
  clock clk_i -both_edges
  clock clk_slow_i -factor 3
  clock clk_lc_i
  clock -rate {esc_rst_tx_i} clk_lc_i
  reset -expr {!rst_ni !rst_slow_ni !rst_main_ni !rst_lc_ni}

} elseif {$env(DUT_TOP) == "rv_dm"} {
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

} elseif {$env(DUT_TOP) == "usbdev"} {
  clock clk_i -both_edges
  clock clk_aon_i
  clock -rate {tl_i, cio_d_i, cio_dp_i, cio_dn_i, cio_sense_i} clk_i
  reset -expr {!rst_ni !rst_aon_ni}

} elseif {$env(DUT_TOP) == "clkmgr"} {
  clock clk_main_i
  clock clk_i -both_edges
  clock clk_io_i -factor 1
  clock clk_usb_i -factor 1
  clock clk_aon_i -factor 2
  clock -rate -default clk_i
  reset -expr {!rst_ni !rst_main_ni}

} elseif {$env(DUT_TOP) == "rstmgr"} {
  clock clk_main_i
  clock clk_i -both_edges
  clock clk_io_i -factor 1
  clock clk_io_div2_i -factor 1
  clock clk_io_div4_i -factor 1
  clock clk_usb_i -factor 1
  clock clk_aon_i -factor 2
  clock -rate -default clk_i
  reset -expr {!rst_ni !rst_por_ni}

} else {
  clock clk_i -both_edges
  reset -expr {!rst_ni}
  clock -rate -default clk_i
}

#-------------------------------------------------------------------------
# disable assertions
#-------------------------------------------------------------------------

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

# run once to check if assumptions have any conflict
if {[info exists ::env(CHECK)]} {
  if {$env(CHECK)} {
    check_assumptions -conflict
    check_assumptions -live
    check_assumptions -dead_end
  }
}

# If `TASK` variable is set, choose the subset of assertions that contain ${TASK} in their
# assertion names.
if {$env(TASK) ne ""} {
  task -create $env(TASK) -source_task <embedded> -copy *$env(TASK)* -copy_assumes -set
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

get_reset_info -x_value -with_reset_pin

# time limit set to 2 hours
if {$env(TASK) ne ""} {
  prove -task $env(TASK) -time_limit 2h
} else {
  prove -all -time_limit 2h
}

report

#-------------------------------------------------------------------------
# check coverage and report
#-------------------------------------------------------------------------

if {$env(COV) == 1} {
  check_cov -measure -time_limit 2h
  check_cov -report -force -exclude { reset waived }
  check_cov -report -no_return -report_file cover.html \
      -html -force -exclude { reset waived }
}
