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


#-------------------------------------------------------------------------
# read design
#-------------------------------------------------------------------------

# only one scr file exists in this folder
analyze -sv09                 \
  +define+FPV_ON              \
  -f [glob *.scr]

elaborate -top $env(FPV_TOP)

#-------------------------------------------------------------------------
# specify clock(s) and reset(s)
#-------------------------------------------------------------------------

# select primary clock and reset condition (use ! for active-low reset)
# note: -both_edges is needed below because the TL-UL protocol checker
# tlul_assert.sv operates on the negedge clock

if {$env(FPV_TOP) == "rv_dm"} {
  clock clk_i -both_edges
  clock tck_i
  reset -expr {!rst_ni !trst_ni}
} elseif {$env(FPV_TOP) == "spi_device"} {
  clock clk_i -both_edges
  clock cio_sck_i
  reset -expr {!rst_ni cio_csb_i}
} elseif {$env(FPV_TOP) == "usb_fs_nb_pe"} {
  clock clk_48mhz_i
  reset -expr {!rst_ni}
} elseif {$env(FPV_TOP) == "usbuart"} {
  clock clk_i -both_edges
  clock clk_48mhz_i
  reset -expr {!rst_ni}
} elseif {$env(FPV_TOP) == "usbdev"} {
  clock clk_i -both_edges
  clock clk_usb_48mhz_i
  reset -expr {!rst_ni}
} elseif {$env(FPV_TOP) == "top_earlgrey"} {
  clock clk_i -both_edges
  clock jtag_tck_i
  reset -expr {!rst_ni !jtag_trst_ni}
} elseif {$env(FPV_TOP) == "xbar_main"} {
  clock clk_main_i -both_edges
  reset -expr {!rst_main_ni}
} else {
  clock clk_i -both_edges
  reset -expr {!rst_ni}
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

#-------------------------------------------------------------------------
# TODO: eventually remove below assert disable lines
# To reduce prohibitive runtimes, below assertions are simply turned off for now
#-------------------------------------------------------------------------

# spi_device
assert -disable {*spi_device.u_tlul2sram.tlul_assert_host.responseSize*}
assert -disable {*spi_device.u_tlul2sram.tlul_assert_host.onlyOnePendingReq*}
assert -disable {*spi_device.tlul_assert_host.responseMustHaveReq*}
assert -disable {*spi_device.tlul_assert_host.checkResponseOpcode*}
assert -disable {*spi_device.u_reg.tlul_assert_host.responseMustHaveReq*}
assert -disable {*spi_device.u_reg.tlul_assert_host.checkResponseOpcode*}
assert -disable {*spi_device.u_reg.u_socket.tlul_assert_host.responseMustHaveReq*}
assert -disable {*spi_device.u_reg.u_socket.tlul_assert_host.checkResponseOpcode*}
assert -disable {*spi_device.u_reg.u_socket.tlul_assert_device.gen_assert*.tlul_assert.responseSize*}
assert -disable {*spi_device.u_reg.u_socket.tlul_assert_device.gen_assert*.tlul_assert.onlyOnePendingReq*}
assert -disable {*spi_device.u_reg.u_socket.tlul_assert_host.responseSizeMustEqualReq*}
assert -disable {*spi_device.tlul_assert_host.responseSizeMustEqualReq*}

# hmac
assert -disable {*hmac.u_tlul_adapter.tlul_assert_host.onlyOnePendingReq*}
assert -disable {*hmac.u_reg.u_socket.tlul_assert_device.gen_assert[0]*onlyOnePendingReq*}

# flash_ctrl
assert -disable {*flash_ctrl.tlul_assert_host.response*Must*}
assert -disable {*flash_ctrl.u_reg.u_socket.tlul_assert_*.response*Must*}
assert -disable {*flash_ctrl.u_reg.u_socket.tlul_assert_device.gen_assert*.tlul_assert.onlyOnePendingReq*}

# xbar
assert -disable {*xbar_main.tlul_assert_device_*.sizeMatches*}
assert -disable {*xbar_main.tlul_assert_device_*.legalA*}
assert -disable {*xbar_main.tlul_assert_device_*.addressAligned*}
assert -disable {*xbar_main.tlul_assert_device_*.maskMustBeCont*}
assert -disable {*xbar_main.tlul_assert_host_*.legal*}
assert -disable {*xbar_main.u_*.tlul_assert_host.legalDParam*}
assert -disable {*xbar_main.u_*.tlul_assert_device.response*}
assert -disable {*xbar_main.u_*.tlul_assert_device.legalA*}
assert -disable {*xbar_main.u_*.tlul_assert_device.addressAligned*}
assert -disable {*xbar_main.u_*.tlul_assert_device.checkResponseOp*}
assert -disable {*xbar_main.u_*.tlul_assert_device.maskMustBeCont*}
assert -disable {*xbar_main.u_*.tlul_assert_device.sizeMatches*}
assert -disable {*xbar_main.u_*.tlul_assert_*.gen_assert*.tlul_assert.maskMustBeCont*}
assert -disable {*xbar_main.u_*.tlul_assert_*.gen_assert*.tlul_assert.addressAlignedToSize*}
assert -disable {*xbar_main.u_*.tlul_assert_*.gen_assert*.tlul_assert.legal*}
assert -disable {*xbar_main.u_*.tlul_assert_*.gen_assert*.tlul_assert.sizeMatches*}

# top_earlgrey
assert -disable {top_earlgrey.*addressAligned*}
assert -disable {top_earlgrey.*tlul_assert*Must*}
assert -disable {top_earlgrey.*onlyOne*}
assert -disable {top_earlgrey.*Response*}
assert -disable {top_earlgrey.*legal*}
assert -disable {top_earlgrey.u_xbar_main.u_sm1_*.rspIdInRange}
assert -disable {top_earlgrey.u_xbar_main.*depthShall*}
assert -disable {top_earlgrey.u_xbar_main.*tlul_assert*DataKnown*}
assert -disable {top_earlgrey.u_dm_top.*tlul_assert_*DataKnown*}

# TODO: If scanmode is set to 0, then JasperGold errors out complaining
# about combo loops, which should be debugged further. For now, below
# lines work around this issue
if {$env(FPV_TOP) == "top_earlgrey"} {
  assume {scanmode_i == 1}
}

check_assumptions -conflict
check_assumptions -live
check_assumptions -dead_end

#-------------------------------------------------------------------------
# configure proofgrid
#-------------------------------------------------------------------------
set_proofgrid_per_engine_max_local_jobs 16

# Uncomment below 2 lines when using LSF:
# set_proofgrid_mode lsf
# set_proofgrid_per_engine_max_jobs 16

#-------------------------------------------------------------------------
# prove all assertions & report
#-------------------------------------------------------------------------
# time limit set to 2 hours
get_reset_info -x_value -with_reset_pin
prove -all -time_limit 24h
report
#-------------------------------------------------------------------------
# check coverage and report
#-------------------------------------------------------------------------


