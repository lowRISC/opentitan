# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This script has commands to run the design using VC Formal

#-------------------------------------------------------------------------
# Analysing and elaborating the design
#-------------------------------------------------------------------------
# only one scr file exists in this folder

analyze -format sverilog      \
  -vcs "+define+FPV_ON -assert svaext \
        -f [glob *.scr]"

elaborate -sva $env(FPV_TOP)

#-------------------------------------------------------------------------
# Specify clock(s) and reset(s)
#-------------------------------------------------------------------------
# specify the primary clocks and resets in the design.
# use "-period" option with "create_clock" to specify the period
# use "-sense low/high" option with "create_reset" to specify active low or high reset respectively
#
# note: the TL-UL protocol checker tlul_assert.sv operates on the negedge clock

if {$env(FPV_TOP) == "rv_dm"} {
  create_clock clk_i -period 100
  create_clock tck_i -period 100
  create_reset rst_ni -sense low
  create_reset trst_ni -sense low
} elseif {$env(FPV_TOP) == "spi_device"} {
  create_clock clk_i -period 100
  create_clock cio_sck_i -period 100
  create_reset rst_ni -sense low
  create_reset cio_csb_i -sense high
} elseif {$env(FPV_TOP) == "usb_fs_nb_pe"} {
  create_clock clk_48mhz_i -period 100
  create_reset rst_ni -sense low
} elseif {$env(FPV_TOP) == "usbuart"} {
  create_clock clk_i -period 100
  create_clock clk_48mhz_i -period 100
  create_reset rst_ni -sense low
} elseif {$env(FPV_TOP) == "usbdev"} {
  create_clock clk_i -period 100
  create_clock clk_usb_48mhz_i -period 100
  create_reset rst_ni -sense low
} elseif {$env(FPV_TOP) == "top_earlgrey"} {
  create_clock clk_i -period 100
  create_clock jtag_tck_i -period 100
  create_reset rst_ni -sense low
  create_reset jtag_trst_ni -sense low
} elseif {$env(FPV_TOP) == "xbar_main"} {
  create_clock clk_main_i -period 100
  create_reset rst_main_ni -sense low
} else {
  create_clock clk_i -period 100
  create_reset rst_ni -sense low
}

#-------------------------------------------------------------------------
# Assume properties for inputs
#-------------------------------------------------------------------------

# For sram2tlul, input tl_i.a_ready is constrained by below asssertion
fvassume sram2tlul.validNotReady*

# Input scanmode_i should not be X
fvassume *.scanmodeKnown

#-------------------------------------------------------------------------
# TODO: eventually remove below assert disable lines
# To reduce prohibitive runtimes, below assertions are simply turned off for now
#-------------------------------------------------------------------------

# spi_device
fvdisable {*spi_device.u_tlul2sram.tlul_assert_host.responseSize*}
fvdisable {*spi_device.u_tlul2sram.tlul_assert_host.onlyOnePendingReq*}
fvdisable {*spi_device.tlul_assert_host.responseMustHaveReq*}
fvdisable {*spi_device.tlul_assert_host.checkResponseOpcode*}
fvdisable {*spi_device.u_reg.tlul_assert_host.responseMustHaveReq*}
fvdisable {*spi_device.u_reg.tlul_assert_host.checkResponseOpcode*}
fvdisable {*spi_device.u_reg.u_socket.tlul_assert_host.responseMustHaveReq*}
fvdisable {*spi_device.u_reg.u_socket.tlul_assert_host.checkResponseOpcode*}
fvdisable {*spi_device.u_reg.u_socket.tlul_assert_device.gen_assert*.tlul_assert.responseSize*}
fvdisable {*spi_device.u_reg.u_socket.tlul_assert_device.gen_assert*.tlul_assert.onlyOnePendingReq*}
fvdisable {*spi_device.u_reg.u_socket.tlul_assert_host.responseSizeMustEqualReq*}
fvdisable {*spi_device.tlul_assert_host.responseSizeMustEqualReq*}

# hmac
fvdisable {*hmac.u_tlul_adapter.tlul_assert_host.onlyOnePendingReq*}
fvdisable {*hmac.u_reg.u_socket.tlul_assert_device.gen_assert[0]*onlyOnePendingReq*}

# flash_ctrl
fvdisable {*flash_ctrl.tlul_assert_host.response*Must*}
fvdisable {*flash_ctrl.u_reg.u_socket.tlul_assert_*.response*Must*}
fvdisable {*flash_ctrl.u_reg.u_socket.tlul_assert_device.gen_assert*.tlul_assert.onlyOnePendingReq*}

# xbar
fvdisable {*xbar_main.tlul_assert_device_*.sizeMatches*}
fvdisable {*xbar_main.tlul_assert_device_*.legalA*}
fvdisable {*xbar_main.tlul_assert_device_*.addressAligned*}
fvdisable {*xbar_main.tlul_assert_device_*.maskMustBeCont*}
fvdisable {*xbar_main.tlul_assert_host_*.legal*}
fvdisable {*xbar_main.u_*.tlul_assert_host.legalDParam*}
fvdisable {*xbar_main.u_*.tlul_assert_device.response*}
fvdisable {*xbar_main.u_*.tlul_assert_device.legalA*}
fvdisable {*xbar_main.u_*.tlul_assert_device.addressAligned*}
fvdisable {*xbar_main.u_*.tlul_assert_device.checkResponseOp*}
fvdisable {*xbar_main.u_*.tlul_assert_device.maskMustBeCont*}
fvdisable {*xbar_main.u_*.tlul_assert_device.sizeMatches*}
fvdisable {*xbar_main.u_*.tlul_assert_*.gen_assert*.tlul_assert.maskMustBeCont*}
fvdisable {*xbar_main.u_*.tlul_assert_*.gen_assert*.tlul_assert.addressAlignedToSize*}
fvdisable {*xbar_main.u_*.tlul_assert_*.gen_assert*.tlul_assert.legal*}
fvdisable {*xbar_main.u_*.tlul_assert_*.gen_assert*.tlul_assert.sizeMatches*}

# top_earlgrey
fvdisable {top_earlgrey.*addressAligned*}
fvdisable {top_earlgrey.*tlul_assert*Must*}
fvdisable {top_earlgrey.*onlyOne*}
fvdisable {top_earlgrey.*Response*}
fvdisable {top_earlgrey.*legal*}
fvdisable {top_earlgrey.u_xbar_main.u_sm1_*.rspIdInRange}
fvdisable {top_earlgrey.u_xbar_main.*depthShall*}
fvdisable {top_earlgrey.u_xbar_main.*tlul_assert*DataKnown*}
fvdisable {top_earlgrey.u_dm_top.*tlul_assert_*DataKnown*}

#-------------------------------------------------------------------------
# Configure grid usage
#-------------------------------------------------------------------------
# Use "set_grid_usage" option to launch the run on the grid.
# Use option "-type <LSF|RTDA|SGE>=<# of workers>" to specify the type of grid and the numbers of workers
# "-control {<submission commands>} is used to specify the exact qsub/bsub string to use for accessing the grid resources
# Ex: set_grid_usage -type sge=12 -control { qsub -P <machine name> }
set_grid_usage -type RSH=12

#-------------------------------------------------------------------------
# Run all the assertion and cover properties
#-------------------------------------------------------------------------
# time limit set to 2 hours
set_fml_var fml_max_time 2H

# initialize the design
sim_run -stable
sim_save_reset

check_fv -block

#-------------------------------------------------------------------------
# Report
#-------------------------------------------------------------------------
# to generate detailed report add "-verbose" option to "report_fv"
# Ex: report_fv -verbose > ../../../$env(FPV_TOP)_verbose.result
report_fv > ../../../$env(FPV_TOP).result

#-------------------------------------------------------------------------
# Generate Formal Coverage
#-------------------------------------------------------------------------
# VC Formal also provides formal coverage metrics as part of formal signoff flow.
# If you would like to generate formal coverage or need any other help, please send email to vcf_support@synopsys.com

quit
