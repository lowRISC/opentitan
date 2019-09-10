# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# clear previous settings
clear -all

#-------------------------------------------------------------------------
# read design
#-------------------------------------------------------------------------
analyze -sv09 \
  -f formal_0.scr \
  [glob ../../../../ip/*/dv/*_bind.sv] \
  [glob ../../../../ip/*/dv/tb/*_bind.sv] \
  +define+ASIC_SYNTHESIS \
  +define+SYNTHESIS      \
  +define+FPV_ON

elaborate -top $env(FPV_TOP)

#-------------------------------------------------------------------------
# specify clock(s) and reset(s0
#-------------------------------------------------------------------------

# select primary clock and reset condition (use ! for active-low reset)
if {$env(FPV_TOP) == "usb_fs_nb_pe"} {
  clock clk_48mhz_i -both_edges
  reset -expr {!rst_ni}
} elseif {$env(FPV_TOP) == "xbar_main"} {
  clock clk_main_i -both_edges
  reset -expr {!rst_main_ni}
} else {
  clock clk_i -both_edges
  reset -expr {!rst_ni}
}
# TODO: define additional clocks here for modules with multiple clocks
# (such as cio_sck_i for spi_device module)

#-------------------------------------------------------------------------
# assume properties for inputs
#-------------------------------------------------------------------------

# For generated *_reg_top modules, below assertion solely depends on
# module inputs a_valid and a_user.parity_en, and therefore is
# assumed to be correct
assume -from_assert -remove_original -regexp {^\w*\.u_reg\.reqParity}

# For all TL-UL host-interfaces (i.e. ports interfacing a host), A-channel is
# an input, so inputs a_opcode, a_param, etc. are constrained by below assuames.
# Note that all tlul_assert checkers for host interfaces are called tlul_assert_host*
assume -from_assert -remove_original -regexp {^\w*\.tlul_assert_host\w*\.legalAOpcode}
assume -from_assert -remove_original -regexp {^\w*\.tlul_assert_host\w*\.legalAParam}
assume -from_assert -remove_original -regexp {^\w*\.tlul_assert_host\w*\.sizeMatchesMask}
assume -from_assert -remove_original -regexp {^\w*\.tlul_assert_host\w*\.onlyOnePendingReqPerSourceID}
assume -from_assert -remove_original -regexp {^\w*\.tlul_assert_host\w*\.addressAlignedToSize}
assume -from_assert -remove_original -regexp {^\w*\.tlul_assert_host\w*\.maskMustBeContiguous}

# For all TL-UL device-interfaces (i.e. ports interfacing a device), D-channel is an
# input, so inputs d_* are constrained by below assumes
assume -from_assert -remove_original -regexp {^\w*\.tlul_assert_device\w*\.checkResponseOpcode}
assume -from_assert -remove_original -regexp {^\w*\.tlul_assert_device\w*\.legalDParam}
assume -from_assert -remove_original -regexp {^\w*\.tlul_assert_device\w*\.responseSizeMustEqualReqSize}
assume -from_assert -remove_original -regexp {^\w*\.tlul_assert_device\w*\.responseMustHaveReq}

# Notes on above regular expressions: ^ indicates the beginning of the string;
# \w* includes all letters a-z, A-Z, and the underscore, but not the period.
# And \. is for period (with escape). These regular expressions make sure that
# the assume only applies to module_name.tlul_assert_*, but not to
# module_name.submodule.tlul_assert_*

# For sram2tlul, input tl_i.a_ready is constrained by below asssertion
if {$env(FPV_TOP) == "sram2tlul"} {
  assume -from_assert -remove_original {sram2tlul.validNotReady}
}

# TODO: remove below assert disable lines
# To reduce prohibitive runtimes, below assertions are simply turned off for now
assert -disable {spi_device.u_tlul2sram.*}
assert -disable {spi_device*.responseMustHaveReq}
assert -disable {spi_device*.checkResponseOpcode}
assert -disable {spi_device.u_reg.u_socket.tlul_assert_device.responseSize*}
assert -disable {spi_device.u_reg.u_socket.tlul_assert_device.onlyOnePendingReq*}
assert -disable {spi_device.u_reg.u_socket.tlul_assert_host.responseSizeMustEqualReq*}
assert -disable {spi_device.tlul_assert_host.responseSizeMustEqualReq*}
assert -disable {hmac.u_tlul_adapter.*}
assert -disable {hmac.tlul_assert_host.response*Must*}
assert -disable {hmac.tlul_assert_host.checkResponseOpcode*}
assert -disable {hmac.u_reg.u_socket.tlul_assert_*.response*Must*}
assert -disable {hmac.u_reg.u_socket.tlul_assert_*.*ResponseOpcode}
assert -disable {hmac.u_reg.u_socket.tlul_assert_*.onlyOnePendingReq*}
assert -disable {flash_ctrl.tlul_assert_host.response*Must*}
assert -disable {flash_ctrl.u_reg.u_socket.tlul_assert_*.response*Must*}
assert -disable {flash_ctrl.u_reg.u_socket.tlul_assert_device.onlyOnePendingReq*}
assert -disable {xbar_main.tlul_assert_device_*}
assert -disable {xbar_main.tlul_assert_host_*.legal*}
assert -disable {xbar_main.u_s*}
assert -disable {top_earlgrey.u_xbar_main.*}
assert -disable {top_earlgrey.*tl_adapter_*}
assert -disable {top_earlgrey.*tlul_assert_*}
assert -disable {top_earlgrey.*.u_reg.reAfter*}
assert -disable {top_earlgrey.*.u_reg.reqParity}
assert -disable {top_earlgrey.hmac.u_tlul_adapter.*}
assert -disable {top_earlgrey.spi_devicore.u_core.load_store_unit_i.*}
assert -disable {top_earlgrey.core.u_core.load_store_unit_i.*}
assert -disable {top_earlgrey.uart.uart_core.u_uart_rxfifo.depthShall*}

#-------------------------------------------------------------------------
# prove all assertions & covers, report
#-------------------------------------------------------------------------
set_proofgrid_per_engine_max_local_jobs 8
prove -all
report

exit
