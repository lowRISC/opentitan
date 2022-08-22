# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Meridian RDC Reset Scenario

###################
# Reset Scenarios #
###################

# TODO: SPI_CSB asserted(release from reset) only when SYS_RST_N is not asserted


# POR_N
# When POR_N released, POK remains high (already released from reset)
set_reset_scenario { \
  { POR_N           { reset {#2 0} { #10 1} }} \
  { u_ast.vcaon_pok { constraint {@t0 1} }} \
} -name ScnPOR

# AST POK
set_reset_scenario { \
  { u_ast.vcaon_pok { reset {@t0 0} { #2 1} } } \
} -name ScnPOK

# AST Regulator Resets
set_reset_scenario { \
  { u_ast.u_rglts_pdm_3p3v.vcmain_pok_h { reset { @t0 0 } { #10 1}}} \
} -name ScnMainPok

set_reset_scenario { \
  { u_ast.u_rglts_pdm_3p3v.rglssm_vmppr_h_o { reset { @t0 0 } { #10 1}}} \
} -name ScnRglSsmVmppr

set_reset_scenario { \
  { u_ast.u_rglts_pdm_3p3v.deep_sleep_h_o \
    { reset { @t0 1 } { #10 0} { #10 0 }} \
  } \
} -name ScnRglDeepSleep

# PWRMGR Reset Cause

# RSTMGR SW Resets
#set_reset_scenario { {{top_earlgrey.u_rstmgr_aon.u_ndm_sync.u_sync_2.gen_generic.u_impl_generic.q_o[0]} {reset  { @t0 1 } { #10 0}} }} -name Scenario8 -comment "functional reset"
set_reset_scenario { \
  {{top_earlgrey.u_rstmgr_aon.u_reg.u_sw_rst_ctrl_n_0.q[0]} {reset  { @t0 0 } { #10 1}} } \
  {{top_earlgrey.u_rstmgr_aon.u_reg.u_sw_rst_ctrl_n_1.q[0]} {reset  { @t0 0 } { #10 1}} } \
  {{top_earlgrey.u_rstmgr_aon.u_reg.u_sw_rst_ctrl_n_2.q[0]} {reset  { @t0 0 } { #10 1}} } \
  {{top_earlgrey.u_rstmgr_aon.u_reg.u_sw_rst_ctrl_n_3.q[0]} {reset  { @t0 0 } { #10 1}} } \
  {{top_earlgrey.u_rstmgr_aon.u_reg.u_sw_rst_ctrl_n_4.q[0]} {reset  { @t0 0 } { #10 1}} } \
  {{top_earlgrey.u_rstmgr_aon.u_reg.u_sw_rst_ctrl_n_5.q[0]} {reset  { @t0 0 } { #10 1}} } \
  {{top_earlgrey.u_rstmgr_aon.u_reg.u_sw_rst_ctrl_n_6.q[0]} {reset  { @t0 0 } { #10 1}} } \
  {{top_earlgrey.u_rstmgr_aon.u_reg.u_sw_rst_ctrl_n_7.q[0]} {reset  { @t0 0 } { #10 1}} } \
  { POR_N           { constraint { @t0 1 } } } \
  { u_ast.vcaon_pok { constraint { @t0 1 } } } \
} -name RstMgrSwRst -comment "RSTMGR SW Controlled Resets"

# SPI_DEVICE FIFO Reset (Sync)
#  They can be asserted only in Generic Mode. Keep Mode in Generic then assert
#  reset.
#
# Assume control_mode is Generic mode `{constraint {@t0 0}}`
# Then `CONTROL.rst_rxfifo` 0 -> 1 {after 10 clks} -> 0 {after 4 clks}
set_reset_scenario { \
  { {top_earlgrey.u_spi_device.u_reg.u_control_rst_rxfifo.q[0]} \
    {reset  { @t0 0 } { #10 1} { #4 0 }} } \
  { top_earlgrey.u_spi_device.u_reg.u_control_mode.q \
    {constraint {@t0 0}}} \
  } -name SpidRstRxFifo -comment "SPI_DEVICE Async RX FIFO Functional Reset"
set_reset_scenario { \
  { {top_earlgrey.u_spi_device.u_reg.u_control_rst_txfifo.q[0]} \
    {reset  { @t0 0 } { #10 1} { #4 0 }} } \
  { top_earlgrey.u_spi_device.u_reg.u_control_mode.q \
    {constraint {@t0 0}}} \
  } -name SpidRstTxFifo -comment "SPI_DEVICE Async TX FIFO Functional Reset"
