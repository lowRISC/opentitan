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
# dio_pad_attr_q[12] is SCK PAD. The invert signal remains 0 always
#
# TODO: Create two scns (either vcmain_pok 0 (turn off all clock), or
#       vcmain_pok 1 (all clocks alive))
# regulator FSM stays in VCMON when POR_N is asserted.
set_reset_scenario { \
  { POR_N           { reset { @t0 1 } {#2 0} { #10 1} }} \
  { u_ast.u_rglts_pdm_3p3v.vcaon_pok_h  { constraint {@t0 1} }} \
  { top_earlgrey.u_pinmux_aon.dio_pad_attr_q[12].invert \
    { constraint { @t0 0 } } } \
  { top_earlgrey.u_spi_device.cio_sck_i { constraint { @t0 0 } } } \
  { u_ast.u_rglts_pdm_3p3v.rgls_sm[0] { constraint { @t0 1 } } } \
  { u_ast.u_rglts_pdm_3p3v.rgls_sm[1] { constraint { @t0 0 } } } \
  { u_ast.u_rglts_pdm_3p3v.rgls_sm[2] { constraint { @t0 0 } } } \
} -name ScnPOR

# AST AON POK
# When AON_POK drops, main_pok goes to 0 also
set_reset_scenario { \
  { u_ast.u_rglts_pdm_3p3v.vcaon_pok_h  { reset { @t0 1 } { #5 0 } { #10 1 } } } \
  { u_ast.u_rglts_pdm_3p3v.vcmain_pok_h { reset { @t0 1 } { #5 0 } { #10 1 } } } \
  { POR_N                               { constraint { @t0 1 } } } \
  { top_earlgrey.u_spi_device.cio_sck_i { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_io_div4_powerup { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_main_powerup    { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_io_powerup      { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_usb_powerup     { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_io_div2_powerup { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_main_aes        { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_main_hmac       { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_main_kmac       { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_main_otbn       { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_io_div4_infra   { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_main_infra      { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_usb_infra       { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_io_infra        { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_io_div2_infra   { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_io_div4_secure  { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_main_secure     { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_io_div4_timers  { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_io_div4_peri    { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_io_div2_peri    { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_io_peri         { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_usb_peri        { constraint { @t0 0 } } } \
  { top_earlgrey.pwrmgr_aon_low_power                  { constraint { @t0 1 } } } \
  { top_earlgrey.spi_device_passthrough_req.passthrough_en { constraint { @t0 0 } } } \
  { top_earlgrey.u_spi_host0.reg2hw.control.output_en.q    { constraint { @t0 0 } } } \
  { top_earlgrey.u_pinmux_aon.u_pinmux_strap_sampling.tap_strap_q { constraint { @t0 0 } } } \
} -name ScnAonPOK

# AST Regulator Resets
# This scenario is entering low power mode (not brownout) in that case the
# clocks other than clk_aon are gated prior to turn off main power.
set_reset_scenario { \
  { u_ast.u_rglts_pdm_3p3v.vcmain_pok_h { reset { @t0 1 } { #2 0 } { #10 1 } } } \
  { u_ast.u_rglts_pdm_3p3v.vcaon_pok_h  { constraint { @t0 1} } } \
  { top_earlgrey.u_spi_device.cio_sck_i { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_io_div4_powerup { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_main_powerup    { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_io_powerup      { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_usb_powerup     { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_io_div2_powerup { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_main_aes        { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_main_hmac       { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_main_kmac       { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_main_otbn       { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_io_div4_infra   { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_main_infra      { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_usb_infra       { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_io_infra        { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_io_div2_infra   { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_io_div4_secure  { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_main_secure     { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_io_div4_timers  { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_io_div4_peri    { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_io_div2_peri    { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_io_peri         { constraint { @t0 0 } } } \
  { top_earlgrey.clkmgr_aon_clocks.clk_usb_peri        { constraint { @t0 0 } } } \
  { top_earlgrey.pwrmgr_aon_low_power                  { constraint { @t0 1 } } } \
  { top_earlgrey.spi_device_passthrough_req.passthrough_en { constraint { @t0 0 } } } \
  { top_earlgrey.u_spi_host0.reg2hw.control.output_en.q    { constraint { @t0 0 } } } \
  { top_earlgrey.u_pinmux_aon.u_pinmux_strap_sampling.tap_strap_q { constraint { @t0 0 } } } \
} -name ScnMainPok

#set_reset_scenario { \
#  { u_ast.u_rglts_pdm_3p3v.rglssm_vmppr_h_o { reset { @t0 0 } { #10 1}}} \
#  { top_earlgrey.u_spi_device.cio_sck_i { constraint { @t0 0 } } } \
#} -name ScnRglSsmVmppr
#
#set_reset_scenario { \
#  { u_ast.u_rglts_pdm_3p3v.deep_sleep_h_o \
#    { reset { @t0 1 } { #10 0} { #10 0 }} \
#  } \
#} -name ScnRglDeepSleep

# PWRMGR Reset Cause

# RSTMGR SW Resets
#set_reset_scenario { {{top_earlgrey.u_rstmgr_aon.u_ndm_sync.u_sync_2.gen_generic.u_impl_generic.q_o[0]} {reset  { @t0 1 } { #10 0}} }} -name Scenario8 -comment "functional reset"
set_reset_scenario { \
  {{top_earlgrey.u_rstmgr_aon.u_reg.u_sw_rst_ctrl_n_0.q[0]} {reset  { @t0 1 } { #2 0 } { #10 1}} } \
  {{top_earlgrey.u_rstmgr_aon.u_reg.u_sw_rst_ctrl_n_1.q[0]} {reset  { @t0 1 } { #2 0 } { #10 1}} } \
  {{top_earlgrey.u_rstmgr_aon.u_reg.u_sw_rst_ctrl_n_2.q[0]} {reset  { @t0 1 } { #2 0 } { #10 1}} } \
  {{top_earlgrey.u_rstmgr_aon.u_reg.u_sw_rst_ctrl_n_3.q[0]} {reset  { @t0 1 } { #2 0 } { #10 1}} } \
  {{top_earlgrey.u_rstmgr_aon.u_reg.u_sw_rst_ctrl_n_4.q[0]} {reset  { @t0 1 } { #2 0 } { #10 1}} } \
  {{top_earlgrey.u_rstmgr_aon.u_reg.u_sw_rst_ctrl_n_5.q[0]} {reset  { @t0 1 } { #2 0 } { #10 1}} } \
  {{top_earlgrey.u_rstmgr_aon.u_reg.u_sw_rst_ctrl_n_6.q[0]} {reset  { @t0 1 } { #2 0 } { #10 1}} } \
  {{top_earlgrey.u_rstmgr_aon.u_reg.u_sw_rst_ctrl_n_7.q[0]} {reset  { @t0 1 } { #2 0 } { #10 1}} } \
  { POR_N                               { constraint { @t0 1 } } } \
  { u_ast.u_rglts_pdm_3p3v.vcmain_pok_h { constraint { @t0 1 } } } \
  { u_ast.u_rglts_pdm_3p3v.vcaon_pok_h  { constraint { @t0 1 } } } \
  { top_earlgrey.u_spi_device.cio_sck_i { constraint { @t0 0 } } } \
  { top_earlgrey.spi_device_passthrough_req.passthrough_en { constraint { @t0 0 } } } \
  { top_earlgrey.u_spi_host0.reg2hw.control.output_en.q    { constraint { @t0 0 } } } \
} -name RstMgrSwRst -comment "RSTMGR SW Controlled Resets"

# SPI_DEVICE FIFO Reset (Sync)
#  They can be asserted only in Generic Mode. Keep Mode in Generic then assert
#  reset.
#
# Assume control_mode is Generic mode `CONTROL.mode {constraint {@t0 0}}`
# Then `CONTROL.rst_rxfifo` 0 -> 1 {after 10 clks} -> 0 {after 4 clks}
set_reset_scenario { \
  { {top_earlgrey.u_spi_device.u_reg.u_control_rst_rxfifo.q[0]} \
    {reset  { @t0 0 } { #10 1} { #4 0 }} } \
  { top_earlgrey.u_spi_device.u_reg.u_control_mode.q \
    {constraint { @t0 S } } } \
  { top_earlgrey.u_spi_device.rst_csb_buf {constraint { @t0 1 } } } \
  } -name SpidRstRxFifo -comment "SPI_DEVICE Async RX FIFO Functional Reset"
set_reset_scenario { \
  { {top_earlgrey.u_spi_device.u_reg.u_control_rst_txfifo.q[0]} \
    {reset  { @t0 0 } { #10 1} { #4 0 }} } \
  { top_earlgrey.u_spi_device.u_reg.u_control_mode.q \
    {constraint { @t0 S } } } \
  { top_earlgrey.u_spi_device.rst_csb_buf {constraint { @t0 1 } } } \
  } -name SpidRstTxFifo -comment "SPI_DEVICE Async TX FIFO Functional Reset"

# SPI_DEVICE CSb Reset. IP reset should be stable
set_reset_scenario { \
 { {top_earlgrey.u_spi_device.rst_csb_buf} { reset { @t0 1 } { #10 0} } } \
 { u_ast.u_rglts_pdm_3p3v.vcaon_pok_h      { constraint { @t0 1 } } } \
 { top_earlgrey.u_spi_device.rst_ni        { constraint { @t0 1 } } } \
} -name RstSpidCsb -comment "SPI_DEVICE CSb Assertion"

# SPI_DEVICE TPM CSb Reset. SPID IP reset should be stable
set_reset_scenario { \
  { {top_earlgrey.u_spi_device.rst_tpm_csb_buf} \
    {reset { @t0 1} {#10 0}} } \
  { u_ast.u_rglts_pdm_3p3v.vcaon_pok_h { constraint { @t0 1 } } } \
  { POR_N                              { constraint { @t0 1 } } } \
  { top_earlgrey.u_spi_device.rst_ni   { constraint { @t0 1 } } } \
} -name RstSpidTpmCsb -comment "SPI_DEVICE TPM CSb Assertion"

# JTAG Scenarios
## RV_DM
set_reset_scenario { \
  { top_earlgrey.u_pinmux_aon.u_pinmux_strap_sampling.jtag_req.trst_n \
    { reset { @t0 1 } { #10 0 } { #10 1 } } } \
  { top_earlgrey.u_pinmux_aon.u_pinmux_strap_sampling.tap_strap_q[1] { constraint { @t0 1 } } } \
  { top_earlgrey.u_pinmux_aon.u_pinmux_strap_sampling.tap_strap_q[0] { constraint { @t0 0 } } } \
  { top_earlgrey.u_rv_dm.dap.i_dmi_cdc.i_cdc_req.u_prim_sync_reqack.gen_rz_hs_protocol.dst_fsm_q \
    { constraint { @t0 0 } } } \
  { top_earlgrey.u_rv_dm.dap.i_dmi_cdc.i_cdc_req.wvalid_i \
    { constraint { @t0 0 } } } \
  { top_earlgrey.u_rv_dm.dap.i_dmi_cdc.i_cdc_req.pending_q \
    { constraint { @t0 0 } } } \
  { top_earlgrey.u_rv_dm.dap.i_dmi_cdc.i_cdc_req.u_prim_sync_reqack.gen_rz_hs_protocol.src_fsm_q \
    { constraint { @t0 0 } } } \
  { POR_N                               { constraint { @t0 1 } } } \
  { u_ast.u_rglts_pdm_3p3v.vcaon_pok_h  { constraint { @t0 1 } } } \
  { u_ast.u_rglts_pdm_3p3v.vcmain_pok_h { constraint { @t0 1 } } } \
} -name JtagRvDm -comment "RV_DM JTAG Reset Scenario"
## LC_CTRL
set_reset_scenario { \
  { top_earlgrey.u_pinmux_aon.u_pinmux_strap_sampling.jtag_req.trst_n \
    { reset { @t0 1 } { #10 0 } { #10 1 } } } \
  { top_earlgrey.u_pinmux_aon.u_pinmux_strap_sampling.tap_strap_q[1] { constraint { @t0 0 } } } \
  { top_earlgrey.u_pinmux_aon.u_pinmux_strap_sampling.tap_strap_q[0] { constraint { @t0 1 } } } \
  { top_earlgrey.u_lc_ctrl.u_dmi_jtag.i_dmi_cdc.i_cdc_req.u_prim_sync_reqack.gen_rz_hs_protocol.dst_fsm_q \
    { constraint { @t0 0 } } } \
  { top_earlgrey.u_lc_ctrl.u_dmi_jtag.i_dmi_cdc.i_cdc_req.u_prim_sync_reqack.gen_rz_hs_protocol.src_fsm_q \
    { constraint { @t0 0 } } } \
  { top_earlgrey.u_lc_ctrl.u_dmi_jtag.i_dmi_cdc.i_cdc_req.wvalid_i \
    { constraint { @t0 0 } } } \
  { top_earlgrey.u_lc_ctrl.u_dmi_jtag.i_dmi_cdc.i_cdc_req.pending_q \
    { constraint { @t0 0 } } } \
  { POR_N                               { constraint { @t0 1 } } } \
  { u_ast.u_rglts_pdm_3p3v.vcaon_pok_h  { constraint { @t0 1 } } } \
  { u_ast.u_rglts_pdm_3p3v.vcmain_pok_h { constraint { @t0 1 } } } \
} -name JtagLifeCycle -comment "LC_CTRL JTAG Reset Scenario"
