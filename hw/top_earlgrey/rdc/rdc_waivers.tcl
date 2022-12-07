# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Meridian RDC Waivers

# Assumes modules defined in run-rdc.tcl
if {[info exists modules] == 0} {
  error "modules variable does not exist!" 99
}

foreach mod $modules {
  if {[file exists $RDC_WAIVER_DIR/rdc_waivers.$mod.tcl]} {
    source $RDC_WAIVER_DIR/rdc_waivers.$mod.tcl
  }
}

# clk_ast_ext_i: Ignore S_GENCLK
set_rule_status -rule {S_GENCLK} -status {Waived}  \
  -expression {(ClockTreeSignal=~"IOC6")} \
  -comment {External signal has SW bypass option. But usually not used. So internal generated clock is define ans main clock}

# RstMgrSwRst scenario does not involved in retention logic
set_rule_status -rule {E_RST_METASTABILITY} -status {Waived} \
  -expression {(FromScenario=="RstMgrSwRst") && \
    (MetaStableFlop=~"*u_pinmux_aon.*io_*_retreg*")} \
  -comment {RstMgrSwRst scenario does not involved in retention logic}

# RstMgrSwRst scenario: Xbar should not have any outstanding req.
set_rule_status -rule {E_RST_METASTABILITY} -status {Waived} \
  -expression {(FromScenario=="RstMgrSwRst") && \
    (ResetFlop=~"*.u_reg_if.outstanding_q")} \
  -comment {RstMgrSwRst scenario: Xbar should not have any outstanding req.}

# USBDEV Wake up to PINMUX
set_rule_status -rule {E_RST_METASTABILITY} -status {Waived} \
  -expression {(ResetFlop=~"*.u_usbdev.u_reg.u_wake_control_cdc.u_src_to_dst_req.dst_level_q") && \
    (MetaStableFlop=~"*.u_pinmux_aon.u_usbdev_aon_wake.wake_detect_active_q")} \
  -comment {Suspend request signal is a pulse signal. \
    It is to initiate the wakeup detector FSM inside pinmux. \
    When Power is down, the state machine is already configures.}

# USBDEV SW RST REQ: All reset are in phase (sync assert, sync de-assert)
set_rule_status -rule {E_RST_METASTABILITY} -status {Waived} \
  -expression {(FromScenario=="RstMgrSwRst") && \
    (ResetFlop=~"*.u_usbdev.gen_no_stubbed_*") && \
    (MetaStableFlop=~"*.u_xbar_main.u_asf_41.*.fifo_*ptr*") && \
    (ClockDomains=="USB_CLK::USB_CLK")} \
  -comment {SW Reset is sync assert and sync de-assert. \
    So, when signal crossing the domain, it has no metastability issue.}

# USBDEV, CSR to PAD
set_rule_status -rule {E_RST_METASTABILITY} -status {Waived} \
  -expression {(ResetFlop=~"*.u_usbdev.u_reg.u_phy_pins_drive_d*_o.q*") && \
    (MetaStableFlop=~"USB_*")} \
  -comment {For AonPok, MainPok drop cases, the module floats the PAD \
  intentionally. If the PADs should drive values, the values are \
  pre-configured before entering to the low power modes. \
  For SW_RST_REQ cases, SW should correctly configure the pull-ups, \
  pull-downs prior to resetting the USBDEV IP.}

# Ibex Clock Gating
set_rule_status -rule E_RST_METASTABILITY -status Waived \
  -expression { \
    (ResetFlop=~"*.u_rv_core_ibex.u_core.g_clock_en_secure.u_prim_core_busy_flop.gen_generic.u_impl_generic.q_o[0]") && \
    (MetaStableFlop=~"*.u_rv_core_ibex.u_core.core_clock_gate_i.gen_generic.u_impl_generic.en_latch")} \
  -comment {If clockgating enble is reset, it affects the gating cell when \
    CLK is 0 value.}

# PINMUX CSR to SPI_DEV PADs
set_rule_status -rule E_RST_METASTABILITY -status Waived \
  -expression {(ResetFlop=~"*.u_pinmux_aon.dio*.pull_en") && \
    (MetaStableFlop=~"SPI_DEV_*")} \
  -comment {POR_N resets SPI_DEV. The SPI_CLK portion is in idle state.}

# PINMUX Retention to SPI_HOST
set_rule_status -rule E_RST_METASTABILITY -status Waived \
  -expression {(ResetFlop=~"*.u_pinmux_aon.dio_oe_retreg_q*") && \
    (MetaStableFlop=~"SPI_HOST_CLK")} \
  -comment {SPI_HOST_CLK is in idle when POR_N is asserted.}
# PINMUX Retention to USB
set_rule_status -rule E_RST_METASTABILITY -status Waived \
  -expression {(ResetFlop=~"*.u_pinmux_aon.dio_oe_retreg_q*") && \
    (MetaStableFlop=~"USB_*")} \
  -comment {USB is in idle when POR_N is asserted.}

# AES Clock Gating
set_rule_status -rule E_RST_METASTABILITY -status Waived \
  -expression {(SourceReset=="POR_N") && \
    (ResetFlop=~"*clk_main_aes_trans*") && \
    (MetaStableFlop=~"*u_clk_main_aes_trans.u_cg.*en_latch")} \
  -comment {POR_N resets AES module too.}
# HMAC Clock Gating
set_rule_status -rule E_RST_METASTABILITY -status Waived \
  -expression {(SourceReset=="POR_N") && \
    (ResetFlop=~"*clk_main_hmac_trans*") && \
    (MetaStableFlop=~"*u_clk_main_hmac_trans.u_cg.*en_latch")} \
  -comment {POR_N resets HMAC module too.}
# KMAC Clock Gating
set_rule_status -rule E_RST_METASTABILITY -status Waived \
  -expression {(SourceReset=="POR_N") && \
    (ResetFlop=~"*clk_main_kmac_trans*") && \
    (MetaStableFlop=~"*u_clk_main_kmac_trans.u_cg.*en_latch")} \
  -comment {POR_N resets KMAC module too.}

# OTBN Clock Gating
set_rule_status -rule E_RST_METASTABILITY -status Waived \
  -expression {(SourceReset=="POR_N") && \
    (ResetFlop=~"*clk_main_otbn_trans*") && \
    (MetaStableFlop=~"*u_clk_main_otbn_trans.u_cg.*en_latch")} \
  -comment {POR_N resets OTBN module too.}

# SW_EN to CG
create_view_criteria -name PorNSwEnCg -rule E_RST_METASTABILITY \
  -criteria {(SourceReset=="POR_N") && \
    (ResetFlop=~"*.u_clkmgr_aon.*_sw_en_sync*")}
set_rule_status -rule E_RST_METASTABILITY -status Waived \
  -expression {(SourceReset=="POR_N") && \
    (ResetFlop=~"*.u_clkmgr_aon.*io_div2_peri_sw_en_sync*") && \
    (MetaStableFlop=~"*.u_clk_io_div2_peri_cg.*")}
set_rule_status -rule E_RST_METASTABILITY -status Waived \
  -expression {(SourceReset=="POR_N") && \
    (ResetFlop=~"*.u_clkmgr_aon.*io_peri_sw_en_sync*") && \
    (MetaStableFlop=~"*.u_clk_io_peri_cg.*")}
set_rule_status -rule E_RST_METASTABILITY -status Waived \
  -expression {(SourceReset=="POR_N") && \
    (ResetFlop=~"*.u_clkmgr_aon.*io_div4_peri_sw_en_sync*") && \
    (MetaStableFlop=~"*.u_clk_io_div4_peri_cg.*")}
set_rule_status -rule E_RST_METASTABILITY -status Waived \
  -expression {(SourceReset=="POR_N") && \
    (ResetFlop=~"*.u_clkmgr_aon.*usb_peri_sw_en_sync*") && \
    (MetaStableFlop=~"*.u_clk_usb_peri_cg.*")}

# SPI_HOST_CLK
set_rule_status -rule {E_RST_METASTABILITY} -status {Waived} \
  -expression {(ResetFlop=~"*u_spi_host*u_sck_flop*") && \
    (MetaStableFlop=~"SPI_HOST_CLK")} \
  -comment {If SPI_HOST receives a reset, CS_L will be de-asserted. \
    Any transactions will be cancelled.}

# W_ASYNC_RST_FLOPS
set_rule_status -rule W_ASYNC_RST_FLOPS -status Waived \
  -expression {(DrivingSignal=~"*strap_sampling.tap_strap_q*")} \
  -comment {STRAP can be changed. \
    However, whenever the tap sample is changed, TRST_N holds the \
    reset state. So, all TAPs remain in the reset state. \
    Async reset glitch won't affect the design.  }
set_rule_status -rule W_ASYNC_RST_FLOPS -status Waived \
  -expression {(DrivingSignal=~"*.u_rv_dm.u_pm_en_sync.*")} \
  -comment {LifeCycle HW Debug Enable signal is static and determined \
    at boot time.}

# EN sync to EN Latch in CG
# (io_div4|io_div2|io|usb)_root_ctrl
create_view_criteria -name PorNRootCtrlCg -rule E_RST_METASTABILITY \
  -criteria {(SourceReset=="POR_N") && \
    (ResetFlop=~"*.u_clkmgr_aon.*root_ctrl*") && \
    (MetaStableFlop=~"*.u_*_root_ctrl.u_cg*")}
set_rule_status -rule E_RST_METASTABILITY -status Waived \
  -expression {(SourceReset=="POR_N") && \
    (ResetFlop=~"*.u_clkmgr_aon.u_main_root_ctrl.u_cg*") && \
    (MetaStableFlop=~"*.u_clkmgr_aon.u_main_root_ctrl.u_cg*")}
set_rule_status -rule E_RST_METASTABILITY -status Waived \
  -expression {(SourceReset=="POR_N") && \
    (ResetFlop=~"*.u_clkmgr_aon.u_io_div4_root_ctrl.u_cg*") && \
    (MetaStableFlop=~"*.u_clkmgr_aon.u_io_div4_root_ctrl.u_cg*")}
set_rule_status -rule E_RST_METASTABILITY -status Waived \
  -expression {(SourceReset=="POR_N") && \
    (ResetFlop=~"*.u_clkmgr_aon.u_io_div2_root_ctrl.u_cg*") && \
    (MetaStableFlop=~"*.u_clkmgr_aon.u_io_div2_root_ctrl.u_cg*")}
set_rule_status -rule E_RST_METASTABILITY -status Waived \
  -expression {(SourceReset=="POR_N") && \
    (ResetFlop=~"*.u_clkmgr_aon.u_io_root_ctrl.u_cg*") && \
    (MetaStableFlop=~"*.u_clkmgr_aon.u_io_root_ctrl.u_cg*")}
set_rule_status -rule E_RST_METASTABILITY -status Waived \
  -expression {(SourceReset=="POR_N") && \
    (ResetFlop=~"*.u_clkmgr_aon.u_usb_root_ctrl.u_cg*") && \
    (MetaStableFlop=~"*.u_clkmgr_aon.u_usb_root_ctrl.u_cg*")}

# Waiver: PowerDown to AST Regulator
# No need of verifying AST behavioral model
set_rule_status -rule E_RST_METASTABILITY -status Waived \
  -expression {(SourceReset=="POR_N") && \
    (ResetFlop=~"*.u_pwrmgr_aon.u_slow_fsm.pd_nq") && \
    (MetaStableFlop=~"u_ast.u_rglts_pdm_3p3v.*")} \
  -comment {AST is a behavioral model. No need to verify}
