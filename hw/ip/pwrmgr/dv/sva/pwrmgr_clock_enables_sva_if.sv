// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This has some assertions that check that the output clock enables correspond
// to the control CSR when transitioning into or out of the active state. In
// addition, the usb clock can change anytime when in the active state.
interface pwrmgr_clock_enables_sva_if (
  input logic                        clk_i,
  input logic                        rst_ni,
  input pwrmgr_pkg::fast_pwr_state_e fast_state,
  input pwrmgr_pkg::slow_pwr_state_e slow_state,
  // The synchronized control CSR bits.
  input logic                        main_pd_ni,
  input logic                        io_clk_en_i,
  input logic                        core_clk_en_i,
  input logic                        usb_clk_en_lp_i,
  input logic                        usb_clk_en_active_i,
  input logic                        usb_ip_clk_status_i,
  // The output enables.
  input logic                        main_pd_n,
  input logic                        io_clk_en,
  input logic                        core_clk_en,
  input logic                        usb_clk_en
);

  bit disable_sva;
  bit reset_or_disable;

  always_comb reset_or_disable = !rst_ni || disable_sva;

  sequence transitionUp_S; slow_state == pwrmgr_pkg::SlowPwrStateReqPwrUp; endsequence

  sequence transitionDown_S; slow_state == pwrmgr_pkg::SlowPwrStatePwrClampOn; endsequence

  bit fast_is_active;
  always_comb fast_is_active = fast_state == pwrmgr_pkg::FastPwrStateActive;

  // This allows the usb enable to be slower since it also depends on usb clk_status.
  sequence usbActiveTransition_S;
    ##[0:7] !fast_is_active || usb_clk_en == (usb_clk_en_active_i | usb_ip_clk_status_i);
  endsequence

  `ASSERT(CoreClkPwrUp_A, transitionUp_S |=> core_clk_en == 1'b1, clk_i, reset_or_disable)
  `ASSERT(IoClkPwrUp_A, transitionUp_S |=> io_clk_en == 1'b1, clk_i, reset_or_disable)
  `ASSERT(UsbClkPwrUp_A, transitionUp_S |=> usb_clk_en == usb_clk_en_active_i, clk_i,
          reset_or_disable)

  // This deals with transitions while the fast fsm is active.
  `ASSERT(UsbClkActive_A, fast_is_active && $changed(usb_clk_en_active_i) |=> usbActiveTransition_S,
          clk_i, reset_or_disable)

  `ASSERT(CoreClkPwrDown_A, transitionDown_S |=> core_clk_en == (core_clk_en_i && main_pd_ni),
          clk_i, reset_or_disable)
  `ASSERT(IoClkPwrDown_A, transitionDown_S |=> io_clk_en == (io_clk_en_i && main_pd_ni), clk_i,
          reset_or_disable)
  `ASSERT(UsbClkPwrDown_A, transitionDown_S |=> usb_clk_en == (usb_clk_en_lp_i && main_pd_ni),
          clk_i, reset_or_disable)
endinterface
