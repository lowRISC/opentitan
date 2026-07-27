// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Mode signals for rv_dm

interface rv_dm_mode_if(input clk);
  import lc_ctrl_pkg::lc_tx_t;
  import prim_mubi_pkg::mubi8_t, prim_mubi_pkg::mubi4_t;

  // If is_active is true, the signals that will be connected to its input ports are driven by cb.
  // If is_active is false, they are driven with 'z here, which allows the interface to monitor a
  // larger design that drives rv_dm itself.
  //
  // The flag is defined as a wire with a weak pull-up. This ensures that a testbench that doesn't
  // customise is_active will see the interface be driven actively, but allows a testbench that
  // *does* want to customise the signal to pull it low.
  wire is_active;
  assign (weak0, weak1) is_active = 1'b1;

  wire [31:0]  next_dm_addr;
  wire lc_tx_t lc_hw_debug_clr;
  wire lc_tx_t lc_hw_debug_en;
  wire lc_tx_t lc_dft_en;
  wire lc_tx_t pinmux_hw_debug_en;
  wire lc_tx_t lc_check_byp_en;
  wire lc_tx_t lc_escalate_en;
  wire lc_tx_t lc_init_done;
  wire         strap_en;
  wire         strap_en_override;
  wire mubi8_t otp_dis_rv_dm_late_debug;
  wire mubi4_t scanmode;

  logic [31:0] next_dm_addr_internal;
  lc_tx_t      lc_hw_debug_clr_internal;
  lc_tx_t      lc_hw_debug_en_internal;
  lc_tx_t      lc_dft_en_internal;
  lc_tx_t      pinmux_hw_debug_en_internal;
  lc_tx_t      lc_check_byp_en_internal;
  lc_tx_t      lc_escalate_en_internal;
  lc_tx_t      lc_init_done_internal;
  logic        strap_en_internal;
  logic        strap_en_override_internal;
  mubi8_t      otp_dis_rv_dm_late_debug_internal;
  mubi4_t      scanmode_internal;

  assign next_dm_addr             = is_active ? next_dm_addr_internal             : 'z;
  assign lc_hw_debug_clr          = is_active ? lc_hw_debug_clr_internal          : lc_tx_t'('z);
  assign lc_hw_debug_en           = is_active ? lc_hw_debug_en_internal           : lc_tx_t'('z);
  assign lc_dft_en                = is_active ? lc_dft_en_internal                : lc_tx_t'('z);
  assign pinmux_hw_debug_en       = is_active ? pinmux_hw_debug_en_internal       : lc_tx_t'('z);
  assign lc_check_byp_en          = is_active ? lc_check_byp_en_internal          : lc_tx_t'('z);
  assign lc_escalate_en           = is_active ? lc_escalate_en_internal           : lc_tx_t'('z);
  assign lc_init_done             = is_active ? lc_init_done_internal             : lc_tx_t'('z);
  assign strap_en                 = is_active ? strap_en_internal                 : 'z;
  assign strap_en_override        = is_active ? strap_en_override_internal        : 'z;
  assign otp_dis_rv_dm_late_debug = is_active ? otp_dis_rv_dm_late_debug_internal : mubi8_t'('z);
  assign scanmode                 = is_active ? scanmode_internal                 : mubi4_t'('z);

  // An active clocking block for all signals that are not expected to be constant and are thus
  // driven/sampled on the clock.
  clocking cb @(posedge clk);
    output lc_hw_debug_clr    = lc_hw_debug_clr_internal;
    output lc_hw_debug_en     = lc_hw_debug_en_internal;
    output lc_dft_en          = lc_dft_en_internal;
    output pinmux_hw_debug_en = pinmux_hw_debug_en_internal;
    output lc_check_byp_en    = lc_check_byp_en_internal;
    output lc_escalate_en     = lc_escalate_en_internal;
    output lc_init_done       = lc_init_done_internal;
    output strap_en_override  = strap_en_override_internal;
  endclocking

  // A monitor clocking block for signals that are not expected to be constant.
  clocking mon_cb @(posedge clk);
    input lc_hw_debug_clr    = lc_hw_debug_clr;
    input lc_hw_debug_en     = lc_hw_debug_en;
    input lc_dft_en          = lc_dft_en;
    input pinmux_hw_debug_en = pinmux_hw_debug_en;
    input lc_check_byp_en    = lc_check_byp_en;
    input lc_escalate_en     = lc_escalate_en;
    input lc_init_done       = lc_init_done;
    input strap_en_override  = strap_en_override;
  endclocking
endinterface
