// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// The overall clock manager

`include "prim_assert.sv"



module clkmgr
import clkmgr_pkg::*;
(
    // Primary module control clocks and resets
    // This drives the register interface
    input clk_i,
    input rst_ni,

    // System clocks and resets
    // These are the source clocks for the system
    input clk_main_i,
    input rst_main_ni,
    input clk_io_i,
    input rst_io_ni,
    input clk_usb_i,
    input rst_usb_ni,
    input clk_aon_i,

    // Resets for derived clocks
    // clocks are derived locally
    input rst_io_div2_ni,

    // Bus Interface
    input  tlul_pkg::tl_h2d_t tl_i,
    output tlul_pkg::tl_d2h_t tl_o,

    // pwrmgr interface
    input  pwrmgr_pkg::pwr_clk_req_t pwr_i,
    output pwrmgr_pkg::pwr_clk_rsp_t pwr_o,

    // dft interface
    input clk_dft_t dft_i,

    // idle hints
    input clk_hint_status_t status_i,

    // clock output interface
    output clkmgr_out_t clocks_o

);

  ////////////////////////////////////////////////////
  // Register Interface
  ////////////////////////////////////////////////////

  clkmgr_reg_pkg::clkmgr_reg2hw_t reg2hw;
  clkmgr_reg_pkg::clkmgr_hw2reg_t hw2reg;

  clkmgr_reg_top u_reg (
      .clk_i,
      .rst_ni,
      .tl_i,
      .tl_o,
      .reg2hw,
      .hw2reg,
      .devmode_i(1'b1)
  );

  ////////////////////////////////////////////////////
  // Divided clocks
  ////////////////////////////////////////////////////
  logic clk_io_div2_i;

  assign clk_io_div2_i = clk_io_i;



  ////////////////////////////////////////////////////
  // Feed through clocks
  // Feed through clocks do not actually need to be in clkmgr, as they are
  // completely untouched. The only reason they are here is for easier
  // bundling management purposes through clocks_o
  ////////////////////////////////////////////////////
  assign clocks_o.clk_io_powerup = clk_io_i;
  assign clocks_o.clk_aon_powerup = clk_aon_i;
  assign clocks_o.clk_main_powerup = clk_main_i;
  assign clocks_o.clk_usb_powerup = clk_usb_i;
  assign clocks_o.clk_io_div2_powerup = clk_io_div2_i;

  ////////////////////////////////////////////////////
  // Root gating
  ////////////////////////////////////////////////////

  logic async_roots_en;
  logic roots_en_q2, roots_en_q1, roots_en_d;
  logic clk_main_root;
  logic clk_main_en;
  logic clk_io_root;
  logic clk_io_en;
  logic clk_usb_root;
  logic clk_usb_en;
  logic clk_io_div2_root;
  logic clk_io_div2_en;

  prim_clock_gating_sync i_main_cg (
      .clk_i     (clk_main_i),
      .rst_ni    (rst_main_ni),
      .test_en_i (dft_i.test_en),
      .async_en_i(pwr_i.ip_clk_en),
      .en_o      (clk_main_en),
      .clk_o     (clk_main_root)
  );
  prim_clock_gating_sync i_io_cg (
      .clk_i     (clk_io_i),
      .rst_ni    (rst_io_ni),
      .test_en_i (dft_i.test_en),
      .async_en_i(pwr_i.ip_clk_en),
      .en_o      (clk_io_en),
      .clk_o     (clk_io_root)
  );
  prim_clock_gating_sync i_usb_cg (
      .clk_i     (clk_usb_i),
      .rst_ni    (rst_usb_ni),
      .test_en_i (dft_i.test_en),
      .async_en_i(pwr_i.ip_clk_en),
      .en_o      (clk_usb_en),
      .clk_o     (clk_usb_root)
  );
  prim_clock_gating_sync i_io_div2_cg (
      .clk_i     (clk_io_div2_i),
      .rst_ni    (rst_io_div2_ni),
      .test_en_i (dft_i.test_en),
      .async_en_i(pwr_i.ip_clk_en),
      .en_o      (clk_io_div2_en),
      .clk_o     (clk_io_div2_root)
  );

  // an async OR of all the synchronized enables
  assign async_roots_en = clk_main_en | clk_io_en | clk_usb_en | clk_io_div2_en;

  // Sync the OR back into clkmgr domain for feedback to pwrmgr.
  // Since the signal is combo / converged on the other side, de-bounce
  // the signal prior to output
  prim_flop_2sync #(
      .Width(1)
  ) i_roots_en_sync (
      .clk_i,
      .rst_ni,
      .d_i(async_roots_en),
      .q_o(roots_en_d)
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      roots_en_q1 <= 1'b0;
      roots_en_q2 <= 1'b0;
    end else begin
      roots_en_q1 <= roots_en_d;

      if (roots_en_q1 == roots_en_d) begin
        roots_en_q2 <= roots_en_q1;
      end
    end
  end

  assign pwr_o.roots_en = roots_en_q2;

  ////////////////////////////////////////////////////
  // Clocks with only root gate
  ////////////////////////////////////////////////////
  assign clocks_o.clk_main_infra = clk_main_root;
  assign clocks_o.clk_io_infra = clk_io_root;
  assign clocks_o.clk_io_secure = clk_io_root;
  assign clocks_o.clk_main_secure = clk_main_root;
  assign clocks_o.clk_io_timers = clk_io_root;
  assign clocks_o.clk_proc_main = clk_main_root;

  ////////////////////////////////////////////////////
  // Software direct control group
  ////////////////////////////////////////////////////

  logic clk_io_peri_sw_en;
  logic clk_usb_peri_sw_en;

  prim_flop_2sync #(
      .Width(1)
  ) i_clk_io_peri_sw_en_sync (
      .clk_i (clk_io_i),
      .rst_ni(rst_io_ni),
      .d_i   (reg2hw.clk_enables.clk_io_peri_en.q),
      .q_o   (clk_io_peri_sw_en)
  );

  prim_clock_gating i_clk_io_peri_cg (
      .clk_i    (clk_io_i),
      .en_i     (clk_io_peri_sw_en & clk_io_en),
      .test_en_i(dft_i.test_en),
      .clk_o    (clocks_o.clk_io_peri)
  );

  prim_flop_2sync #(
      .Width(1)
  ) i_clk_usb_peri_sw_en_sync (
      .clk_i (clk_usb_i),
      .rst_ni(rst_usb_ni),
      .d_i   (reg2hw.clk_enables.clk_usb_peri_en.q),
      .q_o   (clk_usb_peri_sw_en)
  );

  prim_clock_gating i_clk_usb_peri_cg (
      .clk_i    (clk_usb_i),
      .en_i     (clk_usb_peri_sw_en & clk_usb_en),
      .test_en_i(dft_i.test_en),
      .clk_o    (clocks_o.clk_usb_peri)
  );


  ////////////////////////////////////////////////////
  // Software hint group
  // The idle hint feedback is assumed to be synchronous to the
  // clock target
  ////////////////////////////////////////////////////

  logic clk_main_aes_hint;
  logic clk_main_aes_en;
  logic clk_main_hmac_hint;
  logic clk_main_hmac_en;
  logic clk_main_otbn_hint;
  logic clk_main_otbn_en;

  assign clk_main_aes_en = clk_main_aes_hint | ~status_i.idle[0];

  prim_flop_2sync #(
      .Width(1)
  ) i_clk_main_aes_hint_sync (
      .clk_i (clk_main_i),
      .rst_ni(rst_main_ni),
      .d_i   (reg2hw.clk_hints.clk_main_aes_hint.q),
      .q_o   (clk_main_aes_hint)
  );

  prim_clock_gating i_clk_main_aes_cg (
      .clk_i    (clk_main_i),
      .en_i     (clk_main_aes_en & clk_main_en),
      .test_en_i(dft_i.test_en),
      .clk_o    (clocks_o.clk_main_aes)
  );

  assign clk_main_hmac_en = clk_main_hmac_hint | ~status_i.idle[1];

  prim_flop_2sync #(
      .Width(1)
  ) i_clk_main_hmac_hint_sync (
      .clk_i (clk_main_i),
      .rst_ni(rst_main_ni),
      .d_i   (reg2hw.clk_hints.clk_main_hmac_hint.q),
      .q_o   (clk_main_hmac_hint)
  );

  prim_clock_gating i_clk_main_hmac_cg (
      .clk_i    (clk_main_i),
      .en_i     (clk_main_hmac_en & clk_main_en),
      .test_en_i(dft_i.test_en),
      .clk_o    (clocks_o.clk_main_hmac)
  );

  assign clk_main_otbn_en = clk_main_otbn_hint | ~status_i.idle[2];

  prim_flop_2sync #(
      .Width(1)
  ) i_clk_main_otbn_hint_sync (
      .clk_i (clk_main_i),
      .rst_ni(rst_main_ni),
      .d_i   (reg2hw.clk_hints.clk_main_otbn_hint.q),
      .q_o   (clk_main_otbn_hint)
  );

  prim_clock_gating i_clk_main_otbn_cg (
      .clk_i    (clk_main_i),
      .en_i     (clk_main_otbn_en & clk_main_en),
      .test_en_i(dft_i.test_en),
      .clk_o    (clocks_o.clk_main_otbn)
  );


  // state readback
  assign hw2reg.clk_hints_status.clk_main_aes_val.de = 1'b1;
  assign hw2reg.clk_hints_status.clk_main_aes_val.d = clk_main_aes_en;
  assign hw2reg.clk_hints_status.clk_main_hmac_val.de = 1'b1;
  assign hw2reg.clk_hints_status.clk_main_hmac_val.d = clk_main_hmac_en;
  assign hw2reg.clk_hints_status.clk_main_otbn_val.de = 1'b1;
  assign hw2reg.clk_hints_status.clk_main_otbn_val.d = clk_main_otbn_en;


  ////////////////////////////////////////////////////
  // Assertions
  ////////////////////////////////////////////////////


endmodule  // rstmgr
