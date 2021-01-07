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



module clkmgr import clkmgr_pkg::*; (
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
  input rst_io_div4_ni,

  // Bus Interface
  input tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // pwrmgr interface
  input pwrmgr_pkg::pwr_clk_req_t pwr_i,
  output pwrmgr_pkg::pwr_clk_rsp_t pwr_o,

  // dft interface
  input scanmode_i,

  // idle hints
  input [3:0] idle_i,

  // clock bypass control
  input lc_ctrl_pkg::lc_tx_t ast_clk_bypass_ack_i,
  output lc_ctrl_pkg::lc_tx_t lc_clk_bypass_ack_o,

  // clock output interface
  output clkmgr_ast_out_t clocks_ast_o,
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

  lc_ctrl_pkg::lc_tx_t step_down_req;
  logic [1:0] step_down_acks;

  prim_lc_sync u_rcv (
    .clk_i,
    .rst_ni,
    .lc_en_i(ast_clk_bypass_ack_i),
    .lc_en_o(step_down_req)
  );

  logic clk_io_div2_i;
  logic clk_io_div4_i;

  prim_clock_div #(
    .Divisor(2)
  ) u_io_div2_div (
    .clk_i(clk_io_i),
    .rst_ni(rst_io_ni),
    .step_down_req_i(step_down_req == lc_ctrl_pkg::On),
    .step_down_ack_o(step_down_acks[0]),
    .test_en_i(scanmode_i),
    .clk_o(clk_io_div2_i)
  );
  prim_clock_div #(
    .Divisor(4)
  ) u_io_div4_div (
    .clk_i(clk_io_i),
    .rst_ni(rst_io_ni),
    .step_down_req_i(step_down_req == lc_ctrl_pkg::On),
    .step_down_ack_o(step_down_acks[1]),
    .test_en_i(scanmode_i),
    .clk_o(clk_io_div4_i)
  );

  prim_lc_sender u_send (
   .clk_i,
   .rst_ni,
   .lc_en_i(&step_down_acks ? lc_ctrl_pkg::On : lc_ctrl_pkg::Off),
   .lc_en_o(lc_clk_bypass_ack_o)
  );

  ////////////////////////////////////////////////////
  // Feed through clocks
  // Feed through clocks do not actually need to be in clkmgr, as they are
  // completely untouched. The only reason they are here is for easier
  // bundling management purposes through clocks_o
  ////////////////////////////////////////////////////
  prim_clock_buf u_clk_io_div4_powerup_buf (
    .clk_i(clk_io_div4_i),
    .clk_o(clocks_o.clk_io_div4_powerup)
  );
  prim_clock_buf u_clk_aon_powerup_buf (
    .clk_i(clk_aon_i),
    .clk_o(clocks_o.clk_aon_powerup)
  );
  prim_clock_buf u_clk_main_powerup_buf (
    .clk_i(clk_main_i),
    .clk_o(clocks_o.clk_main_powerup)
  );
  prim_clock_buf u_clk_io_powerup_buf (
    .clk_i(clk_io_i),
    .clk_o(clocks_o.clk_io_powerup)
  );
  prim_clock_buf u_clk_usb_powerup_buf (
    .clk_i(clk_usb_i),
    .clk_o(clocks_o.clk_usb_powerup)
  );
  prim_clock_buf u_clk_io_div2_powerup_buf (
    .clk_i(clk_io_div2_i),
    .clk_o(clocks_o.clk_io_div2_powerup)
  );
  prim_clock_buf u_clk_aon_secure_buf (
    .clk_i(clk_aon_i),
    .clk_o(clocks_o.clk_aon_secure)
  );

  ////////////////////////////////////////////////////
  // Root gating
  ////////////////////////////////////////////////////

  logic wait_enable;
  logic wait_disable;
  logic en_status_d;
  logic dis_status_d;
  logic [1:0] en_status_q;
  logic [1:0] dis_status_q;
  logic clk_status;
  logic clk_main_root;
  logic clk_main_en;
  logic clk_io_root;
  logic clk_io_en;
  logic clk_usb_root;
  logic clk_usb_en;
  logic clk_io_div2_root;
  logic clk_io_div2_en;
  logic clk_io_div4_root;
  logic clk_io_div4_en;

  prim_clock_gating_sync u_main_cg (
    .clk_i(clk_main_i),
    .rst_ni(rst_main_ni),
    .test_en_i(scanmode_i),
    .async_en_i(pwr_i.ip_clk_en),
    .en_o(clk_main_en),
    .clk_o(clk_main_root)
  );
  prim_clock_gating_sync u_io_cg (
    .clk_i(clk_io_i),
    .rst_ni(rst_io_ni),
    .test_en_i(scanmode_i),
    .async_en_i(pwr_i.ip_clk_en),
    .en_o(clk_io_en),
    .clk_o(clk_io_root)
  );
  prim_clock_gating_sync u_usb_cg (
    .clk_i(clk_usb_i),
    .rst_ni(rst_usb_ni),
    .test_en_i(scanmode_i),
    .async_en_i(pwr_i.ip_clk_en),
    .en_o(clk_usb_en),
    .clk_o(clk_usb_root)
  );
  prim_clock_gating_sync u_io_div2_cg (
    .clk_i(clk_io_div2_i),
    .rst_ni(rst_io_div2_ni),
    .test_en_i(scanmode_i),
    .async_en_i(pwr_i.ip_clk_en),
    .en_o(clk_io_div2_en),
    .clk_o(clk_io_div2_root)
  );
  prim_clock_gating_sync u_io_div4_cg (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_io_div4_ni),
    .test_en_i(scanmode_i),
    .async_en_i(pwr_i.ip_clk_en),
    .en_o(clk_io_div4_en),
    .clk_o(clk_io_div4_root)
  );

  // an async AND of all the synchronized enables
  // return feedback to pwrmgr only when all clocks are enabled
  assign wait_enable =
    clk_main_en &
    clk_io_en &
    clk_usb_en &
    clk_io_div2_en &
    clk_io_div4_en;

  // an async OR of all the synchronized enables
  // return feedback to pwrmgr only when all clocks are disabled
  assign wait_disable =
    clk_main_en |
    clk_io_en |
    clk_usb_en |
    clk_io_div2_en |
    clk_io_div4_en;

  // Sync clkmgr domain for feedback to pwrmgr.
  // Since the signal is combo / converged on the other side, de-bounce
  // the signal prior to output
  prim_flop_2sync #(
    .Width(1)
  ) u_roots_en_status_sync (
    .clk_i,
    .rst_ni,
    .d_i(wait_enable),
    .q_o(en_status_d)
  );

  prim_flop_2sync #(
    .Width(1)
  ) u_roots_or_sync (
    .clk_i,
    .rst_ni,
    .d_i(wait_disable),
    .q_o(dis_status_d)
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      en_status_q <= '0;
      dis_status_q <= '0;
      clk_status <= '0;
    end else begin
      en_status_q <= {en_status_q[0], en_status_d};
      dis_status_q <= {dis_status_q[0], dis_status_d};

      if (&en_status_q) begin
        clk_status <= 1'b1;
      end else if (|dis_status_q == '0) begin
        clk_status <= 1'b0;
      end
    end
  end

  assign pwr_o.clk_status = clk_status;

  ////////////////////////////////////////////////////
  // Clocks with only root gate
  ////////////////////////////////////////////////////
  assign clocks_o.clk_main_infra = clk_main_root;
  assign clocks_o.clk_io_div4_infra = clk_io_div4_root;
  assign clocks_o.clk_io_div4_secure = clk_io_div4_root;
  assign clocks_o.clk_main_secure = clk_main_root;
  assign clocks_o.clk_io_div4_timers = clk_io_div4_root;
  assign clocks_o.clk_main_timers = clk_main_root;
  assign clocks_o.clk_proc_main = clk_main_root;

  ////////////////////////////////////////////////////
  // Software direct control group
  ////////////////////////////////////////////////////

  logic clk_io_div4_peri_sw_en;
  logic clk_usb_peri_sw_en;

  prim_flop_2sync #(
    .Width(1)
  ) u_clk_io_div4_peri_sw_en_sync (
    .clk_i(clk_io_div4_i),
    .rst_ni(rst_io_div4_ni),
    .d_i(reg2hw.clk_enables.clk_io_div4_peri_en.q),
    .q_o(clk_io_div4_peri_sw_en)
  );

  prim_clock_gating #(
    .NoFpgaGate(1'b1)
  ) u_clk_io_div4_peri_cg (
    .clk_i(clk_io_div4_root),
    .en_i(clk_io_div4_peri_sw_en & clk_io_div4_en),
    .test_en_i(scanmode_i),
    .clk_o(clocks_o.clk_io_div4_peri)
  );

  prim_flop_2sync #(
    .Width(1)
  ) u_clk_usb_peri_sw_en_sync (
    .clk_i(clk_usb_i),
    .rst_ni(rst_usb_ni),
    .d_i(reg2hw.clk_enables.clk_usb_peri_en.q),
    .q_o(clk_usb_peri_sw_en)
  );

  prim_clock_gating #(
    .NoFpgaGate(1'b1)
  ) u_clk_usb_peri_cg (
    .clk_i(clk_usb_root),
    .en_i(clk_usb_peri_sw_en & clk_usb_en),
    .test_en_i(scanmode_i),
    .clk_o(clocks_o.clk_usb_peri)
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
  logic clk_main_kmac_hint;
  logic clk_main_kmac_en;
  logic clk_main_otbn_hint;
  logic clk_main_otbn_en;

  assign clk_main_aes_en = clk_main_aes_hint | ~idle_i[Aes];

  prim_flop_2sync #(
    .Width(1)
  ) u_clk_main_aes_hint_sync (
    .clk_i(clk_main_i),
    .rst_ni(rst_main_ni),
    .d_i(reg2hw.clk_hints.clk_main_aes_hint.q),
    .q_o(clk_main_aes_hint)
  );

  prim_clock_gating #(
    .NoFpgaGate(1'b1)
  ) u_clk_main_aes_cg (
    .clk_i(clk_main_root),
    .en_i(clk_main_aes_en & clk_main_en),
    .test_en_i(scanmode_i),
    .clk_o(clocks_o.clk_main_aes)
  );

  assign clk_main_hmac_en = clk_main_hmac_hint | ~idle_i[Hmac];

  prim_flop_2sync #(
    .Width(1)
  ) u_clk_main_hmac_hint_sync (
    .clk_i(clk_main_i),
    .rst_ni(rst_main_ni),
    .d_i(reg2hw.clk_hints.clk_main_hmac_hint.q),
    .q_o(clk_main_hmac_hint)
  );

  prim_clock_gating #(
    .NoFpgaGate(1'b1)
  ) u_clk_main_hmac_cg (
    .clk_i(clk_main_root),
    .en_i(clk_main_hmac_en & clk_main_en),
    .test_en_i(scanmode_i),
    .clk_o(clocks_o.clk_main_hmac)
  );

  assign clk_main_kmac_en = clk_main_kmac_hint | ~idle_i[Kmac];

  prim_flop_2sync #(
    .Width(1)
  ) u_clk_main_kmac_hint_sync (
    .clk_i(clk_main_i),
    .rst_ni(rst_main_ni),
    .d_i(reg2hw.clk_hints.clk_main_kmac_hint.q),
    .q_o(clk_main_kmac_hint)
  );

  prim_clock_gating #(
    .NoFpgaGate(1'b1)
  ) u_clk_main_kmac_cg (
    .clk_i(clk_main_root),
    .en_i(clk_main_kmac_en & clk_main_en),
    .test_en_i(scanmode_i),
    .clk_o(clocks_o.clk_main_kmac)
  );

  assign clk_main_otbn_en = clk_main_otbn_hint | ~idle_i[Otbn];

  prim_flop_2sync #(
    .Width(1)
  ) u_clk_main_otbn_hint_sync (
    .clk_i(clk_main_i),
    .rst_ni(rst_main_ni),
    .d_i(reg2hw.clk_hints.clk_main_otbn_hint.q),
    .q_o(clk_main_otbn_hint)
  );

  prim_clock_gating #(
    .NoFpgaGate(1'b1)
  ) u_clk_main_otbn_cg (
    .clk_i(clk_main_root),
    .en_i(clk_main_otbn_en & clk_main_en),
    .test_en_i(scanmode_i),
    .clk_o(clocks_o.clk_main_otbn)
  );


  // state readback
  assign hw2reg.clk_hints_status.clk_main_aes_val.de = 1'b1;
  assign hw2reg.clk_hints_status.clk_main_aes_val.d = clk_main_aes_en;
  assign hw2reg.clk_hints_status.clk_main_hmac_val.de = 1'b1;
  assign hw2reg.clk_hints_status.clk_main_hmac_val.d = clk_main_hmac_en;
  assign hw2reg.clk_hints_status.clk_main_kmac_val.de = 1'b1;
  assign hw2reg.clk_hints_status.clk_main_kmac_val.d = clk_main_kmac_en;
  assign hw2reg.clk_hints_status.clk_main_otbn_val.de = 1'b1;
  assign hw2reg.clk_hints_status.clk_main_otbn_val.d = clk_main_otbn_en;

  ////////////////////////////////////////////////////
  // Exported clocks
  ////////////////////////////////////////////////////

  assign clocks_ast_o.clk_ast_sensor_ctrl_io_div4_secure = clocks_o.clk_io_div4_secure;
  assign clocks_ast_o.clk_ast_usbdev_io_div4_peri = clocks_o.clk_io_div4_peri;
  assign clocks_ast_o.clk_ast_usbdev_usb_peri = clocks_o.clk_usb_peri;

  ////////////////////////////////////////////////////
  // Assertions
  ////////////////////////////////////////////////////

  `ASSERT_KNOWN(TlDValidKnownO_A, tl_o.d_valid)
  `ASSERT_KNOWN(TlAReadyKnownO_A, tl_o.a_ready)
  `ASSERT_KNOWN(ExportClocksKownO_A, clocks_ast_o)
  `ASSERT_KNOWN(ClocksKownO_A, clocks_o)

endmodule // clkmgr
