// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Power Manager CDC handling
//

`include "prim_assert.sv"

module pwrmgr_cdc import pwrmgr_pkg::*; import pwrmgr_reg_pkg::*;
(
  // Clocks and resets
  input clk_slow_i,
  input clk_i,
  input rst_slow_ni,
  input rst_ni,

  // slow domain signals,
  input slow_req_pwrup_i,
  input slow_ack_pwrdn_i,
  input slow_fsm_invalid_i,
  input slow_pwrup_cause_toggle_i,
  input pwrup_cause_e slow_pwrup_cause_i,
  output logic [NumWkups-1:0] slow_wakeup_en_o,
  output logic [NumRstReqs-1:0] slow_reset_en_o,
  output logic slow_main_pd_no,
  output logic slow_io_clk_en_o,
  output logic slow_core_clk_en_o,
  output logic slow_usb_clk_en_lp_o,
  output logic slow_usb_clk_en_active_o,
  output logic slow_req_pwrdn_o,
  output logic slow_ack_pwrup_o,
  output pwr_ast_rsp_t slow_ast_o,
  output pwr_peri_t slow_peri_reqs_o,
  input pwr_peri_t slow_peri_reqs_masked_i,
  output logic slow_clr_req_o,
  input slow_usb_ip_clk_en_i,
  output slow_usb_ip_clk_status_o,

  // fast domain signals
  input req_pwrdn_i,
  input ack_pwrup_i,
  input cfg_cdc_sync_i,
  input [NumWkups-1:0] wakeup_en_i,
  input logic [NumRstReqs-1:0] reset_en_i,
  input main_pd_ni,
  input io_clk_en_i,
  input core_clk_en_i,
  input usb_clk_en_lp_i,
  input usb_clk_en_active_i,
  output logic ack_pwrdn_o,
  output logic fsm_invalid_o,
  output logic req_pwrup_o,
  output pwrup_cause_e pwrup_cause_o,
  output pwr_peri_t peri_reqs_o,
  output logic cdc_sync_done_o,
  input clr_slow_req_i,
  output logic usb_ip_clk_en_o,
  input usb_ip_clk_status_i,

  // peripheral inputs, mixed domains
  input pwr_peri_t peri_i,
  input pwr_flash_t flash_i,
  output pwr_flash_t flash_o,

  // otp interface
  input  pwr_otp_rsp_t otp_i,
  output pwr_otp_rsp_t otp_o,

  // AST inputs, unknown domain
  input pwr_ast_rsp_t ast_i,

  // rom_ctrl signals
  input prim_mubi_pkg::mubi4_t rom_ctrl_done_i,
  output prim_mubi_pkg::mubi4_t rom_ctrl_done_o,

  // core sleeping
  input core_sleeping_i,
  output logic core_sleeping_o

);

  ////////////////////////////////
  // Sync from clk_i to clk_slow_i
  ////////////////////////////////

  logic slow_cdc_sync;
  pwr_ast_rsp_t slow_ast_q, slow_ast_q2;

  prim_flop_2sync # (
    .Width(1)
  ) u_req_pwrdn_sync (
    .clk_i(clk_slow_i),
    .rst_ni(rst_slow_ni),
    .d_i(req_pwrdn_i),
    .q_o(slow_req_pwrdn_o)
  );

  prim_flop_2sync # (
    .Width(1)
  ) u_ack_pwrup_sync (
    .clk_i(clk_slow_i),
    .rst_ni(rst_slow_ni),
    .d_i(ack_pwrup_i),
    .q_o(slow_ack_pwrup_o)
  );

  prim_pulse_sync u_slow_cdc_sync (
    .clk_src_i(clk_i),
    .rst_src_ni(rst_ni),
    .src_pulse_i(cfg_cdc_sync_i),
    .clk_dst_i(clk_slow_i),
    .rst_dst_ni(rst_slow_ni),
    .dst_pulse_o(slow_cdc_sync)
  );

  // Even though this is multi-bit, the bits are individual request lines.
  // So there is no general concern about recombining as there is
  // no intent to use them in a related manner.
  prim_flop_2sync # (
    .Width($bits(pwr_peri_t))
  ) u_slow_ext_req_sync (
    .clk_i  (clk_slow_i),
    .rst_ni (rst_slow_ni),
    .d_i    (peri_i),
    .q_o    (slow_peri_reqs_o)
  );

  prim_flop_2sync # (
    .Width(1)
  ) u_ip_clk_status_sync (
    .clk_i  (clk_slow_i),
    .rst_ni (rst_slow_ni),
    .d_i    (usb_ip_clk_status_i),
    .q_o    (slow_usb_ip_clk_status_o)
  );

  // Some of the AST signals are multi-bits themselves (such as clk_val)
  // thus they need to be delayed one more stage to check for stability
  prim_flop_2sync # (
    .Width($bits(pwr_ast_rsp_t)),
    .ResetValue(PWR_AST_RSP_SYNC_DEFAULT)
  ) u_ast_sync (
    .clk_i  (clk_slow_i),
    .rst_ni (rst_slow_ni),
    .d_i    (ast_i),
    .q_o    (slow_ast_q)
  );

  always_ff @(posedge clk_slow_i or negedge rst_slow_ni) begin
    if (!rst_slow_ni) begin
      slow_ast_q2 <= PWR_AST_RSP_SYNC_DEFAULT;
    end else begin
      slow_ast_q2 <= slow_ast_q;
    end
  end

  // if possible, we should simulate below with random delays through
  // flop_2sync
  always_ff @(posedge clk_slow_i or negedge rst_slow_ni) begin
    if (!rst_slow_ni) begin
      slow_ast_o <= PWR_AST_RSP_SYNC_DEFAULT;
    end else if (slow_ast_q2 == slow_ast_q) begin
      // Output only updates whenever sync and delayed outputs both agree.
      // If there are delays in sync, this will result in a 1 cycle difference
      // and the output will hold the previous value
      slow_ast_o <= slow_ast_q2;
    end
  end

  // only register configurations can be sync'd using slow_cdc_sync
  always_ff @(posedge clk_slow_i or negedge rst_slow_ni) begin
    if (!rst_slow_ni) begin
      slow_wakeup_en_o <= '0;
      slow_reset_en_o <= '0;
      slow_main_pd_no <= '1;
      slow_io_clk_en_o <= '0;
      slow_core_clk_en_o <= '0;
      slow_usb_clk_en_lp_o <= '0;
      slow_usb_clk_en_active_o <= 1'b1;
    end else if (slow_cdc_sync) begin
      slow_wakeup_en_o <= wakeup_en_i;
      slow_reset_en_o <= reset_en_i;
      slow_main_pd_no <= main_pd_ni;
      slow_io_clk_en_o <= io_clk_en_i;
      slow_core_clk_en_o <= core_clk_en_i;
      slow_usb_clk_en_lp_o <= usb_clk_en_lp_i;
      slow_usb_clk_en_active_o <= usb_clk_en_active_i;
    end
  end

  ////////////////////////////////
  // Sync from clk_slow_i to clk_i
  ////////////////////////////////

  logic pwrup_cause_toggle_q, pwrup_cause_toggle_q2;
  logic pwrup_cause_chg;

  prim_flop_2sync # (
    .Width(1)
  ) u_req_pwrup_sync (
    .clk_i,
    .rst_ni,
    .d_i(slow_req_pwrup_i),
    .q_o(req_pwrup_o)
  );

  prim_flop_2sync # (
    .Width(1)
  ) u_ack_pwrdn_sync (
    .clk_i,
    .rst_ni,
    .d_i(slow_ack_pwrdn_i),
    .q_o(ack_pwrdn_o)
  );

  prim_flop_2sync # (
    .Width(1)
  ) u_int_fsm_invalid_sync (
    .clk_i,
    .rst_ni,
    .d_i(slow_fsm_invalid_i),
    .q_o(fsm_invalid_o)
  );

  prim_flop_2sync # (
    .Width(1)
  ) u_pwrup_chg_sync (
    .clk_i,
    .rst_ni,
    .d_i(slow_pwrup_cause_toggle_i),
    .q_o(pwrup_cause_toggle_q)
  );

  prim_flop_2sync # (
    .Width(1)
  ) u_ip_clk_en_sync (
    .clk_i,
    .rst_ni,
    .d_i(slow_usb_ip_clk_en_i),
    .q_o(usb_ip_clk_en_o)
  );

  prim_flop_2sync # (
    .Width(1)
  ) u_sleeping_sync (
    .clk_i,
    .rst_ni,
    .d_i(core_sleeping_i),
    .q_o(core_sleeping_o)
  );

  prim_pulse_sync u_scdc_sync (
    .clk_src_i(clk_slow_i),
    .rst_src_ni(rst_slow_ni),
    .src_pulse_i(slow_cdc_sync),
    .clk_dst_i(clk_i),
    .rst_dst_ni(rst_ni),
    .dst_pulse_o(cdc_sync_done_o)
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      pwrup_cause_toggle_q2 <= 1'b0;
    end else begin
      pwrup_cause_toggle_q2 <= pwrup_cause_toggle_q;
    end
  end

  assign pwrup_cause_chg = pwrup_cause_toggle_q2 ^ pwrup_cause_toggle_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      pwrup_cause_o <= Por;
    end else if (pwrup_cause_chg) begin
      pwrup_cause_o <= slow_pwrup_cause_i;
    end
  end

  prim_flop_2sync #(
    .Width($bits(pwr_peri_t))
  ) u_ext_req_sync (
    .clk_i,
    .rst_ni,
    .d_i(slow_peri_reqs_masked_i),
    .q_o(peri_reqs_o)
  );

  prim_flop_2sync #(
    .Width(1),
    .ResetValue(1'b1)
  ) u_sync_flash_idle (
    .clk_i,
    .rst_ni,
    .d_i(flash_i.flash_idle),
    .q_o(flash_o.flash_idle)
  );

  prim_flop_2sync #(
    .Width($bits(pwr_otp_rsp_t)),
    .ResetValue('0)
  ) u_sync_otp (
    .clk_i,
    .rst_ni,
    .d_i(otp_i),
    .q_o(otp_o)
  );

  prim_mubi4_sync #(
    .NumCopies(1),
    .AsyncOn(1),
    .StabilityCheck(1)
  ) u_sync_rom_ctrl (
    .clk_i,
    .rst_ni,
    .mubi_i(rom_ctrl_done_i),
    .mubi_o({rom_ctrl_done_o})
  );

  ////////////////////////////////
  // Handshake
  ////////////////////////////////
  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_clr_req_sync (
    .clk_i(clk_slow_i),
    .rst_ni(rst_slow_ni),
    .d_i(clr_slow_req_i),
    .q_o(slow_clr_req_o)
  );

endmodule
