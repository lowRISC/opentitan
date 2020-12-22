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
  output logic req_pwrup_o,
  output pwrup_cause_e pwrup_cause_o,
  output pwr_peri_t peri_reqs_o,
  output logic cdc_sync_done_o,

  // peripheral inputs, mixed domains
  input pwr_peri_t peri_i,
  input pwr_flash_rsp_t flash_i,
  output pwr_flash_rsp_t flash_o,

  // otp interface
  input  pwr_otp_rsp_t otp_i,
  output pwr_otp_rsp_t otp_o,

  // AST inputs, unknown domain
  input pwr_ast_rsp_t ast_i

);

  ////////////////////////////////
  // Sync from clk_i to clk_slow_i
  ////////////////////////////////

  logic slow_cdc_sync;
  pwr_ast_rsp_t slow_ast_q, slow_ast_q2;

  prim_flop_2sync # (
    .Width(1)
  ) i_req_pwrdn_sync (
    .clk_i(clk_slow_i),
    .rst_ni(rst_slow_ni),
    .d_i(req_pwrdn_i),
    .q_o(slow_req_pwrdn_o)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_ack_pwrup_sync (
    .clk_i(clk_slow_i),
    .rst_ni(rst_slow_ni),
    .d_i(ack_pwrup_i),
    .q_o(slow_ack_pwrup_o)
  );

  prim_pulse_sync i_slow_cdc_sync (
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
  ) i_slow_ext_req_sync (
    .clk_i  (clk_slow_i),
    .rst_ni (rst_slow_ni),
    .d_i    (peri_i),
    .q_o    (slow_peri_reqs_o)
  );


  // Some of the AST signals are multi-bits themselves (such as clk_val)
  // thus they need to be delayed one more stage to check for stability
  prim_flop_2sync # (
    .Width($bits(pwr_ast_rsp_t)),
    .ResetValue(PWR_AST_RSP_SYNC_DEFAULT)
  ) i_ast_sync (
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
      slow_main_pd_no <= '0;
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
  ) i_req_pwrup_sync (
    .clk_i,
    .rst_ni,
    .d_i(slow_req_pwrup_i),
    .q_o(req_pwrup_o)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_ack_pwrdn_sync (
    .clk_i,
    .rst_ni,
    .d_i(slow_ack_pwrdn_i),
    .q_o(ack_pwrdn_o)
  );

  prim_flop_2sync # (
    .Width(1)
  ) i_pwrup_chg_sync (
    .clk_i,
    .rst_ni,
    .d_i(slow_pwrup_cause_toggle_i),
    .q_o(pwrup_cause_toggle_q)
  );

  prim_pulse_sync i_scdc_sync (
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
  ) i_ext_req_sync (
    .clk_i,
    .rst_ni,
    .d_i(slow_peri_reqs_masked_i),
    .q_o(peri_reqs_o)
  );

  // synchronize inputs from flash
  prim_flop_2sync #(
    .Width(1),
    .ResetValue(1'b0)
  ) u_sync_flash_done (
    .clk_i,
    .rst_ni,
    .d_i(flash_i.flash_done),
    .q_o(flash_o.flash_done)
  );

  prim_flop_2sync #(
    .Width(1),
    // TODO: Is a value of 1 correct here?
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

endmodule


// An alternative solution relying on finding slow clock edges
// Keep it around just in case

/*
  // finds a clk_slow edge in clk domain to know when it is safe to sync over
  // this signal is only safe to use within the pwrmgr module when the source
  // and destination clock domains are both clear
  logic cdc_safe;

  // pwrup is synced directly as it acts as a start signal to the pulse module
  prim_flop_2sync # (
    .Width(1)
  ) i_pwrup_sync (
    .clk_i,
    .rst_ni,
    .d_i(slow_req_pwrup),
    .q_o(req_pwrup)
  );

  pwrmgr_cdc_pulse i_cdc_pulse (
    .clk_slow_i,
    .clk_i,
    .rst_ni,
    .start_i(req_pwrup),
    .stop_i(req_pwrdn),
    .pulse_o(cdc_safe)
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ack_pwrdn   <= '0;
      pwrup_cause <= Por;
    end else if (cdc_safe) begin
      ack_pwrdn   <= slow_ack_pwrdn;
      pwrup_cause <= slow_pwrup_cause;
    end
  end

  ////////////////////////////
  ///  cdc handling - clk_slow_i
  ////////////////////////////

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      slow_wakeup_en <= '0;
      slow_reset_en  <= '0;
      slow_main_pdb  <= '0;
      slow_io_clk_en <= '0;
      slow_core_clk_en <= '0;
      slow_ack_pwrup <= '0;
      slow_req_pwrdn <= '0;
    end else if (cdc_safe) begin
      slow_wakeup_en <= reg2hw.wakeup_en.q;
      slow_reset_en  <= reg2hw.reset_en.q;
      slow_main_pdb  <= reg2hw.control.main_pdb.q;
      slow_io_clk_en <= reg2hw.control.io_clk_en.q;
      slow_core_clk_en <= reg2hw.control.core_clk_en.q;
      slow_ack_pwrup <= ack_pwrup;
      slow_req_pwrdn <= req_pwrdn;
    end
  end

  // TODO
  // Need to vote on the differential signals to ensure they are stable
  prim_flop_2sync # (
    .Width($bits(pwr_ast_rsp_t))
  ) i_pok_sync (
    .clk_i  (clk_slow_i),
    .rst_ni (rst_slow_ni),
    .d_i    (pwr_ast_i),
    .q_o    (slow_ast_q)
  );
*/
