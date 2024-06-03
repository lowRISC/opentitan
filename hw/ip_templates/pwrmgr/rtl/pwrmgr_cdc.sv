// Copyright lowRISC contributors (OpenTitan project).
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
  input clk_cpu_i,
  input rst_slow_ni,
  input rst_ni,
  input rst_cpu_ni,

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
  input low_power_hint_i,
  input core_sleeping_i,
  output logic core_sleep_entry_o,
  output logic core_sleep_exit_o,
  output logic core_sleep_pending_clr_o
);

  /////////////////////////////////
  // Track synchronization requests
  /////////////////////////////////

  logic cdc_sync_pending, slow_cdc_sync_pending, cpu_cdc_sync_pending;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cdc_sync_pending <= 1'b0;
    end else if (cfg_cdc_sync_i) begin
      cdc_sync_pending <= 1'b1;
    end else if (cdc_sync_done_o) begin
      cdc_sync_pending <= 1'b0;
    end
  end

  assign cdc_sync_done_o = cdc_sync_pending && !slow_cdc_sync_pending && !cpu_cdc_sync_pending;

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

  // Synchronize qualified core_sleeping events into the pwrmgr fast domain. Use a handshake with
  // software for activating the monitoring of core_sleeping events for low-power entry and fall
  // through exit. Use a hardware-only mechanism to prevent reactivation of the monitoring until
  // both domains have reset (using the REGWEN for CONTROL). Software may busy-poll this CSR before
  // writing LOW_POWER_HINT again, as the synchronization is guaranteed to make forward progress.
  //
  // Strategy bullet points:
  //   - CPU low power entry/exit request events are ignored in the pwrmgr fast domain if
  //     low_power_hint is 0.
  //   - After low_power_hint drops to 0 and the "unlock CONTROL" REGWEN change is staged, a reqack
  //     for "all clear" is used to...
  //     - clear requests in CPU domain
  //     - unlock CONTROL in the fast domain after the ACK
  //   - When low_power_hint is 1 and we get cdc_cfg_sync_i, a reqack for "enable" is used to...
  //     - Turn on events (monitoring core_sleeping)
  //   - Use a prim_flop_2sync for the entry and exit requests.
  //     - For the clearing case, low_power_hint cannot become 1 ahead of the
  //       cleared requests crossing domains. This is guaranteed by sending
  //       the ACK after clearing and forbidding TL-UL writes to CONTROL until
  //       the ACK comes back.
  //     - For the setting case, cdc_sync_done doesn't go high until the ACK
  //       returns. Software should not enter WFI until it performs this
  //       synchronization.
  logic low_power_hint_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      low_power_hint_q <= 1'b0;
    end else begin
      low_power_hint_q <= low_power_hint_i;
    end
  end

  logic low_power_hint_sync_req, low_power_hint_sync_ack;
  logic low_power_hint_sync_reqdata;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      low_power_hint_sync_req <= 1'b0;
      low_power_hint_sync_reqdata <= 1'b0;
      cpu_cdc_sync_pending <= 1'b0;
      core_sleep_pending_clr_o <= 1'b0;
    end else if ((low_power_hint_i && cfg_cdc_sync_i) ||
                 (!low_power_hint_i && low_power_hint_q)) begin
      low_power_hint_sync_req <= 1'b1;
      low_power_hint_sync_reqdata <= low_power_hint_i;
      cpu_cdc_sync_pending <= cfg_cdc_sync_i;
      core_sleep_pending_clr_o <= !low_power_hint_i;
    end else if (low_power_hint_sync_ack) begin
      low_power_hint_sync_req <= 1'b0;
      cpu_cdc_sync_pending <= 1'b0;
      core_sleep_pending_clr_o <= 1'b0;
    end
  end

  logic cpu_low_power_hint_qe, cpu_low_power_hint_q, cpu_low_power_hint_d;
  logic cpu_low_power_hint_ack;
  prim_sync_reqack_data #(
    .Width (1),
    .EnRzHs(1'b1)
  ) u_cpu_low_power_hint_reqack (
    .clk_src_i  (clk_i),
    .rst_src_ni (rst_ni),
    .clk_dst_i  (clk_cpu_i),
    .rst_dst_ni (rst_cpu_ni),
    .req_chk_i  (1'b1),
    .src_req_i  (low_power_hint_sync_req),
    .src_ack_o  (low_power_hint_sync_ack),
    .dst_req_o  (cpu_low_power_hint_qe),
    .dst_ack_i  (cpu_low_power_hint_ack),
    .data_i     (low_power_hint_sync_reqdata),
    .data_o     (cpu_low_power_hint_d)
  );

  always_ff @(posedge clk_cpu_i or negedge rst_cpu_ni) begin
    if (!rst_cpu_ni) begin
      cpu_low_power_hint_q <= 1'b0;
    end else if (cpu_low_power_hint_qe) begin
      cpu_low_power_hint_q <= cpu_low_power_hint_d;
    end
  end

  always_ff @(posedge clk_cpu_i or negedge rst_cpu_ni) begin
    if (!rst_cpu_ni) begin
      cpu_low_power_hint_ack <= 1'b0;
    end else if (!cpu_low_power_hint_ack) begin
      cpu_low_power_hint_ack <= cpu_low_power_hint_qe;
    end else begin
      cpu_low_power_hint_ack <= 1'b0;
    end
  end

  // Qualify core_sleeping events with low_power_hint in the CPU domain, and
  // return the requests to the pwrmgr fast domain.
  logic core_sleep_entry_set, core_sleep_entry_clr;
  assign core_sleep_entry_set = cpu_low_power_hint_q && core_sleeping_i;
  assign core_sleep_entry_clr = !cpu_low_power_hint_q ||
                               (!cpu_low_power_hint_d && cpu_low_power_hint_qe);

  logic core_sleep_entry;
  always_ff @(posedge clk_cpu_i or negedge rst_cpu_ni) begin
    if (!rst_cpu_ni) begin
      core_sleep_entry <= 1'b0;
    end else if (core_sleep_entry_clr) begin
      core_sleep_entry <= 1'b0;
    end else if (core_sleep_entry_set) begin
      core_sleep_entry <= 1'b1;
    end
  end

  logic core_sleep_exit_set, core_sleep_exit_clr;
  assign core_sleep_exit_set = core_sleep_entry && !core_sleeping_i;
  assign core_sleep_exit_clr = !cpu_low_power_hint_q ||
                               (!cpu_low_power_hint_d && cpu_low_power_hint_qe);
  logic core_sleep_exit;
  always_ff @(posedge clk_cpu_i or negedge rst_cpu_ni) begin
    if (!rst_cpu_ni) begin
      core_sleep_exit <= 1'b0;
    end else if (core_sleep_exit_clr) begin
      core_sleep_exit <= 1'b0;
    end else if (core_sleep_exit_set) begin
      core_sleep_exit <= 1'b1;
    end
  end

  prim_flop_2sync #(
    .Width (1'b1)
  ) u_core_sleep_entry_cdc (
    .clk_i,
    .rst_ni,
    .d_i (core_sleep_entry),
    .q_o (core_sleep_entry_o)
  );

  prim_flop_2sync #(
    .Width (1'b1)
  ) u_core_sleep_exit_cdc (
    .clk_i,
    .rst_ni,
    .d_i (core_sleep_exit),
    .q_o (core_sleep_exit_o)
  );

  logic slow_cdc_sync_ack;
  prim_pulse_sync u_scdc_sync (
    .clk_src_i(clk_slow_i),
    .rst_src_ni(rst_slow_ni),
    .src_pulse_i(slow_cdc_sync),
    .clk_dst_i(clk_i),
    .rst_dst_ni(rst_ni),
    .dst_pulse_o(slow_cdc_sync_ack)
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      slow_cdc_sync_pending <= 1'b0;
    end else if (cfg_cdc_sync_i) begin
      slow_cdc_sync_pending <= 1'b1;
    end else if (slow_cdc_sync_ack) begin
      slow_cdc_sync_pending <= 1'b0;
    end
  end

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
