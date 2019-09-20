// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module implements the ping mechanism. Once enabled, this module uses an
// LFSR-based PRNG to
//
// a) determine the next peripheral index to be pinged (can be an alert receiver or an
//    escalation sender). it it is detected that this particular peripheral is disabled,
//    another index will be drawn from the PRNG.
//
// b) determine the amount of pause cycles to wait before pinging the peripheral selected in a).
//
// Once the ping timer waited for the amount of pause cycles determined in b), it asserts
// the ping enable signal of the peripheral determined in a). If that peripheral does
// not respond within the ping timeout window, an internal alert will be raised.
//
// Further, if a spurious ping_ok signal is detected (i.e., a ping ok that has not been
// requested), the ping timer will also raise an internal alert.
//

module alert_handler_ping_timer (
  input                                     clk_i,
  input                                     rst_ni,
  input                                     entropy_i,          // from TRNG
  input                                     en_i,               // enable ping testing
  input        [alert_pkg::NAlerts-1:0]     alert_en_i,         // determines which alerts to ping
  input        [alert_pkg::PING_CNT_DW-1:0] ping_timeout_cyc_i, // timeout in cycles
  output logic [alert_pkg::NAlerts-1:0]     alert_ping_en_o,    // enable to alert receivers
  output logic [alert_pkg::N_ESC_SEV-1:0]   esc_ping_en_o,      // enable to esc senders
  input        [alert_pkg::NAlerts-1:0]     alert_ping_ok_i,    // response from alert receivers
  input        [alert_pkg::N_ESC_SEV-1:0]   esc_ping_ok_i,      // response from esc senders
  output logic                              alert_ping_fail_o,  // any of the alert receivers failed
  output logic                              esc_ping_fail_o     // any of the esc senders failed
);

  localparam int unsigned NModsToPing = alert_pkg::NAlerts + alert_pkg::N_ESC_SEV;
  localparam int unsigned IdDw        = $clog2(NModsToPing);

  // this defines a random permutation
  localparam int unsigned perm [0:31] = '{ 4, 11, 25,  3,
                                          15, 16,  1, 10,
                                           2, 22,  7,  0,
                                          23, 28, 30, 19,
                                          27, 12, 24, 26,
                                          14, 21, 18,  5,
                                          13,  8, 29, 31,
                                          20,  6,  9, 17};

  //////////////////////////////////////////////////////
  // PRNG
  //////////////////////////////////////////////////////

  logic lfsr_en;
  logic [31:0] lfsr_state, perm_state;

  prim_lfsr #(
    .LfsrDw ( 32                  ),
    .InDw   ( 1                   ),
    .OutDw  ( 32                  ),
    .Seed   ( alert_pkg::LfsrSeed )
  ) i_prim_lfsr (
    .clk_i,
    .rst_ni,
    .en_i   ( lfsr_en    ),
    .data_i ( entropy_i  ),
    .data_o ( lfsr_state )
  );

  for (genvar k = 0; k < 32; k++) begin : gen_perm
    assign perm_state[k] = lfsr_state[perm[k]];
  end

  logic [IdDw-1:0] id_to_ping;
  logic [alert_pkg::PING_CNT_DW-1:0] wait_cyc;
  // we only use bits up to 23, as IdDw is 8bit maximum
  assign id_to_ping = perm_state[16 +: IdDw];
  // concatenate with constant offset, introduce some stagger
  // by concatenating the lower bits below
  assign wait_cyc   = {perm_state[15:2], 8'h01, perm_state[1:0]};

  logic [2**IdDw-1:0] enable_mask;
  always_comb begin : p_enable_mask
    enable_mask                                   = '0;         // tie off unused
    enable_mask[alert_pkg::NAlerts-1:0]           = alert_en_i; // alerts
    enable_mask[NModsToPing-1:alert_pkg::NAlerts] = '1;         // escalation senders
  end

  logic id_vld;
  // check if the randomly drawn ID is actually valid and the alert is enabled
  assign id_vld  = enable_mask[id_to_ping];

  //////////////////////////////////////////////////////
  // Counter
  //////////////////////////////////////////////////////

  logic [alert_pkg::PING_CNT_DW-1:0] cnt_d, cnt_q;
  logic cnt_en, cnt_clr;
  logic wait_ge, timeout_ge;

  assign cnt_d = (cnt_clr) ? '0           :
                 (cnt_en)  ? cnt_q + 1'b1 :
                             cnt_q;

  assign wait_ge    = (cnt_q >= wait_cyc);
  assign timeout_ge = (cnt_q >= ping_timeout_cyc_i);

  //////////////////////////////////////////////////////
  // Ping and Timeout Logic
  //////////////////////////////////////////////////////

  typedef enum logic [1:0] {Init, RespWait, DoPing} state_e;
  state_e state_d, state_q;
  logic ping_en, ping_ok;
  logic [NModsToPing-1:0] ping_sel;
  logic [NModsToPing-1:0] spurious_ping;
  logic spurious_alert_ping, spurious_esc_ping;

  // generate ping enable vector
  assign ping_sel        = (alert_pkg::NAlerts+alert_pkg::N_ESC_SEV)'(ping_en) << id_to_ping;
  assign alert_ping_en_o = ping_sel[alert_pkg::NAlerts-1:0];
  assign esc_ping_en_o   = ping_sel[NModsToPing-1:alert_pkg::NAlerts];

  // mask out response
  assign ping_ok             = |({esc_ping_ok_i, alert_ping_ok_i} & ping_sel);
  assign spurious_ping       = ({esc_ping_ok_i, alert_ping_ok_i} & ~ping_sel);
  // under normal operation, these signals should never be asserted.
  // double check that these signals are not optimized away during synthesis.
  // this may need "don't touch" or "no boundary optimization" constraints
  assign spurious_alert_ping = |spurious_ping[alert_pkg::NAlerts-1:0];
  assign spurious_esc_ping   = |spurious_ping[NModsToPing-1:alert_pkg::NAlerts];

  always_comb begin : p_fsm
    // default
    state_d = state_q;
    cnt_en  = 1'b0;
    cnt_clr = 1'b0;
    lfsr_en = 1'b0;
    ping_en = 1'b0;
    // this captures spurious
    alert_ping_fail_o = spurious_alert_ping;
    esc_ping_fail_o   = spurious_esc_ping;

    unique case (state_q)
      ///////////////////////////
      // wait until activiated
      // we never return to this state
      // once activated!
      Init: begin
        cnt_clr = 1'b0;
        if (en_i) begin
          state_d = RespWait;
        end
      end
      ///////////////////////////
      // wait for random amount of cycles
      // draw another ID/wait count if the
      // peripheral ID is not valid
      RespWait: begin
        if (!id_vld) begin
          lfsr_en = 1'b1;
          cnt_clr = 1'b1;
        end else if (wait_ge) begin
          state_d = DoPing;
          lfsr_en = 1'b1;
          cnt_clr = 1'b1;
        end else begin
          cnt_en = 1'b1;
        end
      end
      ///////////////////////////
      // send out ping request and wait for a ping
      // response or a ping timeout (whatever comes first)
      DoPing: begin
        cnt_en  = 1'b1;
        ping_en = 1'b1;
        if (timeout_ge || ping_ok) begin
          state_d = RespWait;
          cnt_clr = 1'b1;
          if (timeout_ge) begin
            if (id_to_ping < alert_pkg::NAlerts) begin
              alert_ping_fail_o = 1'b1;
            end else begin
              esc_ping_fail_o   = 1'b1;
            end
          end
        end
      end
      ///////////////////////////
      default : state_d = Init;
    endcase

  end

  //////////////////////////////////////////////////////
  // Flops
  //////////////////////////////////////////////////////

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      state_q <= Init;
      cnt_q   <= '0;
    end else begin
      state_q <= state_d;
      cnt_q   <= cnt_d;
    end
  end

  //////////////////////////////////////////////////////
  // Assertions
  //////////////////////////////////////////////////////

  // internals
  `ASSERT(PingOH0, $onehot0(ping_sel), clk_i, !rst_ni)
  // we should never get into the ping state without knowing
  // which module to ping
  `ASSERT(PingOH, ping_en |-> $onehot(ping_sel), clk_i, !rst_ni)

  // TODO: add some cover metrics to check whether all devices
  // are pinged eventually.

endmodule : alert_handler_ping_timer
