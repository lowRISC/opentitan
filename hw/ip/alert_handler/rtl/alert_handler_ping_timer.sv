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

`include "prim_assert.sv"

module alert_handler_ping_timer import alert_pkg::*; #(
  // Compile time random constants, to be overriden by topgen.
  parameter lfsr_seed_t        RndCnstLfsrSeed = RndCnstLfsrSeedDefault,
  parameter lfsr_perm_t        RndCnstLfsrPerm = RndCnstLfsrPermDefault,
  // Enable this for DV, disable this for long LFSRs in FPV
  parameter bit                MaxLenSVA  = 1'b1,
  // Can be disabled in cases where entropy
  // inputs are unused in order to not distort coverage
  // (the SVA will be unreachable in such cases)
  parameter bit                LockupSVA  = 1'b1
) (
  input                          clk_i,
  input                          rst_ni,
  input                          entropy_i,          // from TRNG
  input                          en_i,               // enable ping testing
  input        [NAlerts-1:0]     alert_ping_en_i,    // determines which alerts to ping
  input        [PING_CNT_DW-1:0] ping_timeout_cyc_i, // timeout in cycles
  input        [PING_CNT_DW-1:0] wait_cyc_mask_i,    // wait cycles mask
  output logic [NAlerts-1:0]     alert_ping_req_o,   // request to alert receivers
  output logic [N_ESC_SEV-1:0]   esc_ping_req_o,     // enable to esc senders
  input        [NAlerts-1:0]     alert_ping_ok_i,    // response from alert receivers
  input        [N_ESC_SEV-1:0]   esc_ping_ok_i,      // response from esc senders
  output logic                   alert_ping_fail_o,  // any of the alert receivers failed
  output logic                   esc_ping_fail_o     // any of the esc senders failed
);

  localparam int unsigned NModsToPing = NAlerts + N_ESC_SEV;
  localparam int unsigned IdDw        = $clog2(NModsToPing);

  //////////
  // PRNG //
  //////////

  logic lfsr_en;
  logic [31:0] lfsr_state;
  logic [16-IdDw-1:0] unused_lfsr_state;

  prim_lfsr #(
    .LfsrDw      ( 32              ),
    .EntropyDw   ( 1               ),
    .StateOutDw  ( 32              ),
    .DefaultSeed ( RndCnstLfsrSeed ),
    .StatePermEn ( 1'b1            ),
    .StatePerm   ( RndCnstLfsrPerm ),
    .MaxLenSVA   ( MaxLenSVA       ),
    .LockupSVA   ( LockupSVA       ),
    .ExtSeedSVA  ( 1'b0            ) // ext seed is unused
  ) i_prim_lfsr (
    .clk_i,
    .rst_ni,
    .seed_en_i  ( 1'b0       ),
    .seed_i     ( '0         ),
    .lfsr_en_i  ( lfsr_en    ),
    .entropy_i,
    .state_o    ( lfsr_state )
  );

  logic [IdDw-1:0] id_to_ping;
  logic [PING_CNT_DW-1:0] wait_cyc;
  // we only use bits up to 23, as IdDw is 8bit maximum
  assign id_to_ping = lfsr_state[16 +: IdDw];

  // to avoid lint warnings
  assign unused_lfsr_state = lfsr_state[31:16+IdDw];

  // concatenate with constant offset, introduce some stagger
  // by concatenating the lower bits below
  assign wait_cyc   = PING_CNT_DW'({lfsr_state[15:2], 8'h01, lfsr_state[1:0]}) & wait_cyc_mask_i;

  logic [2**IdDw-1:0] enable_mask;
  always_comb begin : p_enable_mask
    enable_mask                        = '0;         // tie off unused
    enable_mask[NAlerts-1:0]           = alert_ping_en_i; // alerts
    enable_mask[NModsToPing-1:NAlerts] = '1;         // escalation senders
  end

  logic id_vld;
  // check if the randomly drawn ID is actually valid and the alert is enabled
  assign id_vld  = enable_mask[id_to_ping];

  /////////////
  // Counter //
  /////////////

  logic [PING_CNT_DW-1:0] cnt_d, cnt_q;
  logic cnt_en, cnt_clr;
  logic wait_ge, timeout_ge;

  assign cnt_d      = cnt_q + 1'b1;
  assign wait_ge    = (cnt_q >= wait_cyc);
  assign timeout_ge = (cnt_q >= ping_timeout_cyc_i);

  ////////////////////////////
  // Ping and Timeout Logic //
  ////////////////////////////

  typedef enum logic [1:0] {Init, RespWait, DoPing} state_e;
  state_e state_d, state_q;
  logic ping_en, ping_ok;
  logic [NModsToPing-1:0] ping_sel;
  logic [NModsToPing-1:0] spurious_ping;
  logic spurious_alert_ping, spurious_esc_ping;

  // generate ping enable vector
  assign ping_sel        = NModsToPing'(ping_en) << id_to_ping;
  assign alert_ping_req_o = ping_sel[NAlerts-1:0];
  assign esc_ping_req_o   = ping_sel[NModsToPing-1:NAlerts];

  // mask out response
  assign ping_ok             = |({esc_ping_ok_i, alert_ping_ok_i} & ping_sel);
  assign spurious_ping       = ({esc_ping_ok_i, alert_ping_ok_i} & ~ping_sel);
  // under normal operation, these signals should never be asserted.
  // we place hand instantiated buffers here such that these signals are not
  // optimized away during synthesis (these buffers will receive a keep or size_only
  // attribute in our Vivado and DC synthesis flows).
  prim_buf u_prim_buf_spurious_alert_ping (
    .in_i(|spurious_ping[NAlerts-1:0]),
    .out_o(spurious_alert_ping)
  );
  prim_buf u_prim_buf_spurious_esc_ping (
    .in_i(|spurious_ping[NModsToPing-1:NAlerts]),
    .out_o(spurious_esc_ping)
  );

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
      // wait until activiated
      // we never return to this state
      // once activated!
      Init: begin
        cnt_clr = 1'b1;
        if (en_i) begin
          state_d = RespWait;
        end
      end
      // wait for random amount of cycles
      // draw another ID/wait count if the
      // peripheral ID is not valid
      RespWait: begin
        if (!id_vld) begin
          lfsr_en = 1'b1;
          cnt_clr = 1'b1;
        end else if (wait_ge) begin
          state_d = DoPing;
          cnt_clr = 1'b1;
        end else begin
          cnt_en = 1'b1;
        end
      end
      // send out ping request and wait for a ping
      // response or a ping timeout (whatever comes first)
      DoPing: begin
        cnt_en  = 1'b1;
        ping_en = 1'b1;
        if (timeout_ge || ping_ok) begin
          state_d = RespWait;
          lfsr_en = 1'b1;
          cnt_clr = 1'b1;
          if (timeout_ge) begin
            if (id_to_ping < IdDw'(NAlerts)) begin
              alert_ping_fail_o = 1'b1;
            end else begin
              esc_ping_fail_o   = 1'b1;
            end
          end
        end
      end
      // this should never happen
      // if we for some reason end up in this state (e.g. malicious glitching)
      // we are going to assert both ping fails continuously
      default: begin
        alert_ping_fail_o = 1'b1;
        esc_ping_fail_o   = 1'b1;
      end
    endcase
  end

  ///////////////
  // Registers //
  ///////////////

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      state_q <= Init;
      cnt_q   <= '0;
    end else begin
      state_q <= state_d;

      if (cnt_clr) begin
        cnt_q <= '0;
      end else if (cnt_en) begin
        cnt_q <= cnt_d;
      end
    end
  end

  ////////////////
  // Assertions //
  ////////////////

  // internals
  `ASSERT(PingOH0_A, $onehot0(ping_sel))
  // we should never get into the ping state without knowing
  // which module to ping
  `ASSERT(PingOH_A, ping_en |-> $onehot(ping_sel))

endmodule : alert_handler_ping_timer
