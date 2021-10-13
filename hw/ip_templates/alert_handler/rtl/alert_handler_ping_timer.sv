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
  input                            clk_i,
  input                            rst_ni,
  output logic                     edn_req_o,          // request to EDN
  input                            edn_ack_i,          // ack from EDN
  input        [LfsrWidth-1:0]     edn_data_i,         // from EDN
  input                            en_i,               // enable ping testing
  input        [NAlerts-1:0]       alert_ping_en_i,    // determines which alerts to ping
  input        [PING_CNT_DW-1:0]   ping_timeout_cyc_i, // timeout in cycles
  input        [PING_CNT_DW-1:0]   wait_cyc_mask_i,    // mask to shorten the counters in DV / FPV
  output logic [NAlerts-1:0]       alert_ping_req_o,   // request to alert receivers
  output logic [N_ESC_SEV-1:0]     esc_ping_req_o,     // enable to esc senders
  input        [NAlerts-1:0]       alert_ping_ok_i,    // response from alert receivers
  input        [N_ESC_SEV-1:0]     esc_ping_ok_i,      // response from esc senders
  output logic                     alert_ping_fail_o,  // any of the alert receivers failed
  output logic                     esc_ping_fail_o     // any of the esc senders failed
);

  localparam int unsigned IdDw = $clog2(NAlerts);

  // Entropy reseeding is triggered every time this counter expires.
  // The expected wait time between pings is 2**(PING_CNT_DW-1) on average.
  // We do not need to reseed the LFSR very often, and the constant below is chosen
  // such that on average the LFSR is reseeded every 16th ping.
  localparam int unsigned ReseedLfsrExtraBits = 3;
  localparam int unsigned ReseedLfsrWidth = PING_CNT_DW + ReseedLfsrExtraBits;

  ////////////////////
  // Reseed counter //
  ////////////////////

  logic reseed_en;
  logic [ReseedLfsrWidth-1:0] reseed_timer_d, reseed_timer_q;

  assign reseed_timer_d = (reseed_timer_q > '0) ? reseed_timer_q - 1'b1        :
                          (reseed_en)           ? {wait_cyc_mask_i,
                                                  {ReseedLfsrExtraBits{1'b1}}} : '0;
  assign edn_req_o = (reseed_timer_q == '0);
  assign reseed_en = edn_req_o & edn_ack_i;

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      reseed_timer_q <= '0;
    end else begin
      reseed_timer_q <= reseed_timer_d;
    end
  end

  ///////////////////////////
  // Tandem LFSR Instances //
  ///////////////////////////

  logic lfsr_en, lfsr_en_unbuf;
  logic [LfsrWidth-1:0] entropy_unbuf;
  logic [1:0][LfsrWidth-1:0] lfsr_state;

  assign lfsr_en_unbuf = reseed_en | lfsr_en;
  assign entropy_unbuf = (reseed_en) ? edn_data_i[LfsrWidth-1:0] : '0;

  // We employ two redundant LFSRs to guard against FI attacks.
  // If any of the two is glitched and the two LFSR states do not agree,
  // the FSM below is moved into a terminal error state and all ping alerts
  // are permanently asserted.
  for (genvar k = 0; k < 2; k++) begin : gen_double_lfsr
    // Instantiate size_only buffers to prevent
    // optimization / merging of redundant logic.
    logic lfsr_en_buf;
    logic [LfsrWidth-1:0] entropy_buf, lfsr_state_unbuf;
    prim_buf #(
      .Width(LfsrWidth)
    ) u_prim_buf_entropy (
      .in_i(entropy_unbuf),
      .out_o(entropy_buf)
    );

    prim_buf u_prim_buf_lfsr_en (
      .in_i(lfsr_en_unbuf),
      .out_o(lfsr_en_buf)
    );

    prim_buf #(
      .Width(LfsrWidth)
    ) u_prim_buf_state (
      .in_i(lfsr_state_unbuf),
      .out_o(lfsr_state[k])
    );

    prim_lfsr #(
      .LfsrDw      ( LfsrWidth       ),
      .EntropyDw   ( LfsrWidth       ),
      .StateOutDw  ( LfsrWidth       ),
      .DefaultSeed ( RndCnstLfsrSeed ),
      .StatePermEn ( 1'b1            ),
      .StatePerm   ( RndCnstLfsrPerm ),
      .MaxLenSVA   ( MaxLenSVA       ),
      .LockupSVA   ( LockupSVA       ),
      .ExtSeedSVA  ( 1'b0            ) // ext seed is unused
    ) u_prim_lfsr (
      .clk_i,
      .rst_ni,
      .seed_en_i  ( 1'b0             ),
      .seed_i     ( '0               ),
      .lfsr_en_i  ( lfsr_en_buf      ),
      .entropy_i  ( entropy_buf      ),
      .state_o    ( lfsr_state_unbuf )
    );
  end

  logic [IdDw-1:0] id_to_ping;
  assign id_to_ping = lfsr_state[0][PING_CNT_DW +: IdDw];

  // align the enable mask with powers of two for the indexing operation below.
  logic [2**IdDw-1:0] enable_mask;
  assign enable_mask = (2**IdDw)'(alert_ping_en_i);

  // check if the randomly drawn alert ID is actually valid and the alert is enabled
  logic id_vld;
  assign id_vld = enable_mask[id_to_ping];

  //////////////////////////////////
  // Escalation Counter Instances //
  //////////////////////////////////

  // As opposed to the alert ID, the escalation sender ID to be pinged is not drawn at random.
  // Rather, we cycle through the escalation senders one by one in a deterministic fashion.
  // This allows us to provide guarantees needed for the ping timeout / auto escalation feature
  // implemented at the escalation receiver side.
  //
  // In particular, with N_ESC_SEV escalation senders in the design, we can guarantee
  // that each escalation channel will be pinged at least once every
  //
  // N_ESC_SEV x (NUM_WAIT_COUNT + NUM_TIMEOUT_COUNT) x 2**PING_CNT_DW
  //
  // cycles - independently of the reseeding operation.
  //
  // - N_ESC_SEV: # escalation channels to ping.
  // - NUM_WAIT_COUNT: # wait counts between subsequent escalation channel pings.
  // - NUM_TIMEOUT_COUNT: # timeout counts between subsequent escalation channel pings.
  // - 2**PING_CNT_DW: # maximum counter value.
  //
  // This guarantee is used inside the escalation receivers to monitor the pings sent out by the
  // alert handler. I.e., once the alert handler has started to send out pings, each escalation
  // receiver employs a timeout window within which it expects the next ping to arrive. If
  // escalation pings cease to arrive at an escalation receiver for any reason, this will
  // automatically trigger the associated escalation countermeasure.
  //
  // In order to have enough margin, the escalation receiver timeout counters use a threshold that
  // is 4x higher than the value calculated above. With N_ESC_SEV = 4, PING_CNT_DW = 16 and
  // NUM_WAIT_COUNT = NUM_TIMEOUT_COUNT = 2 this amounts to a 22bit timeout threshold.

  logic esc_cnt_en;
  logic [1:0][PING_CNT_DW-1:0] esc_cnt_q;

  // We employ two redundant counters to guard against FI attacks.
  // If any of the two is glitched and the two counter states do not agree,
  // the FSM below is moved into a terminal error state and all ping alerts
  // are permanently asserted.
  for (genvar k = 0; k < 2; k++) begin : gen_double_esc_cnt

    logic [PING_CNT_DW-1:0] esc_cnt_d;
    assign esc_cnt_d = (esc_cnt_q[k] >= PING_CNT_DW'(N_ESC_SEV-1)) ? '0 : (esc_cnt_q[k] + 1'b1);

    prim_flop_en #(
      .Width(PING_CNT_DW)
    ) u_prim_flop_en (
      .clk_i,
      .rst_ni,
      .en_i  ( esc_cnt_en   ),
      .d_i   ( esc_cnt_d    ),
      .q_o   ( esc_cnt_q[k] )
    );
  end

  /////////////////////////////
  // Timer Counter Instances //
  /////////////////////////////

  logic [1:0][PING_CNT_DW-1:0] cnt_q;
  logic wait_cnt_load, timeout_cnt_load, timer_expired;
  assign timer_expired = (cnt_q[0] == '0);
  assign lfsr_en = wait_cnt_load || timeout_cnt_load;

  // We employ two redundant counters to guard against FI attacks.
  // If any of the two is glitched and the two counter states do not agree,
  // the FSM below is moved into a terminal error state and all ping alerts
  // are permanently asserted.
  for (genvar k = 0; k < 2; k++) begin : gen_double_cnt

    // the constant offset ensures a minimum cycle spacing between pings.
    logic [PING_CNT_DW-1:0] wait_cyc;
    assign wait_cyc = (lfsr_state[k][PING_CNT_DW-1:0] | PING_CNT_DW'(3'b100));

    // note that the masks are used for DV/FPV only in order to reduce the state space.
    logic [PING_CNT_DW-1:0] cnt_d;
    assign cnt_d = (wait_cnt_load)    ? (wait_cyc & wait_cyc_mask_i) :
                   (timeout_cnt_load) ? (ping_timeout_cyc_i)         :
                   (cnt_q[k] > '0)    ? cnt_q[k] - 1'b1              : '0;

    prim_flop #(
      .Width(PING_CNT_DW)
    ) u_prim_flop (
      .clk_i,
      .rst_ni,
      .d_i   ( cnt_d    ),
      .q_o   ( cnt_q[k] )
    );
  end

  ////////////////////////////
  // Ping and Timeout Logic //
  ////////////////////////////

  logic alert_ping_en, esc_ping_en;
  logic spurious_alert_ping, spurious_esc_ping;

  // generate ping enable vector
  assign alert_ping_req_o = NAlerts'(alert_ping_en) << id_to_ping;
  assign esc_ping_req_o   = N_ESC_SEV'(esc_ping_en) << esc_cnt_q[0];

  // under normal operation, these signals should never be asserted.
  // we place hand instantiated buffers here such that these signals are not
  // optimized away during synthesis (these buffers will receive a keep or size_only
  // attribute in our Vivado and DC synthesis flows).
  prim_buf u_prim_buf_spurious_alert_ping (
    .in_i(|(alert_ping_ok_i & ~alert_ping_req_o)),
    .out_o(spurious_alert_ping)
  );
  prim_buf u_prim_buf_spurious_esc_ping (
    .in_i(|(esc_ping_ok_i & ~esc_ping_req_o)),
    .out_o(spurious_esc_ping)
  );

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 5 -m 6 -n 9 \
  //      -s 728582219 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: |||||||||||||||||||| (60.00%)
  //  6: ||||||||||||| (40.00%)
  //  7: --
  //  8: --
  //  9: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 6
  // Minimum Hamming weight: 2
  // Maximum Hamming weight: 6
  //
  localparam int StateWidth = 9;
  typedef enum logic [StateWidth-1:0] {
    InitSt      = 9'b000101100,
    AlertWaitSt = 9'b011001011,
    AlertPingSt = 9'b110000000,
    EscWaitSt   = 9'b101110001,
    EscPingSt   = 9'b011110110,
    FsmErrorSt  = 9'b100011111
  } state_e;

  state_e state_d, state_q;

  always_comb begin : p_fsm
    // default
    state_d          = state_q;
    wait_cnt_load    = 1'b0;
    timeout_cnt_load = 1'b0;
    esc_cnt_en       = 1'b0;
    alert_ping_en    = 1'b0;
    esc_ping_en      = 1'b0;
    // this captures spurious ping responses
    alert_ping_fail_o = spurious_alert_ping;
    esc_ping_fail_o   = spurious_esc_ping;

    unique case (state_q)
      // wait until activated
      // we never return to this state
      // once activated!
      InitSt: begin
        if (en_i) begin
          state_d = AlertWaitSt;
          wait_cnt_load = 1'b1;
        end
      end
      // wait for random amount of cycles
      AlertWaitSt: begin
        if (timer_expired) begin
          state_d = AlertPingSt;
          timeout_cnt_load = 1'b1;
        end
      end
      // send out an alert ping request and wait for a ping
      // response or a ping timeout (whatever comes first).
      // if the alert ID is not valid, we drop the request and
      // proceed to the next ping.
      AlertPingSt: begin
        alert_ping_en = id_vld;
        if (timer_expired || |(alert_ping_ok_i & alert_ping_req_o) || !id_vld) begin
          state_d           = EscWaitSt;
          wait_cnt_load     = 1'b1;
          if (timer_expired) begin
            alert_ping_fail_o = 1'b1;
          end
        end
      end
      // wait for random amount of cycles
      EscWaitSt: begin
        if (timer_expired) begin
          state_d          = EscPingSt;
          timeout_cnt_load = 1'b1;
        end
      end
      // send out an escalation ping request and wait for a ping
      // response or a ping timeout (whatever comes first)
      EscPingSt: begin
        esc_ping_en = 1'b1;
        if (timer_expired || |(esc_ping_ok_i & esc_ping_req_o)) begin
          state_d         = AlertWaitSt;
          wait_cnt_load   = 1'b1;
          esc_cnt_en      = 1'b1;
          if (timer_expired) begin
            esc_ping_fail_o = 1'b1;
          end
        end
      end
      // terminal FSM error state.
      // if we for some reason end up in this state (e.g. malicious glitching)
      // we are going to assert both ping fails continuously
      FsmErrorSt: begin
        alert_ping_fail_o = 1'b1;
        esc_ping_fail_o   = 1'b1;
      end
      default: begin
        state_d = FsmErrorSt;
      end
    endcase

    // if the two LFSR or counter states do not agree,
    // we move into the terminal state.
    if (lfsr_state[0] != lfsr_state[1] ||
        cnt_q[0]      != cnt_q[1]      ||
        esc_cnt_q[0]  != esc_cnt_q[1]) begin
       state_d = FsmErrorSt;
    end
  end

  ///////////////////
  // FSM Registers //
  ///////////////////

  // This primitive is used to place a size-only constraint on the
  // flops in order to prevent FSM state encoding optimizations.
  logic [StateWidth-1:0] state_raw_q;
  assign state_q = state_e'(state_raw_q);

  prim_flop #(
    .Width(StateWidth),
    .ResetValue(StateWidth'(InitSt))
  ) u_state_regs (
    .clk_i,
    .rst_ni,
    .d_i ( state_d     ),
    .q_o ( state_raw_q )
  );

  ////////////////
  // Assertions //
  ////////////////

  // make sure the ID width is within bounds.
  `ASSERT_INIT(MaxIdDw_A, IdDw <= (LfsrWidth - PING_CNT_DW))

  // only one module is pinged at a time.
  `ASSERT(PingOH0_A, $onehot0({alert_ping_req_o, esc_ping_req_o}))

  // we should never get into the ping state without knowing which module to ping.
  `ASSERT(AlertPingOH_A, alert_ping_en |-> $onehot(alert_ping_req_o))
  `ASSERT(EscPingOH_A, esc_ping_en |-> $onehot(esc_ping_req_o))

endmodule : alert_handler_ping_timer
