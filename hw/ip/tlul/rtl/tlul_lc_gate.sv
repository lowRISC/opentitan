// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Life cycle gating module for TL-UL protocol.
// Transactions are passed through when lc_en_i == ON.
// In all other cases (lc_en_i != ON) incoming transactions return a bus error.
//
// Note that the lc_en_i should be synchronized and buffered outside of this module using
// an instance of prim_lc_sync.

module tlul_lc_gate
  import tlul_pkg::*;
  import lc_ctrl_pkg::*;
#(
  // Number of LC gating muxes in each direction.
  // It is recommended to set this parameter to 2, which results
  // in a total of 4 gating muxes.
  parameter int NumGatesPerDirection = 2
) (
  input clk_i,
  input rst_ni,

  // To host
  input  tl_h2d_t tl_h2d_i,
  output tl_d2h_t tl_d2h_o,

  // To device
  output tl_h2d_t tl_h2d_o,
  input  tl_d2h_t tl_d2h_i,

  // Flush control signaling
  input flush_req_i,
  output logic flush_ack_o,

  // Indicates whether there are pending responses on the device side.
  output logic resp_pending_o,

  // LC control signal
  input  lc_tx_t  lc_en_i,
  output logic err_o
);

  //////////////////
  // Access Gates //
  //////////////////

  lc_tx_t err_en;
  lc_tx_t [NumGatesPerDirection-1:0] err_en_buf;

  prim_lc_sync #(
    .NumCopies(NumGatesPerDirection),
    .AsyncOn(0)
  ) u_err_en_sync (
    .clk_i,
    .rst_ni,
    .lc_en_i(err_en),
    .lc_en_o(err_en_buf)
  );

  tl_h2d_t tl_h2d_int [NumGatesPerDirection+1];
  tl_d2h_t tl_d2h_int [NumGatesPerDirection+1];
  for (genvar k = 0; k < NumGatesPerDirection; k++) begin : gen_lc_gating_muxes
    // H -> D path.
    prim_blanker #(
      .Width($bits(tl_h2d_t))
    ) u_prim_blanker_h2d (
      .in_i(tl_h2d_int[k]),
      .en_i(lc_tx_test_false_strict(err_en_buf[k])),
      .out_o(tl_h2d_int[k+1])
    );

    // D -> H path.
    prim_blanker #(
      .Width($bits(tl_d2h_t))
    ) u_prim_blanker_d2h (
      .in_i(tl_d2h_int[k+1]),
      .en_i(lc_tx_test_false_strict(err_en_buf[k])),
      .out_o(tl_d2h_int[k])
    );
  end

  // Assign signals on the device side.
  assign tl_h2d_o = tl_h2d_int[NumGatesPerDirection];
  assign tl_d2h_int[NumGatesPerDirection] = tl_d2h_i;

  ///////////////////////////
  // Host Side Interposing //
  ///////////////////////////

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 5 -m 4 -n 8 \
  //      -s 3379253306 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: |||||||||||||||||||| (66.67%)
  //  6: |||||||||| (33.33%)
  //  7: --
  //  8: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 6
  // Minimum Hamming weight: 3
  // Maximum Hamming weight: 5
  //
  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 5 -m 5 -n 9 \
  //      -s 686407169 --language=sv
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
  // Minimum Hamming weight: 3
  // Maximum Hamming weight: 6
  //
  localparam int StateWidth = 9;
  typedef enum logic [StateWidth-1:0] {
    StActive = 9'b100100001,
    StOutstanding = 9'b011100111,
    StFlush = 9'b001001100,
    StError = 9'b010111010,
    StErrorOutstanding = 9'b100010110
  } state_e;

  state_e state_d, state_q;
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, state_e, StError)

  logic [1:0] outstanding_txn;
  logic a_ack;
  logic d_ack;
  assign a_ack = tl_h2d_i.a_valid & tl_d2h_o.a_ready;
  assign d_ack = tl_h2d_i.d_ready & tl_d2h_o.d_valid;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      outstanding_txn <= '0;
    end else if (a_ack && !d_ack) begin
      outstanding_txn <= outstanding_txn + 1'b1;
    end else if (d_ack && !a_ack) begin
      outstanding_txn <= outstanding_txn - 1'b1;
    end
  end

  logic block_cmd;
  always_comb begin
    block_cmd = '0;
    state_d = state_q;
    err_en = Off;
    err_o = '0;
    flush_ack_o = '0;
    resp_pending_o = 1'b0;

    unique case (state_q)
      StActive: begin
        if (lc_tx_test_false_loose(lc_en_i) || flush_req_i) begin
          state_d = StOutstanding;
        end
        if (outstanding_txn != '0) begin
          resp_pending_o = 1'b1;
        end
      end

      StOutstanding: begin
        block_cmd = 1'b1;
        if (outstanding_txn == '0) begin
          state_d = lc_tx_test_false_loose(lc_en_i) ? StError : StFlush;
        end else begin
          resp_pending_o = 1'b1;
        end
      end

      StFlush: begin
        block_cmd = 1'b1;
        flush_ack_o = 1'b1;
        if (lc_tx_test_false_loose(lc_en_i)) begin
          state_d = StError;
        end else if (!flush_req_i) begin
          state_d = StActive;
        end
      end

      StError: begin
        err_en = On;
        if (lc_tx_test_true_strict(lc_en_i)) begin
          state_d = StErrorOutstanding;
        end
      end

      StErrorOutstanding: begin
        err_en = On;
        block_cmd = 1'b1;
        if (outstanding_txn == '0) begin
          state_d = StActive;
        end
      end

      default: begin
        err_o = 1'b1;
        err_en = On;
      end

    endcase // unique case (state_q)
  end


  // At the host side, we interpose the ready / valid signals so that we can return a bus error
  // in case the lc signal is not set to ON. Note that this logic does not have to be duplicated
  // since erroring back is considered a convenience feature so that the bus does not lock up.
  tl_h2d_t tl_h2d_error;
  tl_d2h_t tl_d2h_error;
  always_comb begin
    tl_h2d_int[0] = tl_h2d_i;
    tl_d2h_o      = tl_d2h_int[0];
    tl_h2d_error  = '0;

    if (lc_tx_test_true_loose(err_en)) begin
      tl_h2d_error  = tl_h2d_i;
      tl_d2h_o      = tl_d2h_error;
    end

    if (block_cmd) begin
      tl_d2h_o.a_ready = 1'b0;
      tl_h2d_int[0].a_valid = 1'b0;
      tl_h2d_error.a_valid = 1'b0;
    end
  end

  tlul_err_resp u_tlul_err_resp (
    .clk_i,
    .rst_ni,
    .tl_h_i(tl_h2d_error),
    .tl_h_o(tl_d2h_error)
  );

  // Add assertion
  `ASSERT(OutStandingOvfl_A, &outstanding_txn |-> ~a_ack)

endmodule : tlul_lc_gate
