// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES counter for CTR mode
//
// This module uses a 16-bit counter to iteratively increment the 128-bit counter value.

`include "prim_assert.sv"

module aes_ctr import aes_pkg::*;
(
  input  logic              clk_i,
  input  logic              rst_ni,

  input  sp2v_e             incr_i,
  output sp2v_e             ready_o,
  output logic              alert_o,

  input  logic  [7:0][15:0] ctr_i, // 8 times 2 bytes
  output logic  [7:0][15:0] ctr_o, // 8 times 2 bytes
  output sp2v_e [7:0]       ctr_we_o
);

  // Reverse byte order
  function automatic logic [15:0][7:0] aes_rev_order_byte(logic [15:0][7:0] in);
    logic [15:0][7:0] out;
    for (int i = 0; i < 16; i++) begin
      out[i] = in[15-i];
    end
    return out;
  endfunction

  // Reverse sp2v order
  function automatic sp2v_e [7:0] aes_rev_order_sp2v(sp2v_e [7:0] in);
    sp2v_e [7:0] out;
    for (int i = 0; i < 8; i++) begin
      out[i] = in[7-i];
    end
    return out;
  endfunction

  // Types
  // $ ./sparse-fsm-encode.py -d 3 -m 3 -n 5 \
  //      -s 31468618 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: |||||||||||||||||||| (66.67%)
  //  4: |||||||||| (33.33%)
  //  5: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 4
  //
  localparam int StateWidth = 5;
  typedef enum logic [StateWidth-1:0] {
    IDLE  = 5'b01110,
    INCR  = 5'b11000,
    ERROR = 5'b00001
  } aes_ctr_e;

  // Signals
  aes_ctr_e          aes_ctr_ns, aes_ctr_cs;
  logic        [2:0] ctr_slice_idx_d, ctr_slice_idx_q;
  logic              ctr_carry_d, ctr_carry_q;

  logic  [7:0][15:0] ctr_i_rev; // 8 times 2 bytes
  logic  [7:0][15:0] ctr_o_rev; // 8 times 2 bytes
  sp2v_e [7:0]       ctr_we_o_rev;
  sp2v_e             ctr_we;

  logic       [15:0] ctr_i_slice;
  logic       [15:0] ctr_o_slice;
  logic       [16:0] ctr_value;

  logic              alert;
  sp2v_e             incr;
  logic              incr_err_d, incr_err_q;

  ////////////
  // Inputs //
  ////////////

  // Reverse byte order
  assign ctr_i_rev = aes_rev_order_byte(ctr_i);

  // Check sparsely encoded incr signal.
  logic [Sp2VWidth-1:0] incr_raw;
  aes_sel_buf_chk #(
    .Num   ( Sp2VNum   ),
    .Width ( Sp2VWidth )
  ) u_aes_sb_en_buf_chk (
    .clk_i  ( clk_i      ),
    .rst_ni ( rst_ni     ),
    .sel_i  ( incr_i     ),
    .sel_o  ( incr_raw   ),
    .err_o  ( incr_err_d )
  );
  assign incr = sp2v_e'(incr_raw);

  // Need to register errors in incr to avoid circular loops in the main
  // controller related to start.
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_out_ack_err
    if (!rst_ni) begin
      incr_err_q <= 1'b0;
    end else if (incr_err_d) begin
      incr_err_q <= 1'b1;
    end
  end

  /////////////
  // Counter //
  /////////////

  // We do 16 bits at a time.
  assign ctr_i_slice = ctr_i_rev[ctr_slice_idx_q];
  assign ctr_value   = ctr_i_slice + {15'b0, ctr_carry_q};
  assign ctr_o_slice = ctr_value[15:0];

  /////////////
  // Control //
  /////////////

  // FSM
  always_comb begin : aes_ctr_fsm

    // Outputs
    ready_o         = SP2V_LOW;
    ctr_we          = SP2V_LOW;
    alert           = 1'b0;

    // FSM
    aes_ctr_ns      = aes_ctr_cs;
    ctr_slice_idx_d = ctr_slice_idx_q;
    ctr_carry_d     = ctr_carry_q;

    unique case (aes_ctr_cs)
      IDLE: begin
        ready_o = SP2V_HIGH;
        if (incr == SP2V_HIGH) begin
          // Initialize slice index and carry bit.
          ctr_slice_idx_d = '0;
          ctr_carry_d     = 1'b1;
          aes_ctr_ns      = INCR;
        end
      end

      INCR: begin
        // Increment slice index.
        ctr_slice_idx_d = ctr_slice_idx_q + 3'b001;
        ctr_carry_d     = ctr_value[16];
        ctr_we          = SP2V_HIGH;

        if (ctr_slice_idx_q == 3'b111) begin
          aes_ctr_ns = IDLE;
        end
      end

      ERROR: begin
        // Terminal error state
        alert = 1'b1;
      end

      // We should never get here. If we do (e.g. via a malicious
      // glitch), error out immediately.
      default: begin
        aes_ctr_ns = ERROR;
      end
    endcase
  end

  // Registers
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ctr_slice_idx_q <= '0;
      ctr_carry_q     <= '0;
    end else begin
      ctr_slice_idx_q <= ctr_slice_idx_d;
      ctr_carry_q     <= ctr_carry_d;
    end
  end

  // This primitive is used to place a size-only constraint on the
  // flops in order to prevent FSM state encoding optimizations.
  logic [StateWidth-1:0] aes_ctr_cs_raw;
  assign aes_ctr_cs = aes_ctr_e'(aes_ctr_cs_raw);
  prim_flop #(
    .Width(StateWidth),
    .ResetValue(StateWidth'(IDLE))
  ) u_state_regs (
    .clk_i,
    .rst_ni,
    .d_i ( aes_ctr_ns     ),
    .q_o ( aes_ctr_cs_raw )
  );

  /////////////
  // Outputs //
  /////////////

  // Combine input and counter output.
  always_comb begin
    ctr_o_rev                  = ctr_i_rev;
    ctr_o_rev[ctr_slice_idx_q] = ctr_o_slice;
  end

  // Generate the sliced write enable.
  always_comb begin
    ctr_we_o_rev                  = {8{SP2V_LOW}};
    ctr_we_o_rev[ctr_slice_idx_q] = ctr_we;
  end

  // Reverse byte and bit order.
  assign ctr_o    = aes_rev_order_byte(ctr_o_rev);
  assign ctr_we_o = aes_rev_order_sp2v(ctr_we_o_rev);

  // Collect alert signals.
  assign alert_o  = alert | incr_err_q;

  ////////////////
  // Assertions //
  ////////////////
  `ASSERT(AesCtrStateValid, !alert_o |-> aes_ctr_cs inside {
      IDLE,
      INCR
      })

endmodule
