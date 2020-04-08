// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES counter for CTR mode
//
// This module uses a 16-bit counter to iteratively increment the 128-bit counter value.

`include "prim_assert.sv"

module aes_ctr(
  input  logic             clk_i,
  input  logic             rst_ni,

  input  logic             incr_i,
  output logic             ready_o,

  input  logic [7:0][15:0] ctr_i, // 8 times 2 bytes
  output logic [7:0][15:0] ctr_o, // 8 times 2 bytes
  output logic [7:0]       ctr_we_o
);

  // Reverse byte order
  function automatic logic [15:0][7:0] aes_rev_order_byte(logic [15:0][7:0] in);
    logic [15:0][7:0] out;
    for (int i=0; i<16; i++) begin
      out[i] = in[15-i];
    end
    return out;
  endfunction

  // Reverse bit order
  function automatic logic [7:0] aes_rev_order_bit(logic [7:0] in);
    logic [7:0] out;
    for (int i=0; i<8; i++) begin
      out[i] = in[7-i];
    end
    return out;
  endfunction

  // Types
  typedef enum logic {
    IDLE, INCR
  } aes_ctr_e;

  // Signals
  aes_ctr_e         aes_ctr_ns, aes_ctr_cs;
  logic       [2:0] ctr_slice_idx_d, ctr_slice_idx_q;
  logic             ctr_carry_d, ctr_carry_q;

  logic [7:0][15:0] ctr_i_rev; // 8 times 2 bytes
  logic [7:0][15:0] ctr_o_rev; // 8 times 2 bytes
  logic [7:0]       ctr_we_o_rev;
  logic             ctr_we;

  logic      [15:0] ctr_i_slice;
  logic      [15:0] ctr_o_slice;
  logic      [16:0] ctr_value;

  ////////////
  // Inputs //
  ////////////

  // Reverse byte order
  assign ctr_i_rev = aes_rev_order_byte(ctr_i);

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
    ready_o         = 1'b0;
    ctr_we          = 1'b0;

    // FSM
    aes_ctr_ns      = aes_ctr_cs;
    ctr_slice_idx_d = ctr_slice_idx_q;
    ctr_carry_d     = ctr_carry_q;

    unique case (aes_ctr_cs)
      IDLE: begin
        ready_o = 1'b1;
        if (incr_i) begin
          // Initialize slice index and carry bit.
          ctr_slice_idx_d = '0;
          ctr_carry_d     = 1'b1;
          aes_ctr_ns      = INCR;
        end
      end

      INCR: begin
        // Increment slice index.
        ctr_slice_idx_d = ctr_slice_idx_q + 3'b1;
        ctr_carry_d     = ctr_value[16];
        ctr_we          = 1'b1;

        if (ctr_slice_idx_q == 3'b111) begin
          aes_ctr_ns = IDLE;
        end
      end

      default: aes_ctr_ns = IDLE;
    endcase
  end

  // Registers
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      aes_ctr_cs      <= IDLE;
      ctr_slice_idx_q <= '0;
      ctr_carry_q     <= '0;
    end else begin
      aes_ctr_cs      <= aes_ctr_ns;
      ctr_slice_idx_q <= ctr_slice_idx_d;
      ctr_carry_q     <= ctr_carry_d;
    end
  end

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
    ctr_we_o_rev                  = '0;
    ctr_we_o_rev[ctr_slice_idx_q] = ctr_we;
  end

  // Reverse byte and bit order.
  assign ctr_o    = aes_rev_order_byte(ctr_o_rev);
  assign ctr_we_o = aes_rev_order_bit(ctr_we_o_rev);

  ////////////////
  // Assertions //
  ////////////////
  `ASSERT_KNOWN(AesCtrStateKnown, aes_ctr_cs)

endmodule
