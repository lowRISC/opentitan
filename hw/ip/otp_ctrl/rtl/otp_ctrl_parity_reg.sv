// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Parity-protected register file for buffered OTP partitions.
//
// TODO: discuss whether reset is allowed here. We may also need a secure wiping feature.

`include "prim_assert.sv"

module otp_ctrl_parity_reg #(
  parameter  int Width = 32, // bit
  parameter  int Depth = 128,
  localparam int Aw    = prim_util_pkg::vbits(Depth) // derived parameter
) (
  input  logic                        clk_i,
  input  logic                        rst_ni,

  input  logic                        wren_i,
  input  logic [Aw-1:0]               addr_i,
  input  logic [Width-1:0]            wdata_i,

  // Concurrent output of the register state.
  output logic [Depth-1:0][Width-1:0] data_o,
  // Concurrent parity check error is flagged via this signal.
  output logic                        parity_err_o
);

  // Integration checks for parameters.
  `ASSERT_INIT(WidthMustBeByteAligned_A, Width % 8 == 0)

  logic [Depth-1:0][Width-1:0]   data_d, data_q;
  logic [Depth-1:0][Width/8-1:0] parity_d, parity_q;

  if (Depth == 1) begin : gen_one_word_only
    always_comb begin : p_write
      data_o = data_q;
      data_d = data_q;
      parity_d = parity_q;

      if (wren_i && 32'(addr_i) < Depth) begin
        data_d[0] = wdata_i;
        // Calculate EVEN parity bit for each Byte written.
        for (int k = 0; k < Width/8; k ++) begin
          parity_d[0][k] = ^wdata_i[k*8 +: 8];
        end
      end
    end
  end else begin : gen_multiple_words
    always_comb begin : p_write
      data_o = data_q;
      data_d = data_q;
      parity_d = parity_q;

      if (wren_i && 32'(addr_i) < Depth) begin
        data_d[addr_i] = wdata_i;
        // Calculate EVEN parity bit for each Byte written.
        for (int k = 0; k < Width/8; k ++) begin
          parity_d[addr_i][k] = ^wdata_i[k*8 +: 8];
        end
      end
    end
  end

  always_comb begin : p_parity
    // Concurrent parity check.
    parity_err_o = 1'b0;
    for (int j = 0; j < Depth; j ++) begin
      for (int k = 0; k < Width/8; k ++) begin
        parity_err_o |= ^{data_q[j][k*8 +: 8], parity_q[j][k]};
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      parity_q <= '0;
      data_q   <= '0;
    end else begin
      parity_q <= parity_d;
      data_q   <= data_d;
    end
  end

  `ASSERT_KNOWN(ParityKnown_A, parity_q)
  `ASSERT_KNOWN(DataKnown_A, data_q)

endmodule : otp_ctrl_parity_reg
