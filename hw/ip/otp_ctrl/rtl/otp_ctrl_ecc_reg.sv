// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Register file for buffered OTP partitions. ECC is used to detect up
// to two simultaneous errors within each 64bit word.

`include "prim_assert.sv"

module otp_ctrl_ecc_reg #(
  parameter  int Width = 64, // bit
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
  // Concurrent ECC check error is flagged via this signal.
  output logic                        ecc_err_o
);

  // Integration checks for parameters.
  `ASSERT_INIT(WidthMustBe64bit_A, Width == 64)

  localparam int EccWidth = 8;

  logic [Depth-1:0][Width-1:0] data_d, data_q;
  logic [Depth-1:0][EccWidth-1:0] ecc_d, ecc_q;
  logic [Width+EccWidth-1:0] ecc_enc;

  // Only one encoder is needed.
  prim_secded_inv_72_64_enc u_prim_secded_inv_72_64_enc (
    .data_i(wdata_i),
    .data_o(ecc_enc)
  );

  if (Depth == 1) begin : gen_one_word_only
    always_comb begin : p_write
      data_o = data_q;
      data_d = data_q;
      ecc_d  = ecc_q;

      if (wren_i && 32'(addr_i) < Depth) begin
        {ecc_d[0], data_d[0]} = ecc_enc;
      end
    end
  end else begin : gen_multiple_words
    always_comb begin : p_write
      data_o = data_q;
      data_d = data_q;
      ecc_d  = ecc_q;

      if (wren_i && 32'(addr_i) < Depth) begin
        {ecc_d[addr_i], data_d[addr_i]} = ecc_enc;
      end
    end
  end

  // Concurrent ECC checks.
  logic [Depth-1:0][1:0] err;
  for (genvar k = 0; k < Depth; k++) begin : gen_ecc_dec
    prim_secded_inv_72_64_dec u_prim_secded_inv_72_64_dec (
      .data_i({ecc_q[k], data_q[k]}),
      // We only rely on the error detection mechanism,
      // and not on error correction.
      .data_o(),
      .syndrome_o(),
      .err_o(err[k])
    );
  end

  assign ecc_err_o = |err;

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      ecc_q  <= {Depth{prim_secded_pkg::SecdedInv7264ZeroEcc}};
      data_q <= '0;
    end else begin
      ecc_q  <= ecc_d;
      data_q <= data_d;
    end
  end

  `ASSERT_KNOWN(EccKnown_A,     ecc_q)
  `ASSERT_KNOWN(DataKnown_A,    data_q)
  `ASSERT_KNOWN(DataOutKnown_A, data_o)
  `ASSERT_KNOWN(EccErrKnown_A,  ecc_err_o)

endmodule : otp_ctrl_ecc_reg
