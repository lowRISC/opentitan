// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Flash Phy Scramble Module
//
// This module implements the flash scramble / de-scramble operation
// This operation is actually XEX.  However the components are broken
// in two and separately manipulated by the program and read pipelines.
//

module flash_phy_scramble import flash_phy_pkg::*; #(
  parameter bit SecScrambleEn = 1'b1
) (
  input clk_i,
  input rst_ni,
  input disable_i,
  input calc_req_i, // calculate galois multiplier mask
  input op_req_i,   // request primitive operation
  input cipher_ops_e op_type_i,  // sramble or de-scramble
  input [BankAddrW-1:0] addr_i,
  input [DataWidth-1:0] plain_data_i,
  input [DataWidth-1:0] scrambled_data_i,
  input [KeySize-1:0] addr_key_i,
  input [KeySize-1:0] data_key_i,
  input [KeySize-1:0] rand_addr_key_i,
  input [KeySize-1:0] rand_data_key_i,
  output logic calc_ack_o,
  output logic op_ack_o,
  output logic [DataWidth-1:0] mask_o,
  output logic [DataWidth-1:0] plain_data_o,
  output logic [DataWidth-1:0] scrambled_data_o
);

  localparam int AddrPadWidth = DataWidth - BankAddrW;
  localparam int UnusedWidth = KeySize - AddrPadWidth;

  // unused portion of addr_key
  logic [KeySize-1:0] muxed_addr_key;

  logic addr_key_sel;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      addr_key_sel <= '0;
    end else if (!calc_req_i || calc_req_i && calc_ack_o) begin
      addr_key_sel <= disable_i;
    end
  end

  assign muxed_addr_key = addr_key_sel ? rand_addr_key_i : addr_key_i;

  logic [UnusedWidth-1:0] unused_key;
  assign unused_key = muxed_addr_key[KeySize-1 -: UnusedWidth];

  // Galois Multiply portion
  if (SecScrambleEn) begin : gen_gf_mult
    prim_gf_mult # (
      .Width(DataWidth),
      .StagesPerCycle(DataWidth / GfMultCycles)
    ) u_mult (
      .clk_i,
      .rst_ni,
      .req_i(calc_req_i),
      .operand_a_i({muxed_addr_key[DataWidth +: AddrPadWidth], addr_i}),
      .operand_b_i(muxed_addr_key[DataWidth-1:0]),
      .ack_o(calc_ack_o),
      .prod_o(mask_o)
    );
  end else begin : gen_no_gf_mult
    assign mask_o = '0;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        calc_ack_o <= '0;
      end else if (calc_req_i && calc_ack_o) begin
        calc_ack_o <= '0;
      end else if (calc_req_i && !calc_ack_o) begin
        calc_ack_o <= '1;
      end
    end
  end


  // Cipher portion
  logic dec;
  logic [DataWidth-1:0] data;
  assign dec = op_type_i == DeScrambleOp;

  // Do not allow the key to change during a transaction.
  // While this may be desirable for security reasons, it creates
  // timing issues for physical design
  logic data_key_sel;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      data_key_sel <= '0;
    end else if (!op_req_i || op_req_i && op_ack_o) begin
      data_key_sel <= disable_i;
    end
  end

  // the prim_prince valid_o is a flopped version of valid_i
  // As a result, when op_req_i stays high due to multiple transactions
  // in-flight, the receiving logic can misinterpret the 'ack' if we just
  // tie it to valid_o.
  // Add a little bit of shimming logic here to properly create the ack
  logic cipher_valid_in_d, cipher_valid_in_q;
  logic cipher_valid_out;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cipher_valid_in_q <= '0;
    end else begin
      cipher_valid_in_q <= cipher_valid_in_d;
    end
  end

  assign cipher_valid_in_d = op_ack_o ? '0 : op_req_i & !cipher_valid_out;
  assign op_ack_o = cipher_valid_in_q & cipher_valid_out;

  if (SecScrambleEn) begin : gen_prince
    prim_prince # (
      .DataWidth(DataWidth),
      .KeyWidth(KeySize),
      // Use improved key schedule proposed by https://eprint.iacr.org/2014/656.pdf (see appendix).
      .UseOldKeySched(1'b0),
      .HalfwayDataReg(1'b1),
      // No key register is needed half way, since the data_key_i and operation op_type_i inputs
      // remain constant until one data block has been processed.
      .HalfwayKeyReg (1'b0)
    ) u_cipher (
      .clk_i,
      .rst_ni,
      .valid_i(cipher_valid_in_d),
      .data_i(dec ? scrambled_data_i : plain_data_i),
      .key_i(data_key_sel ? rand_data_key_i : data_key_i),
      .dec_i(dec),
      .data_o(data),
      .valid_o(cipher_valid_out)
    );

  end else begin : gen_no_prince
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        cipher_valid_out <= '0;
      end else begin
        cipher_valid_out <= cipher_valid_in_d;
      end
    end
    assign data = dec ? scrambled_data_i : plain_data_i;
  end

  // if decrypt, output the unscrambled data, feed input through otherwise
  assign plain_data_o = dec ? data : scrambled_data_i;

  // if encrypt, output the scrambled data, feed input through otherwise
  assign scrambled_data_o = dec ? plain_data_i : data;



endmodule // flash_phy_scramble
