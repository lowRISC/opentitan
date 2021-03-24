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

module flash_phy_scramble import flash_phy_pkg::*; (
  input clk_i,
  input rst_ni,
  input calc_req_i, // calculate galois multiplier mask
  input op_req_i,   // request primitive operation
  input cipher_ops_e op_type_i,  // sramble or de-scramble
  input [BankAddrW-1:0] addr_i,
  input [DataWidth-1:0] plain_data_i,
  input [DataWidth-1:0] scrambled_data_i,
  input [KeySize-1:0] addr_key_i,
  input [KeySize-1:0] data_key_i,
  output logic calc_ack_o,
  output logic op_ack_o,
  output logic [DataWidth-1:0] mask_o,
  output logic [DataWidth-1:0] plain_data_o,
  output logic [DataWidth-1:0] scrambled_data_o
);

  localparam int AddrPadWidth = DataWidth - BankAddrW;
  localparam int UnusedWidth = KeySize - AddrPadWidth;

  // unused portion of addr_key
  logic [UnusedWidth-1:0] unused_key;
  assign unused_key = addr_key_i[KeySize-1 -: UnusedWidth];

  // Galois Multiply portion
  prim_gf_mult # (
    .Width(DataWidth),
    .StagesPerCycle(DataWidth / GfMultCycles)
  ) u_mult (
    .clk_i,
    .rst_ni,
    .req_i(calc_req_i),
    .operand_a_i({addr_key_i[DataWidth +: AddrPadWidth], addr_i}),
    .operand_b_i(addr_key_i[DataWidth-1:0]),
    .ack_o(calc_ack_o),
    .prod_o(mask_o)
  );

  // Cipher portion
  logic dec;
  logic [DataWidth-1:0] data;

  assign dec = op_type_i == DeScrambleOp;

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
    .valid_i(op_req_i),
    .data_i(dec ? scrambled_data_i : plain_data_i),
    .key_i(data_key_i),
    .dec_i(dec),
    .data_o(data),
    .valid_o(op_ack_o)
  );

  // if decrypt, output the unscrambled data, feed input through otherwise
  assign plain_data_o = dec ? data : scrambled_data_i;

  // if encrypt, output the scrambled data, feed input through otherwise
  assign scrambled_data_o = dec ? plain_data_i : data;


endmodule // flash_phy_scramble
