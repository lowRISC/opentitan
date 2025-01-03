// Copyright lowRISC contributors (OpenTitan project).
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
  input [KeySize-1:0] addr_key_i,
  input [KeySize-1:0] data_key_i,
  input [KeySize-1:0] rand_addr_key_i,
  input [KeySize-1:0] rand_data_key_i,
  input  scramble_req_t [NumBanks-1:0] scramble_req_i,
  output scramble_rsp_t [NumBanks-1:0] scramble_rsp_o,
  output logic arb_err_o
);

  ///////////////////////////
  // input arbitration logic
  ///////////////////////////

  localparam int OpDataWidth = 2*DataWidth + $bits(cipher_ops_e);
  logic calc_req, calc_ack, op_req, op_ack;
  logic [NumBanks-1:0] calc_req_banks, calc_ack_banks, op_req_banks, op_ack_banks;
  logic [BankAddrW-1:0] calc_addr_in_banks[NumBanks];
  logic [OpDataWidth-1:0] op_data_in_banks[NumBanks];
  logic [BankAddrW-1:0] calc_addr_in;
  logic [DataWidth-1:0] calc_mask;
  logic [OpDataWidth-1:0] op_data_in;
  cipher_ops_e op_type;
  logic [DataWidth-1:0] plain_data_in, plain_data_out, scrambled_data_in, scrambled_data_out;
  for (genvar k = 0; k < NumBanks; k++) begin : gen_scramble_assign
    // Inputs for GF mult
    assign calc_req_banks[k] = scramble_req_i[k].calc_req;
    assign calc_addr_in_banks[k] = scramble_req_i[k].addr;
    // Outputs for GF mult
    assign scramble_rsp_o[k].calc_ack = calc_ack_banks[k];
    assign scramble_rsp_o[k].mask = calc_mask;


    // Inputs for scrambling primitive
    assign op_req_banks[k] = scramble_req_i[k].op_req;
    assign op_data_in_banks[k] = {scramble_req_i[k].op_type,
                                  scramble_req_i[k].plain_data,
                                  scramble_req_i[k].scrambled_data};
    // Outputs for scrambling primitive
    assign scramble_rsp_o[k].op_ack = op_ack_banks[k];
    assign scramble_rsp_o[k].plain_data = plain_data_out;
    assign scramble_rsp_o[k].scrambled_data = scrambled_data_out;
  end

  // SEC_CM: PHY_ARBITER.CTRL.REDUN
  logic [NumBanks-1:0] local_err;
  prim_arbiter_tree_dup #(
    .N(NumBanks),
    .DW(BankAddrW),
    .EnDataPort(1)
  ) u_prim_arbiter_tree_calc (
    .clk_i,
    .rst_ni,
    .req_chk_i(1'b1),
    .req_i    (calc_req_banks),
    .data_i   (calc_addr_in_banks),
    .gnt_o    (calc_ack_banks),
    .idx_o    (),
    .valid_o  (calc_req),
    .data_o   (calc_addr_in),
    .ready_i  (calc_ack),
    .err_o    (local_err[0])
  );

  // SEC_CM: PHY_ARBITER.CTRL.REDUN
  prim_arbiter_tree_dup #(
    .N(NumBanks),
    .DW(OpDataWidth),
    .EnDataPort(1)
  ) u_prim_arbiter_tree_op (
    .clk_i,
    .rst_ni,
    .req_chk_i(1'b1),
    .req_i    (op_req_banks),
    .data_i   (op_data_in_banks),
    .gnt_o    (op_ack_banks),
    .idx_o    (),
    .valid_o  (op_req),
    .data_o   (op_data_in),
    .ready_i  (op_ack),
    .err_o    (local_err[1])
  );

  assign arb_err_o = |local_err;

  assign {op_type,
          plain_data_in,
          scrambled_data_in} = op_data_in;

  ///////////////////////////
  // GF multiplier
  ///////////////////////////

  localparam int AddrPadWidth = DataWidth - BankAddrW;
  localparam int UnusedWidth = KeySize - AddrPadWidth;

  // unused portion of addr_key
  logic [KeySize-1:0] muxed_addr_key;

  logic addr_key_sel;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      addr_key_sel <= '0;
    end else if (!calc_req || calc_req && calc_ack) begin
      addr_key_sel <= disable_i;
    end
  end

  assign muxed_addr_key = addr_key_sel ? rand_addr_key_i : addr_key_i;

  logic [UnusedWidth-1:0] unused_key;
  assign unused_key = muxed_addr_key[KeySize-1 -: UnusedWidth];

  // Galois Multiply portion
  // Note: Degree of IPoly and width parameters must match (leading MSB of IPoly is dropped).
  if (SecScrambleEn) begin : gen_gf_mult
    prim_gf_mult # (
      .Width(DataWidth),
      .StagesPerCycle(DataWidth / GfMultCycles),
      .IPoly(ScrambleIPoly)
    ) u_mult (
      .clk_i,
      .rst_ni,
      .req_i(calc_req),
      .operand_a_i({muxed_addr_key[DataWidth +: AddrPadWidth], calc_addr_in}),
      .operand_b_i(muxed_addr_key[DataWidth-1:0]),
      .ack_o(calc_ack),
      .prod_o(calc_mask)
    );
  end else begin : gen_no_gf_mult
    assign calc_mask = '0;

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        calc_ack <= '0;
      end else if (calc_req && calc_ack) begin
        calc_ack <= '0;
      end else if (calc_req && !calc_ack) begin
        calc_ack <= '1;
      end
    end
  end

  ///////////////////////////
  // cipher
  ///////////////////////////

  logic dec;
  logic [DataWidth-1:0] data;
  assign dec = op_type == DeScrambleOp;

  // Do not allow the key to change during a transaction.
  // While this may be desirable for security reasons, it creates
  // timing issues for physical design
  logic data_key_sel;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      data_key_sel <= '0;
    end else if (!op_req || op_req && op_ack) begin
      data_key_sel <= disable_i;
    end
  end

  // the prim_prince valid_o is a flopped version of valid_i
  // As a result, when op_req stays high due to multiple transactions
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

  assign cipher_valid_in_d = op_ack ? '0 : op_req & !cipher_valid_out;
  assign op_ack = cipher_valid_in_q & cipher_valid_out;

  if (SecScrambleEn) begin : gen_prince
    prim_prince # (
      .DataWidth(DataWidth),
      .KeyWidth(KeySize),
      // Use improved key schedule proposed by https://eprint.iacr.org/2014/656.pdf (see appendix).
      .UseOldKeySched(1'b0),
      .HalfwayDataReg(1'b1),
      // No key register is needed half way, since the data_key_i and operation op_type inputs
      // remain constant until one data block has been processed.
      .HalfwayKeyReg (1'b0)
    ) u_cipher (
      .clk_i,
      .rst_ni,
      .valid_i(cipher_valid_in_d),
      .data_i(dec ? scrambled_data_in : plain_data_in),
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
    assign data = dec ? scrambled_data_in : plain_data_in;
  end

  // if decrypt, output the unscrambled data, feed input through otherwise
  assign plain_data_out = dec ? data : scrambled_data_in;

  // if encrypt, output the scrambled data, feed input through otherwise
  assign scrambled_data_out = dec ? plain_data_in : data;



endmodule // flash_phy_scramble
