// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// RRAM Scramble Module
//
// This module implements the RRAM scramble / de-scramble operation
// This operation is based on XEX. This module is shared by the write and read path.
// The datapath is 128bits and builds on two interleaved 64b prince ciphers.
//

module rram_scramble import rram_ctrl_pkg::*; #(
  parameter rram_key_t RndCnstAddrKey = RndCnstAddrKeyDefault,
  parameter rram_key_t RndCnstDataKey = RndCnstDataKeyDefault,
  parameter bit        SecScrambleEn  = 1'b1,
  parameter bit        Interleave     = 1'b1
) (
  input  logic                  clk_i,
  input  logic                  rst_ni,
  input  prim_mubi_pkg::mubi4_t keys_disable_i,
  input  logic                  keys_valid_i,
  input  rram_key_t             addr_key_i,
  input  rram_key_t             data_key_i,
  input  rram_key_t             rand_addr_key_i,
  input  rram_key_t             rand_data_key_i,
  input  scramble_req_t [1:0]   scramble_req_i,
  output scramble_rsp_t [1:0]   scramble_rsp_o,
  output logic                  arb_err_o
);

  ///////////////////////////////////////////
  // Swap keys when scrambling is disabled //
  ///////////////////////////////////////////
  rram_key_t addr_key_q, addr_key_d;
  rram_key_t data_key_q, data_key_d;

  always_comb begin
    addr_key_d = addr_key_q;
    data_key_d = data_key_q;

    if (prim_mubi_pkg::mubi4_test_false_strict(keys_disable_i)) begin
      addr_key_d = rand_addr_key_i;
      data_key_d = rand_data_key_i;
    end else if (keys_valid_i) begin
      addr_key_d = addr_key_i;
      data_key_d = data_key_i;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      addr_key_q <= RndCnstAddrKey;
      data_key_q <= RndCnstDataKey;
    end else begin
      addr_key_q <= addr_key_d;
      data_key_q <= data_key_d;
    end
  end

  //////////////////////////////////////////////////////
  // Input arbitration logic from write and read path //
  //////////////////////////////////////////////////////

  localparam int OpDataWidth = DataWidth + $bits(cipher_ops_e) + 1;

  // pre arbitration signals
  logic [1:0] calc_req_all, calc_ack_all, op_req_all, op_ack_all;

  logic [AddrW-1:0]       calc_addr_in_all[2];
  logic [OpDataWidth-1:0] op_data_in_all[2];

  // post arbitration signals
  logic calc_req, calc_ack, op_req, op_ack;
  logic [AddrW-1:0]       calc_addr_in;
  logic [DataWidth-1:0]   calc_mask;
  logic [OpDataWidth-1:0] op_data_in;
  logic [DataWidth-1:0]   data_in, data_out;
  cipher_ops_e            op_type;
  logic                   cipher_switch;

  for (genvar k = 0; k < 2; k++) begin : gen_scramble_assign
    // Inputs for GF mult
    assign calc_req_all[k]     = scramble_req_i[k].calc_req;
    assign calc_addr_in_all[k] = scramble_req_i[k].addr;
    // Outputs of GF mult
    assign scramble_rsp_o[k].calc_ack = calc_ack_all[k];
    assign scramble_rsp_o[k].mask     = calc_ack_all[k] ? calc_mask : '0;

    // Inputs for scrambling primitive
    assign op_req_all[k]     = scramble_req_i[k].op_req;
    assign op_data_in_all[k] = {scramble_req_i[k].op_type,
                                scramble_req_i[k].data_in,
                                scramble_req_i[k].cipher_switch};
    // Outputs of scrambling primitive
    assign scramble_rsp_o[k].op_ack   = op_ack_all[k];
    assign scramble_rsp_o[k].data_out = op_ack_all[k] ? data_out : '0;
  end

  // SEC_CM: PHY_ARBITER.CTRL.REDUN
  logic [1:0] local_err;
  prim_arbiter_tree_dup #(
    .N(2),
    .DW(AddrW),
    .EnDataPort(1)
  ) u_prim_arbiter_tree_calc (
    .clk_i,
    .rst_ni,
    .req_chk_i(1'b1),
    .req_i    (calc_req_all),
    .data_i   (calc_addr_in_all),
    .gnt_o    (calc_ack_all),
    .idx_o    (),
    .valid_o  (calc_req),
    .data_o   (calc_addr_in),
    .ready_i  (calc_ack),
    .err_o    (local_err[0])
  );

  // SEC_CM: PHY_ARBITER.CTRL.REDUN
  prim_arbiter_tree_dup #(
    .N(2),
    .DW(OpDataWidth),
    .EnDataPort(1)
  ) u_prim_arbiter_tree_op (
    .clk_i,
    .rst_ni,
    .req_chk_i(1'b1),
    .req_i    (op_req_all),
    .data_i   (op_data_in_all),
    .gnt_o    (op_ack_all),
    .idx_o    (),
    .valid_o  (op_req),
    .data_o   (op_data_in),
    .ready_i  (op_ack),
    .err_o    (local_err[1])
  );

  assign arb_err_o = |local_err;

  assign {op_type, data_in, cipher_switch} = op_data_in;

  ///////////////////////////
  // GF multiplier
  ///////////////////////////

  localparam int AddrPadWidth = DataWidth - AddrW;

  // Galois Multiply portion
  // Note: Degree of IPoly and width parameters must match (leading MSB of IPoly is dropped).
  if (SecScrambleEn) begin : gen_gf_mult
    logic [DataWidth-1:0] operand_a, operand_b;
    assign operand_a = addr_key_i[DataWidth-1:0];
    assign operand_b = {AddrPadWidth'(0), calc_addr_in};
    prim_gf_mult # (
      .Width(DataWidth),
      .StagesPerCycle(DataWidth / GfMultCycles),
      .IPoly(ScrambleIPoly)
    ) u_mult (
      .clk_i,
      .rst_ni,
      .req_i      (calc_req),
      .operand_a_i(operand_a),
      .operand_b_i(operand_b),
      .ack_o      (calc_ack),
      .ack_pre_o  (),
      .prod_o     (calc_mask)
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
  // Cipher
  ///////////////////////////

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

  if (SecScrambleEn) begin : gen_prince
    logic [1:0]                   cipher_valid;
    logic [1:0] [CipherWidth-1:0] cipher_data_out;
    for (genvar k = 0; k < 2; k++) begin : gen_cipher
      logic [CipherWidth-1:0] cipher_data_in;

      if (Interleave) begin : gen_interleave
        for (genvar i = 0; i < CipherWidth; i++) begin : gen_bits
          assign cipher_data_in[i] = cipher_switch ? data_in[2*i+(1-k)] : data_in[2*i+k];
        end
      end else begin : gen_no_interleave
        assign cipher_data_in = data_in[k*CipherWidth +: CipherWidth];
      end

      prim_prince # (
        .DataWidth(CipherWidth),
        .KeyWidth(KeySize),
        // Use improved key schedule proposed by https://eprint.iacr.org/2014/656.pdf (appendix).
        .UseOldKeySched(1'b0),
        .HalfwayDataReg(1'b1),
        .HalfwayKeyReg (1'b0)
      ) u_cipher (
        .clk_i,
        .rst_ni,
        .valid_i(cipher_valid_in_d),
        .data_i (cipher_data_in),
        .key_i  (data_key_i),
        .dec_i  (op_type == DeScrambleOp),
        .data_o (cipher_data_out[k]),
        .valid_o(cipher_valid[k])
      );

      if (Interleave) begin : gen_deinterleave
        for (genvar i = 0; i < CipherWidth; i++) begin : gen_bits
          assign data_out[2*i+k] = cipher_switch ? cipher_data_out[1-k][i] : cipher_data_out[k][i];
        end
      end else begin : gen_no_deinterleave
        assign data_out[k*CipherWidth +: CipherWidth] = cipher_data_out[k];
      end
    end
    assign cipher_valid_out = &cipher_valid;
  end else begin : gen_no_prince
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        cipher_valid_out <= '0;
      end else begin
        cipher_valid_out <= cipher_valid_in_d;
      end
    end
    assign data_out = data_in;
  end

  assign op_ack = cipher_valid_in_q & cipher_valid_out;

endmodule // rram_scramble
