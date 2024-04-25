// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Ascon duplex function implementation

// Ascon uses big endian encoding!
// Thus prim_ascon_duplex expects partial input blocks to fill up from left to right.
// This means data_in_i[127:120] must always be set for non empty inputs!

// TODO: Add countermeasures: mubi for control signals,
//       random values for state_to_round input, blinding for output signals
// TODO: Add backpressure logic, if output is not ready
// TODO: Add check what to do, if data_in_valid_bytes_i is greater than blocksize

module prim_ascon_duplex
  import prim_ascon_pkg::*;
  import prim_mubi_pkg::*;
 (
  input logic clk_i,
  input logic rst_ni,

  input duplex_variant_e ascon_variant,
  input duplex_op_e ascon_operation,

  input  logic start_i,
  output logic idle_o,

  // It is assumed that no_ad, no_msg, key, and nonce are always
  // valid and constant, when the cipher is triggered by the start command
  input logic no_ad,
  input logic no_msg,

  input logic [127:0] key_i,
  input logic [127:0] nonce_i,

  // Cipher Input Port
  input  logic [127:0] data_in_i,
  input  logic   [4:0] data_in_valid_bytes_i,
  input  mubi4_t       last_block_ad_i,
  input  mubi4_t       last_block_msg_i,
  input  logic         data_in_valid_i,
  output logic         data_in_read_o,

  // Cipher Output Port
  output logic [127:0] data_out_o,
  input  logic         data_out_read_i,
  output logic         data_out_we_o,

  output logic [127:0] tag_out_o,
  output logic         tag_out_we_o,

  output logic err_o
);

// TODO: Add backpressure check
logic unused_data_out_read_i;
assign unused_data_out_read_i = data_out_read_i;

logic round_count_error;
logic sparse_fsm_error;

logic set_round_counter;
logic inc_round_counter;

logic [4:0][63:0] ascon_state_q, ascon_state_d;
logic             ascon_state_update;

// Ascon's 320 bit state
always_ff @(posedge clk_i) begin : ascon_state_reg
  if (ascon_state_update) begin
    ascon_state_q <= ascon_state_d;
  end
end

logic [319:0] state_to_round;
logic [319:0] state_from_round;

fsm_state_e fsm_state_d, fsm_state_q;
perm_offset_e perm_offset;

logic  [63:0] iv;
assign iv = (ascon_variant == ASCON_128) ? IV_128 : IV_128A;

// internal combinatorial signals
mubi4_t complete_block;

// TODO add a check what to do, if data_in_valid_bytes_i is greater than blocksize
assign complete_block =  (ascon_variant == ASCON_128  && data_in_valid_bytes_i ==  8)
                       ||(ascon_variant == ASCON_128A && data_in_valid_bytes_i == 16) ?
                          MuBi4True : MuBi4False;

// Padding:
// 1) Associated Data
//    a) empty AD: No padding, AD-processing phase is skipped!
//    b) incomplete last block: A 10* padding is added to the input data.
//       The padded associated data is XORed to the state.
//    c) complete last block: No padding to the input, but an addtional state in the FSM
//       is used to perform the padding. A 10+ block is XORed to the state.
// 2) Encryption:
//    a) empty or incomplete last block: A 10* padding is added to the input data.
//       The padded associated data is XORed blockwise.
//    b) complete last block: No padding to the input, but an additional state in the FSM
//       is used to perform the padding. A 10+ block is XORed to the sate.
// 3) Decryption:
//    a) empty or incomplete last block: The padded (output) PLAINTEXT is XORed to the state.
//       This is equivalent to:
//       The unpadded part of the Ciphertext replaces the coresponding part of S_r
//       The remaining part of S_r is Xored with 10*.
//    b) complete last block: No padding to the input, but an additional state in the FSM
//       is used to perfom the padding. A 10+ block is XORed to the state,

// Padding logic
logic [127:0] empty_padding;
assign empty_padding = get_padding_mask(5'b00000);

logic [127:0] valid_bytes_bit_mask;
assign valid_bytes_bit_mask = bin2thermo(data_in_valid_bytes_i);

logic [127:0] padding_byte_bit_mask;
assign padding_byte_bit_mask = get_padding_mask(data_in_valid_bytes_i);

logic [127:0] data_in_valid_bytes;
assign data_in_valid_bytes = data_in_i & valid_bytes_bit_mask;

// data output
logic  [127:0] data_out;
assign data_out = (data_in_i ^ {ascon_state_q[0], ascon_state_q[1]}) & valid_bytes_bit_mask;

logic [127:0] data_in_padded;
logic [127:0] data_out_padded; // is only used intenrally for decryption.

// For BOTH encryption AND decryption the PLAINTEXT is XORed to the state!
// For encryption this is straight forward: S_r = S_r XOR P
// For decryption this means: S_r = S_r XOR P = S_r XOR (S_r XOR C) = C
// Thus the ciphertext replaces the rate. However, we cannot simply implement
// S_r = C, because this does not work for incomplete blocks, where only a part
// of the rate is replaced by C and the other part remains:
// S_r = S_l || S_(r-l) = C_l || S_(r-l)
// Therefore, it is easier to always XOR the padded plaintext

always_comb begin
  if (mubi4_test_true_strict(complete_block)) begin
      data_in_padded = data_in_valid_bytes;
      data_out_padded = data_out;
    end else begin
      data_in_padded = data_in_valid_bytes | padding_byte_bit_mask;
      data_out_padded = data_out | padding_byte_bit_mask;
  end
end

// TODO  add blinding
assign data_out_o  = data_out;
assign  tag_out_o  = ({ascon_state_q[3], ascon_state_q[4]} ^ key_i);

// Due to Ascon's round constants the current_round
// contains an offset:
// for P12 we count: from 0 to 11 = 12 rounds,
// for P8  we count: from 4 to 11 =  8 rounds,
// for P6  we count: from 5 to 11 =  6 rounds
logic [AsconRoundCountW-1:0] current_round;

prim_count #(
    .Width(AsconRoundCountW)
) u_round_counter (
    .clk_i,
    .rst_ni,
    .clr_i(1'b0),
    .set_i(set_round_counter),
    .set_cnt_i(perm_offset),
    .incr_en_i(inc_round_counter),
    .decr_en_i(1'b0),
    .step_i(AsconRoundCountW'(1)),
    .commit_i(1'b1),
    .cnt_o(current_round),
    .cnt_after_commit_o(),
    .err_o(round_count_error)
  );

always_comb begin : p_fsm
  // Default assignments
  fsm_state_d = fsm_state_q;
  data_in_read_o = 1'b0;
  data_out_we_o = 1'b0;
  tag_out_we_o = 1'b0;
  sparse_fsm_error = 1'b0;
  ascon_state_update = 1'b0;
  set_round_counter = 1'b0;
  inc_round_counter = 1'b0;
  perm_offset = P12;
  idle_o = 1'b0;

  unique case (fsm_state_q)
    Idle: begin
      idle_o = 1'b1;
      if (start_i) begin
        fsm_state_d = Init;
      end
    end
    Init: begin
      fsm_state_d = PermInit;
      perm_offset = P12;
      set_round_counter = 1'b1;
      ascon_state_update = 1'b1;
    end
    PermInit: begin
      if (current_round == ROUND_MAX) begin
        fsm_state_d = Xor0Key;
      end else begin
        inc_round_counter = 1'b1;
      end
      ascon_state_update = 1'b1;
    end
    Xor0Key: begin
      ascon_state_update = 1'b1;
      if (no_ad) begin
        fsm_state_d = XorDomSep;
      end else begin
        fsm_state_d = AbsorbAD;
      end
    end
    AbsorbAD: begin
      // There will be AD, otherwise we wouldn't be in this state/path
      if (data_in_valid_i) begin
        data_in_read_o = 1'b1; // data_in_valid_i is registered. We don't create a loop here!
        ascon_state_update = 1'b1;
        if (mubi4_test_true_strict(last_block_ad_i)) begin
          if (mubi4_test_true_strict(complete_block)) begin
            fsm_state_d = PermADEmpty;
          end else begin
            fsm_state_d = PermADLast;
          end
        end else begin // there are more blocks to come
          fsm_state_d = PermAD;
        end
      end
      if (ascon_variant == ASCON_128) begin
        perm_offset = P6;
      end else begin //ASCON_128A
        perm_offset = P8;
      end
      set_round_counter = 1'b1;
    end
    PermAD: begin
      if (current_round == ROUND_MAX) begin
        fsm_state_d = AbsorbAD;
      end else begin
        inc_round_counter = 1'b1;
      end
      ascon_state_update = 1'b1;
    end
    PermADLast: begin
      if (current_round == ROUND_MAX) begin
        fsm_state_d = XorDomSep;
      end else begin
        inc_round_counter = 1'b1;
      end
      ascon_state_update = 1'b1;
    end
    PermADEmpty: begin
      if (current_round == ROUND_MAX) begin
        fsm_state_d = AbsorbADEmpty;
      end else begin
        inc_round_counter = 1'b1;
      end
      ascon_state_update = 1'b1;
    end
    AbsorbADEmpty: begin
      ascon_state_update = 1'b1;
      fsm_state_d = PermADLast;
      if (ascon_variant == ASCON_128) begin
        perm_offset = P6;
      end else begin //ASCON_128A
        perm_offset = P8;
      end
      set_round_counter = 1'b1;
    end
    XorDomSep: begin
      ascon_state_update = 1'b1;
      if (no_msg) begin
        fsm_state_d = AbsorbMSGEmpty;
      end else begin
        fsm_state_d = AbsorbMSG;
      end
    end
    AbsorbMSG: begin
      if (data_in_valid_i) begin
        data_in_read_o = 1'b1; // data_in_valid_i is registered. We don't create a loop here!
        data_out_we_o = 1'b1;
        ascon_state_update = 1'b1;
        if (mubi4_test_true_strict(last_block_msg_i)) begin
          if (mubi4_test_true_strict(complete_block)) begin // we need extra padding
            fsm_state_d = PermMSGEmpty;
          end else begin // padding is done on the fly
            fsm_state_d = XorKey0;
          end
        end else begin
          fsm_state_d = PermMSG;
        end
      end

      if (ascon_variant == ASCON_128) begin
        perm_offset = P6;
      end else begin //ASCON_128A
        perm_offset = P8;
      end
      set_round_counter = 1'b1;
    end
    PermMSG: begin
      if (current_round == ROUND_MAX) begin
          fsm_state_d = AbsorbMSG;
      end else begin
        inc_round_counter = 1'b1;
      end
      ascon_state_update = 1'b1;
    end
    PermMSGEmpty: begin
      if (current_round == ROUND_MAX) begin
          fsm_state_d = AbsorbMSGEmpty;
      end else begin
        inc_round_counter = 1'b1;
      end
      ascon_state_update = 1'b1;
    end
    AbsorbMSGEmpty: begin
      ascon_state_update = 1'b1;
      fsm_state_d = XorKey0;
    end
    XorKey0: begin
       ascon_state_update = 1'b1;
       fsm_state_d = PermFinal;
       set_round_counter = 1'b1;
       perm_offset = P12;
    end
    PermFinal: begin
      if (current_round == ROUND_MAX) begin
          fsm_state_d = SqueezeTagXorKey;
      end else begin
        inc_round_counter = 1'b1;
      end
      ascon_state_update = 1'b1;
    end
    SqueezeTagXorKey: begin
      tag_out_we_o = 1'b1;
      fsm_state_d = Idle;
    end
    Error: begin
      fsm_state_d = Error;
      sparse_fsm_error = 1'b1;
    end
    default: begin
      fsm_state_d = Error;
      sparse_fsm_error = 1'b1;
    end
  endcase
end

`PRIM_FLOP_SPARSE_FSM(u_state_regs, fsm_state_d, fsm_state_q, fsm_state_e, Idle)


always_comb begin : ascon_state_mux
  // Default assignments
  ascon_state_d = ascon_state_q;
  // TODO: random values?
  state_to_round = '0;

  unique case (fsm_state_q)
    Init: begin
      ascon_state_d[0] = iv;
      ascon_state_d[1] = key_i[127:64];
      ascon_state_d[2] = key_i[63:0];
      ascon_state_d[3] = nonce_i[127:64];
      ascon_state_d[4] = nonce_i[63:0];
    end
    PermInit: begin
       state_to_round = ascon_state_q;
       ascon_state_d = state_from_round;
    end
    Xor0Key: begin
      ascon_state_d[3] = ascon_state_q[3] ^ key_i[127:64];
      ascon_state_d[4] = ascon_state_q[4] ^ key_i[63:0];
    end
    AbsorbAD: begin
      // padding is not an issue here. It is done on the fly.
      ascon_state_d[0] = ascon_state_q[0] ^ data_in_padded[127:64];
      if (ascon_variant == ASCON_128A) begin
        ascon_state_d[1] = ascon_state_q[1] ^ data_in_padded[63:0];
      end
    end
    PermAD: begin
      state_to_round = ascon_state_q;
      ascon_state_d = state_from_round;
    end
    PermADLast: begin
      state_to_round = ascon_state_q;
      ascon_state_d = state_from_round;
    end
    PermADEmpty: begin
      state_to_round = ascon_state_q;
      ascon_state_d = state_from_round;
    end
    AbsorbADEmpty: begin
      ascon_state_d[0] = ascon_state_q[0] ^ empty_padding[127:64];
      if (ascon_variant == ASCON_128A) begin
        // This should be optimized by the tool.
        // It is left here, so that the structure of the case
        // is the same as AbsorbAD.
        ascon_state_d[1] = ascon_state_q[1] ^ empty_padding[63:0];
      end
    end
    XorDomSep: begin
        // Invert MSB in Ascon's state
        // C-Code: s.x[4] ^= 1;
        // Double checked with C-output
        ascon_state_d[4][0] = ascon_state_q[4][0] ^ 1'b1;
    end
    AbsorbMSG: begin
      if (ascon_operation == ASCON_ENC) begin
        ascon_state_d[0] = ascon_state_q[0] ^ data_in_padded[127:64];
        if (ascon_variant == ASCON_128A) begin
          ascon_state_d[1] = ascon_state_q[0] ^ data_in_padded[63:0];
        end
      end else begin // ASCON_DEC
        ascon_state_d[0] = ascon_state_q[0] ^ data_out_padded[127:64];
        if (ascon_variant == ASCON_128A) begin
          ascon_state_d[1] = ascon_state_q[1] ^ data_out_padded[63:0];
        end
      end
    end
    PermMSG: begin
       state_to_round = ascon_state_q;
       ascon_state_d = state_from_round;
    end
    PermMSGEmpty: begin
      state_to_round = ascon_state_q;
      ascon_state_d = state_from_round;
    end
    AbsorbMSGEmpty: begin
      // The padding for an empty block is the same for encryption and decryption.
      ascon_state_d[0] = ascon_state_q[0] ^ empty_padding[127:64];
      if (ascon_variant == ASCON_128A) begin
        // This should be optimized by the tool.
        // It is left here, so that the structure of the case
        // is the same as AbsorbAD.
        ascon_state_d[1] = ascon_state_q[1] ^ empty_padding[63:0];
      end
    end
    XorKey0: begin
        if (ascon_variant == ASCON_128) begin
          ascon_state_d[2] = ascon_state_q[2] ^ key_i[63:0];
          ascon_state_d[1] = ascon_state_q[1] ^ key_i[127:64];
        end else begin //ASCON_128a
          ascon_state_d[3] = ascon_state_q[3] ^ key_i[63:0];
          ascon_state_d[2] = ascon_state_q[2] ^ key_i[127:64];
        end
    end
    PermFinal: begin
       state_to_round = ascon_state_q;
       ascon_state_d = state_from_round;
    end
    default: ascon_state_d = ascon_state_q;
  endcase
end

assign err_o = round_count_error | sparse_fsm_error;

prim_ascon_round u_prim_ascon_round (
  .state_o(state_from_round),
  .state_i(state_to_round),
  .rcon_i(get_ascon_rcon(current_round))
);


endmodule
