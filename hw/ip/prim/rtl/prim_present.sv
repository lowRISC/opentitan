// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module is an implementation of the encryption pass of the 64bit PRESENT
// block cipher. It is a fully unrolled combinational implementation that
// supports both key sizes specified in the paper (80bit and 128bit). Further,
// the number of rounds is fully configurable, and the primitive supports a
// 32bit block cipher flavor which is not specified in the original paper. It
// should be noted, however, that the 32bit version is **not** secure and must
// not be used in a setting where cryptographic cipher strength is required. The
// 32bit variant is only intended to be used as a lightweight data scrambling
// device.
//
// See also: prim_prince
//
// References: - https://en.wikipedia.org/wiki/PRESENT
//             - https://en.wikipedia.org/wiki/Prince_(cipher)
//             - http://www.lightweightcrypto.org/present/present_ches2007.pdf
//             - https://eprint.iacr.org/2012/529.pdf
//             - https://csrc.nist.gov/csrc/media/events/lightweight-cryptography-workshop-2015/documents/papers/session7-maene-paper.pdf

// TODO: this module has not been verified yet, and has only been used in
// synthesis experiments.

module prim_present #(
  parameter int DataWidth = 64, // {32, 64}
  parameter int KeyWidth  = 80, // {64, 80, 128}
  parameter int NumRounds = 31  // > 0
) (
  input        [DataWidth-1:0] data_i,
  input        [KeyWidth-1:0]  key_i,
  output logic [DataWidth-1:0] data_o
);

  //////////////////////////////////
  // helper functions / constants //
  //////////////////////////////////

  // this is the sbox from the present cipher
  localparam logic[15:0][3:0] SBox4 = {4'h2, 4'h1, 4'h7, 4'h4,
                                       4'h8, 4'hF, 4'hE, 4'h3,
                                       4'hD, 4'hA, 4'h0, 4'h9,
                                       4'hB, 4'h6, 4'h5, 4'hC};

  // these are modified permutation indices for a 32bit version that
  // follow the same pattern as for the 64bit version
  localparam logic[31:0][4:0] Perm32 = {5'd31, 5'd23, 5'd15, 5'd7,
                                        5'd30, 5'd22, 5'd14, 5'd6,
                                        5'd29, 5'd21, 5'd13, 5'd5,
                                        5'd28, 5'd20, 5'd12, 5'd4,
                                        5'd27, 5'd19, 5'd11, 5'd3,
                                        5'd26, 5'd18, 5'd10, 5'd2,
                                        5'd25, 5'd17, 5'd9,  5'd1,
                                        5'd24, 5'd16, 5'd8,  5'd0};

  // these are the permutation indices of the present cipher
  localparam logic[63:0][5:0] Perm64 = {6'd63, 6'd47, 6'd31, 6'd15,
                                        6'd62, 6'd46, 6'd30, 6'd14,
                                        6'd61, 6'd45, 6'd29, 6'd13,
                                        6'd60, 6'd44, 6'd28, 6'd12,
                                        6'd59, 6'd43, 6'd27, 6'd11,
                                        6'd58, 6'd42, 6'd26, 6'd10,
                                        6'd57, 6'd41, 6'd25, 6'd09,
                                        6'd56, 6'd40, 6'd24, 6'd08,
                                        6'd55, 6'd39, 6'd23, 6'd07,
                                        6'd54, 6'd38, 6'd22, 6'd06,
                                        6'd53, 6'd37, 6'd21, 6'd05,
                                        6'd52, 6'd36, 6'd20, 6'd04,
                                        6'd51, 6'd35, 6'd19, 6'd03,
                                        6'd50, 6'd34, 6'd18, 6'd02,
                                        6'd49, 6'd33, 6'd17, 6'd01,
                                        6'd48, 6'd32, 6'd16, 6'd00};

  function automatic logic [DataWidth-1:0] sbox4_layer(logic [DataWidth-1:0] state_in);
    logic [63:0] state_out;
    // note that if simulation performance becomes an issue, this loop can be unrolled
    for (int k = 0; k < DataWidth/4; k++) begin
      state_out[k*4  +: 4] = SBox4[state_in[k*4  +: 4]];
    end
    return state_out;
  endfunction : sbox4_layer

  function automatic logic [DataWidth-1:0] perm_layer(logic [DataWidth-1:0] state_in);
    logic [DataWidth-1:0] state_out;
    if (DataWidth == 64) begin
      // note that if simulation performance becomes an issue, this loop can be unrolled
      for (int k = 0; k < DataWidth; k++) begin
        state_out[k] = state_in[Perm64[k]];
      end
    end else begin
      // note that if simulation performance becomes an issue, this loop can be unrolled
      for (int k = 0; k < DataWidth; k++) begin
        state_out[k] = state_in[Perm32[k]];
      end
    end
    return state_out;
  endfunction : perm_layer

  function automatic logic [KeyWidth-1:0] update_key(logic [KeyWidth-1:0] key_in,
                                                     logic [4:0] round_cnt);
    logic [KeyWidth-1:0] key_out;
    // rotate by 61 to the left
    key_out = KeyWidth'(key_in << 61) | KeyWidth'(key_in >> (KeyWidth-61));
    // sbox on uppermost 4 bits
    key_out[KeyWidth-1 -: 4] = SBox4[key_out[KeyWidth-1 -: 4]];
    // xor in round counter on bits 19 to 15
    key_out[19:15] ^= round_cnt;
    return key_out;
  endfunction : update_key

  //////////////
  // datapath //
  //////////////

  logic [DataWidth-1:0] data_state;
  logic [KeyWidth-1:0]  round_key;
  always_comb begin : p_present
    data_state = data_i;
    round_key  = key_i;
    for (int k = 0; k < NumRounds; k++) begin
      // cipher layers
      data_state = data_state ^ round_key[KeyWidth-1 : KeyWidth-DataWidth];
      data_state = sbox4_layer(data_state);
      data_state = perm_layer(data_state);
      // update round key, count goes from 1 to 31 (max)
      round_key  = update_key(round_key, 5'(k + 1));
    end
    data_o = data_state ^ round_key;
  end

  ////////////////
  // assertions //
  ////////////////

  `ASSERT_INIT(SupportedDataWidth_A, DataWidth inside {32, 64})
  `ASSERT_INIT(SupportedKeyWidth_A, KeyWidth inside {64, 80, 128})
  `ASSERT_INIT(SupportedNumRounds_A, NumRounds > 0)

endmodule : prim_present
