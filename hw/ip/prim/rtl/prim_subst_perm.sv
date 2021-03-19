// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This is a simple data diffusion primitive that is constructed in a similar fashion
// as the PRESENT cipher (i.e. it uses a substitution/permutation network). Note however
// that this is **not** cryptographically secure. The main purpose of this primitive is to
// provide a cheap diffusion mechanism for arbitrarily sized vectors.
//
// See also: prim_prince, prim_present, prim_cipher_pkg

module prim_subst_perm #(
  parameter int DataWidth = 64,
  parameter int NumRounds = 31,
  parameter bit Decrypt   = 0    // 0: encrypt, 1: decrypt
) (
  input        [DataWidth-1:0] data_i,
  input        [DataWidth-1:0] key_i,
  output logic [DataWidth-1:0] data_o
);

  //////////////
  // datapath //
  //////////////

  // The "split_var" hint that we pass to verilator here tells it to schedule the different parts of
  // data_state separately. This avoids an UNOPTFLAT error where it would otherwise see a dependency
  // chain
  //
  //    data_state -> data_state_sbox -> data_state
  //
  logic [NumRounds:0][DataWidth-1:0] data_state /* verilator split_var */;

  // initialize
  assign data_state[0] = data_i;

  for (genvar r = 0; r < NumRounds; r++) begin : gen_round
    logic [DataWidth-1:0] data_state_sbox, data_state_flipped;
    ////////////////////////////////
    // decryption pass, performs inverse permutation and sbox
    if (Decrypt) begin : gen_dec
      always_comb begin : p_dec
        data_state_sbox = data_state[r] ^ key_i;
        // Reverse odd/even grouping
        data_state_flipped = data_state_sbox;
        for (int k = 0; k < DataWidth/2; k++) begin
          data_state_flipped[k * 2]     = data_state_sbox[k];
          data_state_flipped[k * 2 + 1] = data_state_sbox[k + DataWidth/2];
        end
        // Flip vector
        for (int k = 0; k < DataWidth; k++) begin
          data_state_sbox[DataWidth - 1 - k] = data_state_flipped[k];
        end
        // Inverse SBox layer
        for (int k = 0; k < DataWidth/4; k++) begin
          data_state_sbox[k*4 +: 4] = prim_cipher_pkg::PRESENT_SBOX4_INV[data_state_sbox[k*4 +: 4]];
        end
        data_state[r + 1] = data_state_sbox;
      end
    ////////////////////////////////
    // encryption pass
    end else begin : gen_enc
      always_comb begin : p_enc
        data_state_sbox = data_state[r] ^ key_i;
        // This SBox layer is aligned to nibbles, so the uppermost bits may not be affected by this.
        // However, the permutation below ensures that these bits get shuffled to a different
        // position when performing multiple rounds.
        for (int k = 0; k < DataWidth/4; k++) begin
          data_state_sbox[k*4 +: 4] = prim_cipher_pkg::PRESENT_SBOX4[data_state_sbox[k*4 +: 4]];
        end
        // Flip the vector to move the MSB positions into the LSB positions
        for (int k = 0; k < DataWidth; k++) begin
          data_state_flipped[DataWidth - 1 - k] = data_state_sbox[k];
        end
        // Regroup bits such that all even indices are stacked up first, followed by all odd
        // indices. Note that if the Width is odd, this is still ok, since
        // the uppermost bit just stays in place in that case.
        data_state_sbox = data_state_flipped;
        for (int k = 0; k < DataWidth/2; k++) begin
          data_state_sbox[k]               = data_state_flipped[k * 2];
          data_state_sbox[k + DataWidth/2] = data_state_flipped[k * 2 + 1];
        end
        data_state[r + 1] = data_state_sbox;
      end
    end // gen_enc
    ////////////////////////////////
  end // gen_round

  // finalize
  assign data_o = data_state[NumRounds] ^ key_i;

endmodule : prim_subst_perm
