// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package prim_trivium_pkg;

  typedef enum integer {
    SeedTypeKeyIv,        // 2 * 80 bits for key and IV, requires advancing the primitive
                          // 1152/OutputWidth (Trivium) or 708/OutputWidth (Bivium) times
                          // before the key stream becomes usable.
    SeedTypeStateFull,    // Seed the full state
    SeedTypeStatePartial  // Seed PartialSeedWidth bits of the state at a time.
  } seed_type_e;

  parameter int unsigned KeyIvWidth = 80;
  parameter int unsigned PartialSeedWidthDefault = 32;
  parameter int unsigned MinNfsrWidth = 84;

  // These LFSR parameters have been generated with
  // $ ./util/design/gen-lfsr-seed.py --width 288 --seed 31468618 --prefix "Trivium"
  parameter int TriviumLfsrWidth = 288;
  typedef logic [TriviumLfsrWidth-1:0] trivium_lfsr_seed_t;
  parameter trivium_lfsr_seed_t RndCnstTriviumLfsrSeedDefault = {
    32'h758a4420,
    256'h31e1c461_6ea343ec_153282a3_0c132b57_23c5a4cf_4743b3c7_c32d580f_74f1713a
  };

  /////////////
  // Trivium //
  /////////////

  parameter int unsigned TriviumMaxNfsrWidth = 111;
  parameter int TriviumStateWidth = TriviumLfsrWidth;

  function automatic logic [TriviumStateWidth-1:0] trivium_update_state(
    logic [TriviumStateWidth-1:0] in
  );
    logic [TriviumStateWidth-1:0] out;
    logic mul_90_91, mul_174_175, mul_285_286;
    logic add_65_92, add_161_176, add_242_287;

    // First state part intermediate results
    mul_90_91 = in[90] & in[91];
    add_65_92 = in[65] ^ in[92];

    // Second state part intermediate results
    mul_174_175 = in[174] & in[175];
    add_161_176 = in[161] ^ in[176];

    // Third state part intermediate results
    mul_285_286 = in[285] & in[286];
    add_242_287 = in[242] ^ in[287];

    // Updates - feedback part
    out[0] = in[68] ^ (mul_285_286 ^ add_242_287);
    out[93] = in[170] ^ (add_65_92 ^ mul_90_91);
    out[177] = in[263] ^ (mul_174_175 ^ add_161_176);

    // Updates - shift part
    out[92:1] = in[91:0];
    out[176:94] = in[175:93];
    out[287:178] = in[286:177];

    return out;
  endfunction

  function automatic logic trivium_generate_key_stream(
    logic [TriviumStateWidth-1:0] state
  );
    logic key;
    logic add_65_92, add_161_176, add_242_287;
    logic unused_state;

    add_65_92 = state[65] ^ state[92];
    add_161_176 = state[161] ^ state[176];
    add_242_287 = state[242] ^ state[287];
    key = add_161_176 ^ add_65_92 ^ add_242_287;

    unused_state = ^{state[286:243],
                     state[241:177],
                     state[175:162],
                     state[160:93],
                     state[91:66],
                     state[64:0]};
    return key;
  endfunction

  function automatic logic [TriviumStateWidth-1:0] trivium_seed_key_iv(
      logic [KeyIvWidth-1:0] key,
      logic [KeyIvWidth-1:0] iv
    );
    logic [TriviumStateWidth-1:0] state;
    //     [287:285] [284:173] [172:93] [92:80] [79:0]
    state = {3'b111,   112'b0,      iv,  13'b0,   key};
    return state;
  endfunction

  ////////////
  // Bivium //
  ////////////

  parameter int unsigned BiviumMaxNfsrWidth = 93;
  parameter int BiviumStateWidth = 177;

  function automatic logic [BiviumStateWidth-1:0] bivium_update_state(
    logic [BiviumStateWidth-1:0] in
  );
    logic [BiviumStateWidth-1:0] out;
    logic mul_90_91, mul_174_175;
    logic add_65_92, add_161_176;

    // First state half intermediate results
    mul_90_91 = in[90] & in[91];
    add_65_92 = in[65] ^ in[92];

    // Second state half intermediate results
    mul_174_175 = in[174] & in[175];
    add_161_176 = in[161] ^ in[176];

    // Updates - feedback part
    out[0] = in[68] ^ (mul_174_175 ^ add_161_176);
    out[93] = in[170] ^ add_65_92 ^ mul_90_91;

    // Updates - shift part
    out[92:1] = in[91:0];
    out[176:94] = in[175:93];

    return out;
  endfunction

  function automatic logic bivium_generate_key_stream(
    logic [BiviumStateWidth-1:0] state
  );
    logic key;
    logic add_65_92, add_161_176;
    logic unused_state;

    add_65_92 = state[65] ^ state[92];
    add_161_176 = state[161] ^ state[176];
    key = add_161_176 ^ add_65_92;

    unused_state = ^{state[175:162],
                     state[160:93],
                     state[91:66],
                     state[64:0]};
    return key;
  endfunction

  function automatic logic [BiviumStateWidth-1:0] bivium_seed_key_iv(
      logic [KeyIvWidth-1:0] key,
      logic [KeyIvWidth-1:0] iv
    );
    logic [BiviumStateWidth-1:0] state;
    //   [176:173] [172:93] [92:80] [79:0]
    state = {4'b0,      iv,  13'b0,   key};
    return state;
  endfunction

endpackage
