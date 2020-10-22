// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// prim_keccak is single round permutation module
`include "prim_assert.sv"
module prim_keccak #(
  parameter int Width = 1600, // b= {25, 50, 100, 200, 400, 800, 1600}

  // Derived
  localparam int W        = Width/25,
  localparam int L        = $clog2(W),
  localparam int MaxRound = 12 + 2*L, // Keccak-f only
  localparam int RndW     = $clog2(MaxRound+1) // Representing up to MaxRound
) (
  input        [RndW-1:0]  rnd_i,   // Current Round
  input        [Width-1:0] s_i,
  output logic [Width-1:0] s_o
);
  ///////////
  // Types //
  ///////////
  //             x    y    z
  typedef logic [4:0][4:0][W-1:0] box_t;   // (x,y,z) state
  typedef logic           [W-1:0] lane_t;  // (z)
  typedef logic [4:0]     [W-1:0] plane_t; // (x,z)
  typedef logic [4:0][4:0]        slice_t; // (x,y)
  typedef logic      [4:0][W-1:0] sheet_t; // (y,z) identical to plane_t
  typedef logic [4:0]             row_t;   // (x)
  typedef logic      [4:0]        col_t;   // (y) identical to row_t

  //////////////
  // Keccak_f //
  //////////////
  box_t state_in, keccak_f;
  box_t theta_data, rho_data, pi_data, chi_data, iota_data;
  assign state_in = bitarray_to_box(s_i);
  assign theta_data = theta(state_in);
  // Commented out rho function as vcs complains z-Offset%W isn't constant
  //assign rho_data   = rho(theta_data);
  assign pi_data    = pi(rho_data);
  assign chi_data   = chi(pi_data);
  assign iota_data  = iota(chi_data, rnd_i);
  assign keccak_f   = iota_data;
  assign s_o        = box_to_bitarray(keccak_f);

  // Rho ======================================================================
  // As RhoOffset[x][y] is considered as variable int in VCS,
  // it is replaced with generate statement.
  localparam int RhoOffset [5][5]  = '{
    //y  0    1    2    3    4     x
    '{   0,  36,   3, 105, 210},// 0
    '{   1, 300,  10,  45,  66},// 1
    '{ 190,   6, 171,  15, 253},// 2
    '{  28,  55, 153,  21, 120},// 3
    '{  91, 276, 231, 136,  78} // 4
  };
  for (genvar x = 0 ; x < 5 ; x++) begin : gen_rho_x
    for (genvar y = 0 ; y < 5 ; y++) begin : gen_rho_y
      localparam int Offset = RhoOffset[x][y]%W;
      localparam int ShiftAmt = W- Offset;
      if (Offset == 0) begin : gen_offset0
        assign rho_data[x][y][W-1:0] = theta_data[x][y][W-1:0];
      end else begin : gen_others
        assign rho_data[x][y][W-1:0] = {theta_data[x][y][0+:ShiftAmt],
                                        theta_data[x][y][ShiftAmt+:Offset]};
      end
    end
  end

  ////////////////
  // Assertions //
  ////////////////

  `ASSERT_INIT(ValidWidth_A, Width inside {25, 50, 100, 200, 400, 800, 1600})
  `ASSERT_INIT(ValidW_A, W inside {1, 2, 4, 8, 16, 32, 64})
  `ASSERT_INIT(ValidL_A, L inside {0, 1, 2, 3, 4, 5, 6})
  `ASSERT_INIT(ValidRound_A, MaxRound <= 24) // Keccak-f only

  ///////////////
  // Functions //
  ///////////////

  // Convert bitarray to 3D box
  // Please take a look at FIPS PUB 202
  // https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf
  // > For all triples (x,y,z) such that 0<=x<5, 0<=y<5, and 0<=z<w,
  // >    A[x,y,z]=S[w(5y+x)+z]
  function automatic box_t bitarray_to_box(logic [Width-1:0] s_in);
    automatic box_t box;
    for (int y = 0 ; y < 5 ; y++) begin
      for (int x = 0 ; x < 5 ; x++) begin
        for (int z = 0 ; z < W ; z++) begin
          box[x][y][z] = s_in[W*(5*y+x) + z];
        end
      end
    end
    return box;
  endfunction : bitarray_to_box

  // Convert 3D cube to bitarray
  function automatic logic [Width-1:0] box_to_bitarray(box_t state);
    automatic logic [Width-1:0] bitarray;
    for (int y = 0 ; y < 5 ; y++) begin
      for (int x = 0 ; x < 5 ; x++) begin
        for (int z = 0 ; z < W ; z++) begin
          bitarray[W*(5*y+x)+z] = state[x][y][z];
        end
      end
    end
    return bitarray;
  endfunction : box_to_bitarray

  // Step Mapping =============================================================
  // theta(θ)
  // XOR each bit in the state with the parity of two columns
  // C[x,z] = A[x,0,z] ^ A[x,1,z] ^ A[x,2,z] ^ A[x,3,z] ^ A[x,4,z]
  // D[x,z] = C[x-1,z] ^ C[x+1,z-1]
  // theta = A[x,y,z] ^ D[x,z]
  function automatic box_t theta(box_t state);
    plane_t c;
    plane_t d;
    box_t result;
    for (int x = 0 ; x < 5 ; x++) begin
      for (int z = 0 ; z < W ; z++) begin
        c[x][z] = state[x][0][z] ^ state[x][1][z]
                ^ state[x][2][z] ^ state[x][3][z] ^ state[x][4][z];
      end
    end
    for (int x = 0 ; x < 5 ; x++) begin
      int index_x1, index_x2;
      index_x1 = (x == 0) ? 4 : x-1; // (x-1)%5
      index_x2 = (x == 4) ? 0 : x+1; // (x+1)%5
      for (int z = 0 ; z < W ; z++) begin
        int index_z;
        index_z = (z == 0) ? W-1 : z-1; // (z+1)%W
        d[x][z] = c[index_x1][z] ^ c[index_x2][index_z];
      end
    end
    for (int x = 0 ; x < 5 ; x++) begin
      for (int y = 0 ; y < 5 ; y++) begin
        for (int z = 0 ; z < W ; z++) begin
          result[x][y][z] = state[x][y][z] ^ d[x][z];
        end
      end
    end
    return result;
  endfunction : theta

  // rho

  // Commented out entire rho function due to VCS elaboration error.
  // (z-RhoOffset[x][y]%W) isn't considered as a constant in VCS.
  // Even changing it to W-RhoOffset[x][y]%W and assign to ShiftAmt
  // creates same error.

  // Offset : Look at Table 2 in FIPS PUB 202
  //localparam int RhoOffset [5][5]  = '{
  //  //y  0    1    2    3    4     x
  //  '{   0,  36,   3, 105, 210},// 0
  //  '{   1, 300,  10,  45,  66},// 1
  //  '{ 190,   6, 171,  15, 253},// 2
  //  '{  28,  55, 153,  21, 120},// 3
  //  '{  91, 276, 231, 136,  78} // 4
  //};

  // rotate bits of each lane by offset
  // 1. rho[0,0,z] = A[0,0,z]
  // 2. Offset swap
  //    a. (x,y) := (1,0)
  //    b. for t [0..23]
  //       i. rho[x,y,z] = A[x,y,z-(t+1)(t+2)/2]
  //       ii. (x,y) = (y, (2x+3y))
  //function automatic box_t rho(box_t state);
  //  box_t result;
  //  for (int x = 0 ; x < 5 ; x++) begin
  //    for (int y = 0 ; y < 5 ; y++) begin
  //      for (int z = 0 ; z < W ; z++) begin
  //        automatic int index_z;
  //        index_z = (z-RhoOffset[x][y])%W;
  //        result[x][y][z] = state[x][y][(z-RhoOffset[x][y])%W];
  //      end
  //    end
  //  end
  //  return result;
  //endfunction : rho

  // pi
  // rearrange the position of lanes
  // pi[x,y,z] = state[(x+3y),x,z]
  localparam int PiRotate [5][5] = '{
    //y  0    1    2    3    4     x
    '{   0,   3,   1,   4,   2},// 0
    '{   1,   4,   2,   0,   3},// 1
    '{   2,   0,   3,   1,   4},// 2
    '{   3,   1,   4,   2,   0},// 3
    '{   4,   2,   0,   3,   1} // 4
  };
  function automatic box_t pi(box_t state);
    box_t result;
    for (int x = 0 ; x < 5 ; x++) begin
      for (int y = 0 ; y < 5 ; y++) begin
        int index_x;
        result[x][y][W-1:0] = state[PiRotate[x][y]][x][W-1:0];
      end
    end
    return result;
  endfunction : pi

  // chi
  // chi[x,y,z] = state[x,y,z] ^ ((state[x+1,y,z] ^ 1) & state[x+2,y,z])
  function automatic box_t chi(box_t state);
    box_t result;
    for (int x = 0 ; x < 5 ; x++) begin
      int index_x1, index_x2;
      index_x1 = (x == 4) ? 0 : x+1;
      index_x2 = (x >= 3) ? x-3 : x+2;
      for (int y = 0 ; y < 5 ; y++) begin
        for (int z = 0 ; z < W ; z++) begin
          result[x][y][z] = state[x][y][z] ^
                                ((~state[index_x1][y][z])
                                 & state[index_x2][y][z]);
        end
      end
    end
    return result;
  endfunction : chi

  // iota
  // XOR (x,y) = (0,0) with round constant

  // RC parameter: Precomputed by util/keccak_rc.py. Only up-to 0..L-1 is used
  // RC = '0
  // RC[2**j-1] = rc(j+7*rnd)
  // rc(t) =
  //    1. t%255 == 0 -> 1
  //    2. R[0:7] = 'b10000000
  //    3. for i = [1..t%255]
  //      a. R = 0 || R
  //      b. R[0] = R[0] ^ R[8]
  //      c. R[4] = R[4] ^ R[8]
  //      d. R[5] = R[5] ^ R[8]
  //      e. R[6] = R[6] ^ R[8]
  //      f. R = R[0:7]
  //    4. return R[0]
  // RC has L = [0..6]
  // for lower L case, only chopping lower part of 64bit RC is sufficient.
  localparam logic [63:0] RC [24] = '{
     64'h 0000_0000_0000_0001, // Round 0
     64'h 0000_0000_0000_8082, // Round 1
     64'h 8000_0000_0000_808A, // Round 2
     64'h 8000_0000_8000_8000, // Round 3
     64'h 0000_0000_0000_808B, // Round 4
     64'h 0000_0000_8000_0001, // Round 5
     64'h 8000_0000_8000_8081, // Round 6
     64'h 8000_0000_0000_8009, // Round 7
     64'h 0000_0000_0000_008A, // Round 8
     64'h 0000_0000_0000_0088, // Round 9
     64'h 0000_0000_8000_8009, // Round 10
     64'h 0000_0000_8000_000A, // Round 11
     64'h 0000_0000_8000_808B, // Round 12
     64'h 8000_0000_0000_008B, // Round 13
     64'h 8000_0000_0000_8089, // Round 14
     64'h 8000_0000_0000_8003, // Round 15
     64'h 8000_0000_0000_8002, // Round 16
     64'h 8000_0000_0000_0080, // Round 17
     64'h 0000_0000_0000_800A, // Round 18
     64'h 8000_0000_8000_000A, // Round 19
     64'h 8000_0000_8000_8081, // Round 20
     64'h 8000_0000_0000_8080, // Round 21
     64'h 0000_0000_8000_0001, // Round 22
     64'h 8000_0000_8000_8008  // Round 23
  };

  // iota: XOR with RC for (x,y) = (0,0)
  function automatic box_t iota(box_t state, logic [RndW-1:0] rnd);
    box_t result;
    result = state;
    result[0][0][W-1:0] = state[0][0][W-1:0] ^ RC[rnd][W-1:0];

    return result;
  endfunction : iota

  // Round function : Rnd(A,i_r)
  // Not used due to rho function issue described above.

  //function automatic box_t keccak_rnd(box_t state, logic [RndW-1:0] rnd);
  //  box_t keccak_state;
  //  keccak_state = iota(chi(pi(rho(theta(state)))), rnd);
  //
  //  return keccak_state;
  //endfunction : keccak_rnd

endmodule

