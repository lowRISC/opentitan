// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for prim_keccak. Intended to be used with a formal tool.

module keccak_2share_fpv #(
  parameter int Width = 1600
) (
  input                    clk_i,
  input                    rst_ni,
  input                    valid_i,
  input                    rand_valid_i,
  input        [Width-1:0] rand_i,
  input        [Width-1:0] state_i,
  output logic             done_o,
  output logic [Width-1:0] state_o
);

  localparam int W        = Width/25;
  localparam int L        = $clog2(W);
  localparam int NumRound = 12 + 2*L; // Keccak-f only
  localparam int RndW     = $clog2(NumRound+1);

  logic [RndW-1:0] round;
  logic [Width-1:0] state   [2];
  logic [Width-1:0] state_d [2];
  logic [Width-1:0] golden_state;
  logic [Width-1:0] golden_state_d[1];

  logic [Width-1:0] compare_states;
  typedef enum logic [1:0] {
    StIdle,
    StPhase1,
    StPhase2,
    StPhase3
  } share_state_e;

  share_state_e keccak_st, keccak_st_d;

  logic inc_round;
  logic update_state;
  logic sel_mux;

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      keccak_st <= StIdle;
    end else begin
      keccak_st <= keccak_st_d;
    end
  end

  always_comb begin
    keccak_st_d = StIdle;

    inc_round = 1'b0;
    update_state = 1'b0;
    sel_mux = 1'b0;
    unique case (keccak_st)
      StIdle: begin
        sel_mux = 1'b 0;
        if (valid_i) begin
          keccak_st_d = StPhase1;

        end else begin
          keccak_st_d = StIdle;
        end
      end
      StPhase1: begin
        keccak_st_d = StPhase2;

        update_state = 1'b1;
        sel_mux = 1'b0;
      end
      StPhase2: begin
        sel_mux = 1'b1;
        if (rand_valid_i) begin
          keccak_st_d = StPhase3;
        end else begin
          keccak_st_d = StPhase2;
        end
      end
      StPhase3: begin
        sel_mux = 1'b1;
        update_state = 1'b1;
        if (round == NumRound-1) begin
          keccak_st_d = StIdle;
          inc_round = 1'b1;
        end else begin
          keccak_st_d = StPhase1;

          inc_round = 1'b1;
        end
      end
    endcase
  end


  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)            state <= '{default:'0};
    else if (valid_i) begin
      state[0] <= state_i ^ rand_i;
      state[1] <= rand_i;
    end else if (update_state) begin
      state <= state_d;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) round <= '0;
    else if (valid_i) round <= '0;
    else if (inc_round)  round <= round + 1'b 1;
  end

  assign done_o = (round == NumRound);
  assign state_o = state[0] ^ state[1];

  logic [Width-1:0] keccak_in  [2];
  logic [Width-1:0] keccak_out [2];
  assign keccak_in = state;
  assign state_d = keccak_out;


  keccak_2share #(
    .Width (Width),
    .EnMasking (1)   // Masked version
  ) u_keccak (
    .clk_i,
    .rst_ni,

    .rnd_i        (round),
    .rand_valid_i (rand_valid_i),
    .rand_i       (rand_i),
    .sel_i        (sel_mux),
    .s_i          (keccak_in),
    .s_o          (keccak_out)
  );

  // Compare with keccak Unmasking
  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      golden_state <= '0;
    end else if (valid_i) begin
      golden_state <= state_i;
    end else if (keccak_st == StPhase3) begin
      golden_state <= golden_state_d[0];
    end
  end

  keccak_2share #(
    .Width (Width),
    .EnMasking (0) // Unmasked version
  ) u_golden (
    .clk_i,
    .rst_ni,

    .rnd_i (round),
    .rand_i ('0),
    .sel_i  ('0),
    .s_i    ('{golden_state}),
    .s_o    (golden_state_d)
  );

  assign compare_states = golden_state ^ state_o;

  `ASSUME_FPV(ValidSequence_A, ##1 valid_i |=> !valid_i)
  `ASSUME_FPV(ValidValid_A, keccak_st != StIdle |-> !valid_i)

  // Test with value 0
  logic [1599:0] data_0 ;
  always_comb begin
    data_0 = '0;
    // SHA3-256 ==> r : 1088
    data_0[1087] = 1'b 1;
    data_0[2:0] = 3'b 110;
  end
  logic [255:0] digest_0;
  // Big-Endian a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a
  assign digest_0 = 256'h 4a43_f880_4b0a_d882_fa49_3be4_4dff_80f5_62d6_61a0_5647_c151_66d7_1ebf_f8c6_ffa7;
  `ASSUME_FPV(FixedRandomValue_A, rand_i == '1)
  `ASSUME_FPV(Data0TestSHA3_256_A, state_i == data_0)
  `ASSERT(DigestForData0TestSHA3_256_A, done_o |-> state_o[255:0] == digest_0)

  // After a round is completed or at the beginning, golden value and keccak 2share shall be same
  `ASSERT(MaskedSameToUnmasked_A, keccak_st inside {StIdle, StPhase1} |-> compare_states == '0)

endmodule

