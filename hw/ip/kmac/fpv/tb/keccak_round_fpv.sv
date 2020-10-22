// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for keccak_f. Intended to be used with a formal tool.

module keccak_round_fpv #(
  parameter int Width = 1600
) (
  input                    clk_i,
  input                    rst_ni,
  input                    valid_i,
  input                    rand_valid_i,
  input        [Width-1:0] rand_i,
  output logic             done_o
);

  localparam int W        = Width/25;
  localparam int L        = $clog2(W);
  localparam int NumRound = 12 + 2*L; // Keccak-f only
  localparam int RndW     = $clog2(NumRound+1);

  // Feed parameters
  localparam int DInWidth = 64; // currently only 64bit supported
  localparam int DInEntry = Width / DInWidth;
  localparam int DInAddr  = $clog2(DInEntry);

  logic [Width-1:0] masked_state   [2];
  logic [Width-1:0] masked_state_d [2];
  logic [Width-1:0] unmasked_state  [1];
  logic [Width-1:0] unmasked_state_d[1];

  // Data input
  logic                msg_valid;
  logic [DInAddr-1:0]  msg_addr;
  logic [DInWidth-1:0] msg_data;
  logic                msg_ready_masked, msg_ready_unmasked;

  logic run, clear, masked_complete, unmasked_complete;

  // Masked Keccak round

  keccak_round #(
    .Width      (Width),
    .EnMasking  (1),
    .ReuseShare (0)
  ) u_masked (
    .clk_i,
    .rst_ni,

    .valid_i (msg_valid),
    .addr_i  (msg_addr),
    .data_i  ({'0, msg_data}),
    .ready_o (msg_ready_masked),

    .run_i   (run),
    .rand_valid_i (1'b1),
    .rand_data_i  ('0),
    .rand_consumed_o (),

    .complete_o (masked_complete),
    .state_o    (masked_state),
    .clear_i    (clear)
  );

  keccak_round #(
    .Width      (Width),
    .EnMasking  (0)
  ) u_unmasked (
    .clk_i,
    .rst_ni,

    .valid_i (msg_valid),
    .addr_i  (msg_addr),
    .data_i  ('{msg_data}),
    .ready_o (msg_ready_unmasked),

    .run_i   (run),
    .rand_valid_i (1'b1),
    .rand_data_i  ('0),
    .rand_consumed_o (),

    .complete_o (unmasked_complete),
    .state_o    (unmasked_state),
    .clear_i    (clear)
  );

  logic [Width-1:0] compare_states;

  assign compare_states = unmasked_state[0] ^ (masked_state[0] ^ masked_state[1]);

  // Test with value 0
  logic [1599:0] data_0 ;
  always_comb begin
    data_0 = '0;
    // SHA3-256 ==> r : 1088
    data_0[1087] = 1'b 1;
    data_0[2:0] = 3'b 110;
  end

  // Data input : SHA3-256

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      msg_addr <= '0;
    end else if (msg_valid) begin
      msg_addr <= msg_addr + 1'b 1;
    end else if (run) begin
      msg_addr <= '0;
    end
  end

  assign msg_data = data_0[64*msg_addr+:64];

  logic in_progress;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      in_progress <= 1'b0;
    end else if (valid_i) begin
      in_progress <= 1'b 1;
    end else if (done_o) begin
      in_progress <= 1'b 0;
    end
  end

  typedef enum logic [2:0] {
    StIdle,
    StMsg,
    StRun,
    StComplete
  } st_e;

  st_e st, st_d;


  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      st <= StIdle;
    end else begin
      st <= st_d;
    end
  end

  always_comb begin
    st_d = st;

    run = 1'b0;
    msg_valid = 1'b0;
    done_o = 1'b0;

    clear = 1'b 0;

    unique case (st)
      StIdle: begin
        if (valid_i) begin
          st_d = StMsg;
        end
      end

      StMsg: begin
        if (msg_addr == 1088/64) begin
          st_d = StRun;

          run = 1'b1;
        end else begin
          st_d = StMsg;

          msg_valid = 1'b1;
        end
      end

      StRun: begin
        if (masked_complete) begin
          st_d = StComplete;
        end else begin
          st_d = StRun;
        end
      end

      StComplete: begin
        st_d = StIdle;
        clear = 1'b1;
        done_o = 1'b1;
      end

      default: begin
        st_d = StIdle;
      end
    endcase
  end

  //`ASSUME_FPV(DataNotPushWhenProgress_A, msg_valid |-> !in_progress && !valid_i)
  `ASSUME_FPV(ValidPulse_A, ##1 valid_i |=> !valid_i, clk_i, !rst_ni)


  logic [255:0] digest_0;
  // Big-Endian a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a
  assign digest_0 = 256'h 4a43_f880_4b0a_d882_fa49_3be4_4dff_80f5_62d6_61a0_5647_c151_66d7_1ebf_f8c6_ffa7;
  `ASSUME_FPV(FixedRandomValue_A, rand_i == '1)
  `ASSUME_FPV(FixedRandomValid_A, rand_valid_i == '1)
  `ASSERT(DigestForData0TestSHA3_256_Masked_A,
          masked_complete |-> (masked_state[0][255:0] ^ masked_state[1][255:0]) == digest_0,
          clk_i, !rst_ni)
  `ASSERT(DigestForData0TestSHA3_256_Unmasked_A,
          unmasked_complete |-> unmasked_state[0][255:0] == digest_0,
          clk_i, !rst_ni)

  // After a round is completed or at the beginning, golden value and keccak 2share shall be same
  `ASSERT(MaskedSameToUnmasked_A, masked_complete |-> compare_states == '0, clk_i, !rst_ni)

endmodule

