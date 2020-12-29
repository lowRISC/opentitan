// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Keccak full round logic based on given input `Width`
// e.g. Width 800 requires 22 rounds

`include "prim_assert.sv"

module keccak_round #(
  parameter int Width = 1600, // b= {25, 50, 100, 200, 400, 800, 1600}

  // Derived
  localparam int W        = Width/25,
  localparam int L        = $clog2(W),
  localparam int MaxRound = 12 + 2*L,           // Keccak-f only
  localparam int RndW     = $clog2(MaxRound+1), // Representing up to MaxRound-1

  // Feed parameters
  parameter  int DInWidth = 64, // currently only 64bit supported
  localparam int DInEntry = Width / DInWidth,
  localparam int DInAddr  = $clog2(DInEntry),

  // Control parameters
  parameter  bit EnMasking = 0,  // Enable secure hardening
  localparam int Share     = EnMasking ? 2 : 1,

  // If ReuseShare is not 0, the logic will use unused sheet as an entropy
  // at Chi stage. It still needs small portion of the fresh entropy from
  // rand_data_i but the amount required are significantly small.
  // TODO: Implement the feature inside keccak_2share
  parameter  int ReuseShare = 0  // Re-use adjacent share for entropy
) (
  input clk_i,
  input rst_ni,

  // Message Feed
  input                valid_i,
  input [DInAddr-1:0]  addr_i,
  input [DInWidth-1:0] data_i [Share],
  output               ready_o,

  // In-process control
  input                    run_i,  // Pulse signal to initiates Keccak full round
  input                    rand_valid_i,
  input        [Width-1:0] rand_data_i,
  output logic             rand_consumed_o,

  output logic             complete_o, // Indicates full round is done

  // State out. This can be used as Digest
  output logic [Width-1:0] state_o [Share],

  input                    clear_i     // Clear internal state to '0
);

  /////////////////////
  // Control signals //
  /////////////////////

  // Update storage register
  logic update_storage;

  // Reset the storage to 0 to initiate new Hash operation
  logic rst_storage;

  // XOR message into storage register
  // It only does based on the given DInWidth.
  // If DInWidth < Width, it takes multiple cycles to XOR all message
  logic xor_message;

  // Select Keccak_p datapath
  // 0: Select Phase1 (Theta -> Rho -> Pi)
  // 1: Select Phase2 (Chi -> Iota)
  // `sel_mux` need to be asserted until the Chi stage is consumed,
  // It means sel_mux should be 1 until one cycle after `rand_valid_i` is asserted.
  logic sel_mux;


  // Increase/ Reset Round number
  logic inc_rnd_num;
  logic rst_rnd_num;

  // Round reaches end
  // This signal indicates the round reaches desired number, which is MaxRound -1.
  // MaxRound is dependant on the Width. In case of SHA3/SHAKE, MaxRound is 24.
  logic rnd_eq_end;

  // Complete of Keccak_f
  // State machine asserts `complete_d` when it reaches at the end of round and
  // operation (Phase3 if Masked). The the stage, the storage still doesn't have
  // the valid states. So precisely it is not completed yet.
  // State generated `complete_d` is latched with the clock and creates a pulse
  // signal one cycle later. The signal is the indication of completion.
  //
  // Intentionally removed any intermediate step (so called StComplete) in order
  // to save a clock to proceeds next round.
  logic complete_d;

  //////////////////////
  // Datapath Signals //
  //////////////////////

  // Single round keccak output data
  logic [Width-1:0] keccak_out [Share];

  // Keccak Round indicator: range from 0 .. MaxRound
  logic [RndW-1:0] round;

  // Random value and valid signal used in Keccak_p
  // There's plan to make random value generation configurable.
  // 1. Tied to 0 in case of random value is not needed. It means the Keccak
  //    doesn't need to be masked and throughput is the most important thing.
  // 2. Receive random value from entropy source. This requires to fill 1600b
  //    of entropy. It takes long time so generally it will have smaller bits
  //    from tru entropy source and expands to 1600b (Width).
  // 3. Reuse Share. This option is to reuse the other part of share. Chi stage
  //    uses 3 sheets to create a sheet. (newX = X ^ (~(X+1) & (X+2))). So the
  //    other two shares (X-1, X-2) can be assumed as random values, and may be
  //    used as entropy source. It is weaker than the use of true entropy, but
  //    much faster.
  logic             keccak_rand_valid, keccak_rand_consumed;
  logic [Width-1:0] keccak_rand_data;

  //////////////////////
  // Keccak Round FSM //
  //////////////////////

  // state inputs
  assign rnd_eq_end = (round == MaxRound - 1);

  typedef enum logic [2:0] {
      StIdle,

      // Active state is used in Unmasked version only.
      // It handles keccak round in a cycle
      StActive,

      // Phase1 --> Phase2 --> Phase3
      // Activated only in Masked version.
      // Phase1 processes Theta, Rho, Pi steps in a cycle and stores the states
      // into storage. It unconditionally moves to Phase2.
      StPhase1,

      // First half part of Chi step. It waits random value is ready
      // then move to Phase 3.
      StPhase2,

      // Second half of Chi step and Iota step.
      // This state doesn't require random value as it is XORed into the states
      // in Phase2. If round is reached to the end (MaxRound -1) then it
      // completes the process and goes back to Idle. If not, repeats the Phase
      // again.
      StPhase3,

      // Error state. Not clearly defined yet.
      // Intention is if any unexpected input in the process, state moves to
      // here and report through the error fifo with debugging information.
      StError
  } keccak_st_e;
  keccak_st_e keccak_st, keccak_st_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      keccak_st <= StIdle;
    end else begin
      keccak_st <= keccak_st_d;
    end
  end

  // Next state logic and output logic
  always_comb begin
    // Default values
    keccak_st_d = StIdle;

    xor_message    = 1'b 0;
    update_storage = 1'b 0;
    rst_storage    = 1'b 0;

    inc_rnd_num = 1'b 0;
    rst_rnd_num = 1'b 0;

    keccak_rand_consumed = 1'b 0;

    sel_mux = 1'b 0;

    complete_d = 1'b 0;

    unique case (keccak_st)
      StIdle: begin
        if (valid_i) begin
          // State machine allows Sponge Absorbing only in Idle state.
          keccak_st_d = StIdle;

          xor_message    = 1'b 1;
          update_storage = 1'b 1;
        end else if (clear_i) begin
          // Opt1. State machine allows resetting the storage only in Idle
          // Opt2. storage resets regardless of states but clear_i
          // Both are added in the design at this time. Will choose the
          // direction later.
          keccak_st_d = StIdle;

          rst_storage = 1'b 1;
        end else if (EnMasking && run_i) begin
          // Masked version of Keccak handling
          keccak_st_d = StPhase1;
        end else if (!EnMasking && run_i) begin
          // Unmasked version of Keccak handling
          keccak_st_d = StActive;
        end else begin
          keccak_st_d = StIdle;
        end
      end

      StActive: begin
        // Run Keccak single round logic until it reaches MaxRound - 1
        update_storage = 1'b 1;

        if (rnd_eq_end) begin
          keccak_st_d = StIdle;

          rst_rnd_num = 1'b 1;
          complete_d  = 1'b 1;
        end else begin
          keccak_st_d = StActive;

          inc_rnd_num = 1'b 1;
        end
      end

      StPhase1: begin
        // Unconditionally move to next phase.
        keccak_st_d = StPhase2;

        update_storage = 1'b 1;
        sel_mux        = 1'b 0;
      end

      StPhase2: begin
        // Second phase (Chi 1/2)
        sel_mux = 1'b 1;

        if (keccak_rand_valid) begin
          keccak_st_d = StPhase3;

          keccak_rand_consumed = 1'b 1;
        end else begin
          keccak_st_d = StPhase2;
        end
      end

      StPhase3: begin
        sel_mux = 1'b 1;
        update_storage = 1'b 1;

        if (rnd_eq_end) begin
          keccak_st_d = StIdle;

          rst_rnd_num    = 1'b 1;
          complete_d     = 1'b 1;
        end else begin
          keccak_st_d = StPhase1;

          inc_rnd_num = 1'b 1;
        end
      end

      StError: begin
        keccak_st_d = StIdle;
      end

      default: begin
        keccak_st_d = StError;
      end
    endcase
  end

  // Ready indicates the keccak_round is able to receive new message.
  // While keccak_round is processing the data, it blocks the new message to be
  // XORed into the current state.
  assign ready_o = (keccak_st == StIdle) ? 1'b 1 : 1'b 0;

  ////////////////////////////
  // Keccak state registers //
  ////////////////////////////
  logic [Width-1:0] storage   [Share];
  logic [Width-1:0] storage_d [Share];
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      storage <= '{default:'0};
    end else if (rst_storage) begin
      storage <= '{default:'0};
    end else if (update_storage) begin
      storage <= storage_d;
    end
  end

  assign state_o = storage;

  // Storage register input
  // The incoming message is XORed with the existing storage registers.
  // The logic can accept not a block size incoming message chunk but
  // the size defined in `DInWidth` parameter with its position.

  always_comb begin
    storage_d = keccak_out;
    if (xor_message) begin
      for (int j = 0 ; j < Share ; j++) begin
        for (int i = 0 ; i < DInEntry ; i++) begin
          // TODO: handle If Width is not integer divisable by DInWidth
          // Currently it is not allowed to have partial write
          // Please see the Assertion `WidthDivisableByDInWidth_A`
          if (addr_i == $unsigned(i)) begin
            storage_d[j][i*DInWidth+:DInWidth] =
              storage[j][i*DInWidth+:DInWidth] ^ data_i[j];
          end else begin
            storage_d[j][i*DInWidth+:DInWidth] = storage[j][i*DInWidth+:DInWidth];
          end
        end // for i
      end // for j
    end // if xor_message
  end

  //////////////
  // Datapath //
  //////////////
  keccak_2share #(
    .Width     (Width),
    .EnMasking (EnMasking)
  ) u_keccak_p (
    .clk_i,
    .rst_ni,

    .rnd_i           (round),
    .rand_valid_i    (keccak_rand_valid),
    .rand_i          (keccak_rand_data),
    .sel_i           (sel_mux),
    .s_i             (storage),
    .s_o             (keccak_out)
  );

  // keccak entropy handling
  // TODO: Consider reuse of internal share
  assign keccak_rand_valid = rand_valid_i;
  assign rand_consumed_o = keccak_rand_consumed;

  assign keccak_rand_data = rand_data_i;
  `ASSERT_INIT(NoReuseShare_A, ReuseShare == 0)

  // Round number
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      round <= '0;
    end else if (rst_rnd_num) begin
      round <= '0;
    end else if (inc_rnd_num) begin
      round <= round + 1'b 1;
    end
  end

  // completion signal
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      complete_o <= 1'b 0;
    end else begin
      complete_o <= complete_d;
    end
  end

  ////////////////
  // Assertions //
  ////////////////

  // Only allow `DInWidth` that `Width` is integer divisable by `DInWidth`
  `ASSERT_INIT(WidthDivisableByDInWidth_A, (Width % DInWidth) == 0)

  // If `run_i` triggerred, it shall complete
  //`ASSERT(RunResultComplete_A, run_i ##[MaxRound:] complete_o, clk_i, !rst_ni)

  // valid_i and run_i cannot be asserted at the same time
  `ASSUME(OneHot0ValidAndRun_A, $onehot0({valid_i, run_i}), clk_i, !rst_ni)

  // valid_i, run_i only asserted in Idle state
  `ASSUME(ValidRunAssertStIdle_A, valid_i || run_i |-> keccak_st == StIdle, clk_i, !rst_ni)

  // clear_i is assumed to be asserted in Idle state
  `ASSUME(ClearAssertStIdle_A, clear_i |-> keccak_st == StIdle, clk_i, !rst_ni)

  // EnMasking controls the valid states
  if (EnMasking) begin : gen_mask_st_chk
    `ASSERT(EnMaskingValidStates_A, keccak_st != StActive, clk_i, !rst_ni)
  end else begin : gen_unmask_st_chk
    `ASSERT(UnmaskValidStates_A, !(keccak_st inside {StPhase1, StPhase2, StPhase3}),
            clk_i, !rst_ni)
  end

  // If message is fed, it shall start from 0
  // TODO: Handle the case `addr_i` changes prior to `valid_i`
  //`ASSUME(MsgStartFrom0_A, valid_i |->
  //                         (addr_i == 0) || (addr_i == $past(addr_i) + 1),
  //        clk_i,!rst_ni)


endmodule

