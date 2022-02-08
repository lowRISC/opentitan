// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
//    util/design/gen-mubi.py
//
// Double-synchronizer flop for multibit signals with additional output buffers.

`include "prim_assert.sv"

module prim_mubi16_sync
  import prim_mubi_pkg::*;
#(
  // Number of separately buffered output signals.
  // The buffer cells have a don't touch constraint
  // on them such that synthesis tools won't collapse
  // all copies into one signal.
  parameter int NumCopies = 1,
  // This instantiates the synchronizer flops if set to 1.
  // In special cases where the receiver is in the same clock domain as the sender,
  // this can be set to 0. However, it is recommended to leave this at 1.
  parameter bit AsyncOn = 1,
  // This controls whether the mubi module institutes stability checks when
  // AsyncOn is set.  If stability checks are on, a 3rd stage of storage is
  // added after the synchronizers and the outputs only updated if the 3rd
  // stage and sychronizer agree.  If they do not agree, the ResetValue is
  // output instead.
  parameter bit StabilityCheck = 0,
  // Reset value for the sync flops
  parameter mubi16_t ResetValue = MuBi16False
) (
  input                          clk_i,
  input                          rst_ni,
  input  mubi16_t                 mubi_i,
  output mubi16_t [NumCopies-1:0] mubi_o
);

  `ASSERT_INIT(NumCopiesMustBeGreaterZero_A, NumCopies > 0)

  logic [MuBi16Width-1:0] mubi;
  if (AsyncOn) begin : gen_flops
    logic [MuBi16Width-1:0] mubi_sync;
    prim_flop_2sync #(
      .Width(MuBi16Width),
      .ResetValue(MuBi16Width'(ResetValue))
    ) u_prim_flop_2sync (
      .clk_i,
      .rst_ni,
      .d_i(MuBi16Width'(mubi_i)),
      .q_o(mubi_sync)
    );

    if (StabilityCheck) begin : gen_stable_chks
      logic [MuBi16Width-1:0] mubi_q;
      prim_flop #(
        .Width(MuBi16Width),
        .ResetValue(MuBi16Width'(ResetValue))
      ) u_prim_flop_3rd_stage (
        .clk_i,
        .rst_ni,
        .d_i(mubi_sync),
        .q_o(mubi_q)
      );

      logic [MuBi16Width-1:0] sig_unstable;
      prim_xor2 #(
        .Width(MuBi16Width)
      ) u_mubi_xor (
        .in0_i(mubi_sync),
        .in1_i(mubi_q),
        .out_o(sig_unstable)
      );

      logic [MuBi16Width-1:0] reset_value;
      assign reset_value = ResetValue;

      for (genvar k = 0; k < MuBi16Width; k++) begin : gen_bufs_muxes
        logic [MuBi16Width-1:0] sig_unstable_buf;

        // each mux gets its own buffered output, this ensures the OR-ing
        // cannot be defeated in one place.
        prim_sec_anchor_buf #(
          .Width(MuBi16Width)
        ) u_sig_unstable_buf (
          .in_i(sig_unstable),
          .out_o(sig_unstable_buf)
        );

        // if any xor indicates signal is unstable, output the reset
        // value.
        prim_clock_mux2 #(
          .NoFpgaBufG(1'b1)
        ) u_mux (
          .clk0_i(mubi_q[k]),
          .clk1_i(reset_value[k]),
          .sel_i(|sig_unstable_buf),
          .clk_o(mubi[k])
        );
      end

    end else begin : gen_no_stable_chks
      assign mubi = mubi_sync;
    end
  end else begin : gen_no_flops

    // This unused companion logic helps remove lint errors
    // for modules where clock and reset are used for assertions only
    // This logic will be removed for synthesis since it is unloaded.
    mubi16_t unused_logic;
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
         unused_logic <= MuBi16False;
      end else begin
         unused_logic <= mubi_i;
      end
    end

    assign mubi = MuBi16Width'(mubi_i);
  end

  for (genvar j = 0; j < NumCopies; j++) begin : gen_buffs
    logic [MuBi16Width-1:0] mubi_out;
    for (genvar k = 0; k < MuBi16Width; k++) begin : gen_bits
      prim_buf u_prim_buf (
        .in_i(mubi[k]),
        .out_o(mubi_out[k])
      );
    end
    assign mubi_o[j] = mubi16_t'(mubi_out);
  end

  ////////////////
  // Assertions //
  ////////////////

  // The outputs should be known at all times.
  `ASSERT_KNOWN(OutputsKnown_A, mubi_o)

  // If the multibit signal is in a transient state, we expect it
  // to be stable again within one clock cycle.
  // DV will exclude these three assertions by name, thus added a module name prefix to make it
  // harder to accidentally replicate in other modules.
  `ASSERT(PrimMubi16SyncCheckTransients_A,
      !(mubi_i inside {MuBi16True, MuBi16False})
      |=>
      (mubi_i inside {MuBi16True, MuBi16False}))

  // If a signal departs from passive state, we expect it to move to the active state
  // with only one transient cycle in between.
  `ASSERT(PrimMubi16SyncCheckTransients0_A,
      $past(mubi_i == MuBi16False) &&
      !(mubi_i inside {MuBi16True, MuBi16False})
      |=>
      (mubi_i == MuBi16True))

  `ASSERT(PrimMubi16SyncCheckTransients1_A,
      $past(mubi_i == MuBi16True) &&
      !(mubi_i inside {MuBi16True, MuBi16False})
      |=>
      (mubi_i == MuBi16False))

endmodule : prim_mubi16_sync
