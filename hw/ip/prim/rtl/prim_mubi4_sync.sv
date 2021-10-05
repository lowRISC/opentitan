// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
//    hw/ip/prim/util/generate_prim_mubi.py
//
// Double-synchronizer flop for multibit signals with additional output buffers.

`include "prim_assert.sv"

module prim_mubi4_sync
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
  // Reset value for the sync flops
  parameter mubi4_t ResetValue = MuBi4False
) (
  input                          clk_i,
  input                          rst_ni,
  input  mubi4_t                 mubi_i,
  output mubi4_t [NumCopies-1:0] mubi_o
);

  `ASSERT_INIT(NumCopiesMustBeGreaterZero_A, NumCopies > 0)

  logic [MuBi4Width-1:0] mubi;
  if (AsyncOn) begin : gen_flops
    prim_flop_2sync #(
      .Width(MuBi4Width),
      .ResetValue(MuBi4Width'(ResetValue))
    ) u_prim_flop_2sync (
      .clk_i,
      .rst_ni,
      .d_i(mubi_i),
      .q_o(mubi)
    );
  end else begin : gen_no_flops
    logic unused_clk;
    logic unused_rst;
    assign unused_clk = clk_i;
    assign unused_rst = rst_ni;
    assign mubi = mubi_i;
  end

  for (genvar j = 0; j < NumCopies; j++) begin : gen_buffs
    logic [MuBi4Width-1:0] mubi_out;
    for (genvar k = 0; k < MuBi4Width; k++) begin : gen_bits
      prim_buf u_prim_buf (
        .in_i(mubi[k]),
        .out_o(mubi_out[k])
      );
    end
    assign mubi_o[j] = mubi4_t'(mubi_out);
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
  `ASSERT(PrimMubi4SyncCheckTransients_A,
      !(mubi_i inside {MuBi4True, MuBi4False})
      |=>
      (mubi_i inside {MuBi4True, MuBi4False}))

  // If a signal departs from passive state, we expect it to move to the active state
  // with only one transient cycle in between.
  `ASSERT(PrimMubi4SyncCheckTransients0_A,
      $past(mubi_i == MuBi4False) &&
      !(mubi_i inside {MuBi4True, MuBi4False})
      |=>
      (mubi_i == MuBi4True))

  `ASSERT(PrimMubi4SyncCheckTransients1_A,
      $past(mubi_i == MuBi4True) &&
      !(mubi_i inside {MuBi4True, MuBi4False})
      |=>
      (mubi_i == MuBi4False))

endmodule : prim_mubi4_sync
