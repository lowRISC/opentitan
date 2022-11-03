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
  // This controls whether the mubi module institutes stability checks when
  // AsyncOn is set.  If stability checks are on, a 3rd stage of storage is
  // added after the synchronizers and the outputs only updated if the 3rd
  // stage and sychronizer agree.  If they do not agree, the ResetValue is
  // output instead.
  parameter bit StabilityCheck = 0,
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
    logic [MuBi4Width-1:0] mubi_sync;
    prim_flop_2sync #(
      .Width(MuBi4Width),
      .ResetValue(MuBi4Width'(ResetValue))
    ) u_prim_flop_2sync (
      .clk_i,
      .rst_ni,
      .d_i(MuBi4Width'(mubi_i)),
      .q_o(mubi_sync)
    );

    if (StabilityCheck) begin : gen_stable_chks
      logic [MuBi4Width-1:0] mubi_q;
      prim_flop #(
        .Width(MuBi4Width),
        .ResetValue(MuBi4Width'(ResetValue))
      ) u_prim_flop_3rd_stage (
        .clk_i,
        .rst_ni,
        .d_i(mubi_sync),
        .q_o(mubi_q)
      );

      logic [MuBi4Width-1:0] sig_unstable;
      prim_xor2 #(
        .Width(MuBi4Width)
      ) u_mubi_xor (
        .in0_i(mubi_sync),
        .in1_i(mubi_q),
        .out_o(sig_unstable)
      );

      logic [MuBi4Width-1:0] reset_value;
      assign reset_value = ResetValue;

      for (genvar k = 0; k < MuBi4Width; k++) begin : gen_bufs_muxes
        logic [MuBi4Width-1:0] sig_unstable_buf;

        // each mux gets its own buffered output, this ensures the OR-ing
        // cannot be defeated in one place.
        prim_sec_anchor_buf #(
          .Width(MuBi4Width)
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

// Note regarding SVAs below:
//
// 1) Without the sampled rst_ni pre-condition, this may cause false assertion failures right after
// a reset release, since the "disable iff" condition with the rst_ni is sampled in the "observed"
// SV scheduler region after all assignments have been evaluated (see also LRM section 16.12, page
// 423). This is a simulation artifact due to reset synchronization in RTL, which releases rst_ni
// on the active clock edge. This causes the assertion to evaluate although the reset was actually
// 0 when entering this simulation cycle.
//
// 2) Similarly to 1) there can be sampling mismatches of the lc_en_i signal since that signal may
// originate from a different clock domain. I.e., in cases where the lc_en_i signal changes exactly
// at the same time that the clk_i signal rises, the SVA will not pick up that change in that clock
// cycle, whereas RTL will because SVAs sample values in the "preponed" region. To that end we make
// use of an RTL helper variable to sample the lc_en_i signal, hence ensuring that there are no
// sampling mismatches.
`ifdef INC_ASSERT
      mubi4_t mubi_in_sva_q;
      always_ff @(posedge clk_i) begin
        mubi_in_sva_q <= mubi_i;
      end
      `ASSERT(OutputIfUnstable_A, sig_unstable |-> mubi_o == {NumCopies{reset_value}})
      `ASSERT(OutputDelay_A,
              rst_ni |-> ##[3:4] sig_unstable || mubi_o == {NumCopies{$past(mubi_in_sva_q, 2)}})
`endif
    end else begin : gen_no_stable_chks
      assign mubi = mubi_sync;
`ifdef INC_ASSERT
      mubi4_t mubi_in_sva_q;
      always_ff @(posedge clk_i) begin
        mubi_in_sva_q <= mubi_i;
      end
      `ASSERT(OutputDelay_A,
              rst_ni |-> ##3 (mubi_o == {NumCopies{$past(mubi_in_sva_q, 2)}} ||
                              $past(mubi_in_sva_q, 2) != $past(mubi_in_sva_q, 1)))
`endif
    end
  end else begin : gen_no_flops

    //VCS coverage off
    // pragma coverage off

    // This unused companion logic helps remove lint errors
    // for modules where clock and reset are used for assertions only
    // This logic will be removed for synthesis since it is unloaded.
    mubi4_t unused_logic;
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
         unused_logic <= MuBi4False;
      end else begin
         unused_logic <= mubi_i;
      end
    end

    //VCS coverage on
    // pragma coverage on

    assign mubi = MuBi4Width'(mubi_i);

    `ASSERT(OutputDelay_A, mubi_o == {NumCopies{mubi_i}})
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

endmodule : prim_mubi4_sync
