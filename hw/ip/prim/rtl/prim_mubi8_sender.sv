// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
//    util/design/gen-mubi.py
//
// Multibit sender module. This module is instantiates a hand-picked flop cell for each bit in the
// multibit signal such that tools do not optimize the multibit encoding.

`include "prim_assert.sv"

module prim_mubi8_sender
  import prim_mubi_pkg::*;
#(
  // This flops the output if set to 1.
  // In special cases where the sender is in the same clock domain as the receiver,
  // this can be set to 0. However, it is recommended to leave this at 1.
  parameter bit AsyncOn = 1,
  // Enable anchor buffer
  parameter bit EnSecBuf = 0,
  // Reset value for the sender flops
  parameter mubi8_t ResetValue = MuBi8False
) (
  input          clk_i,
  input          rst_ni,
  input  mubi8_t mubi_i,
  output mubi8_t mubi_o
);

  logic [MuBi8Width-1:0] mubi, mubi_int, mubi_out;
  assign mubi = MuBi8Width'(mubi_i);

  // first generation block decides whether a flop should be present
  if (AsyncOn) begin : gen_flops
    prim_flop #(
      .Width(MuBi8Width),
      .ResetValue(MuBi8Width'(ResetValue))
    ) u_prim_flop (
      .clk_i,
      .rst_ni,
      .d_i   ( mubi     ),
      .q_o   ( mubi_int )
    );
  end else begin : gen_no_flops
    assign mubi_int = mubi;

    // This unused companion logic helps remove lint errors
    // for modules where clock and reset are used for assertions only
    // This logic will be removed for sythesis since it is unloaded.
    mubi8_t unused_logic;
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
         unused_logic <= MuBi8False;
      end else begin
         unused_logic <= mubi_i;
      end
    end
  end

  // second generation block determines output buffer type
  // 1. If EnSecBuf -> always leads to a sec buffer regardless of first block
  // 2. If not EnSecBuf and not AsyncOn -> use normal buffer
  // 3. If not EnSecBuf and AsyncOn -> feed through
  if (EnSecBuf) begin : gen_sec_buf
    prim_sec_anchor_buf #(
      .Width(8)
    ) u_prim_sec_buf (
      .in_i(mubi_int),
      .out_o(mubi_out)
    );
  end else if (!AsyncOn) begin : gen_prim_buf
    prim_buf #(
      .Width(8)
    ) u_prim_buf (
      .in_i(mubi_int),
      .out_o(mubi_out)
    );
  end else begin : gen_feedthru
    assign mubi_out = mubi_int;
  end

  assign mubi_o = mubi8_t'(mubi_out);

  ////////////////
  // Assertions //
  ////////////////

  // The outputs should be known at all times.
  `ASSERT_KNOWN(OutputsKnown_A, mubi_o)

endmodule : prim_mubi8_sender
