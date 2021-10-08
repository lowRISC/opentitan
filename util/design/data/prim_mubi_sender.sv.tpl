// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
//    hw/ip/prim/util/generate_prim_mubi.py
//
// Multibit sender module. This module is instantiates a hand-picked flop cell for each bit in the
// multibit signal such that tools do not optimize the multibit encoding.

`include "prim_assert.sv"

module prim_mubi${n_bits}_sender
  import prim_mubi_pkg::*;
#(
  // Reset value for the sender flops
  parameter mubi${n_bits}_t ResetValue = MuBi${n_bits}False
) (
  input          clk_i,
  input          rst_ni,
  input  mubi${n_bits}_t mubi_i,
  output mubi${n_bits}_t mubi_o
);

  logic [MuBi${n_bits}Width-1:0] mubi, mubi_out;
  assign mubi = MuBi${n_bits}Width'(mubi_i);

  prim_flop #(
    .Width(MuBi${n_bits}Width),
    .ResetValue(MuBi${n_bits}Width'(ResetValue))
  ) u_prim_flop (
    .clk_i,
    .rst_ni,
    .d_i   ( mubi     ),
    .q_o   ( mubi_out )
  );

  assign mubi_o = mubi${n_bits}_t'(mubi_out);

  ////////////////
  // Assertions //
  ////////////////

  // The outputs should be known at all times.
  `ASSERT_KNOWN(OutputsKnown_A, mubi_o)

endmodule : prim_mubi${n_bits}_sender
