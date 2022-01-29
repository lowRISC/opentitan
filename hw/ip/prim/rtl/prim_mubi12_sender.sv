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

module prim_mubi12_sender
  import prim_mubi_pkg::*;
#(
  // This flops the output if set to 1.
  // In special cases where the sender is in the same clock domain as the receiver,
  // this can be set to 0. However, it is recommended to leave this at 1.
  parameter bit AsyncOn = 1,
  // Reset value for the sender flops
  parameter mubi12_t ResetValue = MuBi12False
) (
  input          clk_i,
  input          rst_ni,
  input  mubi12_t mubi_i,
  output mubi12_t mubi_o
);

  logic [MuBi12Width-1:0] mubi, mubi_out;
  assign mubi = MuBi12Width'(mubi_i);

  if (AsyncOn) begin : gen_flops
    prim_flop #(
      .Width(MuBi12Width),
      .ResetValue(MuBi12Width'(ResetValue))
    ) u_prim_flop (
      .clk_i,
      .rst_ni,
      .d_i   ( mubi     ),
      .q_o   ( mubi_out )
    );
  end else begin : gen_no_flops
    for (genvar k = 0; k < MuBi12Width; k++) begin : gen_bits
      prim_buf u_prim_buf (
        .in_i(mubi[k]),
        .out_o(mubi_out[k])
      );
    end
    logic unused_clk;
    logic unused_rst;
    assign unused_clk = clk_i;
    assign unused_rst = rst_ni;
  end

  assign mubi_o = mubi12_t'(mubi_out);

  ////////////////
  // Assertions //
  ////////////////

  // The outputs should be known at all times.
  `ASSERT_KNOWN(OutputsKnown_A, mubi_o)

endmodule : prim_mubi12_sender
