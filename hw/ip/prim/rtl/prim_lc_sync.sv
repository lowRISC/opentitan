// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Double-synchronizer flop for life cycle control signals with additional
// output buffers and life-cycle specific assertions.
//
// Should be used exactly as recommended in the life cycle controller spec:
// https://docs.opentitan.org/hw/ip/lc_ctrl/doc/index.html#control-signal-propagation

`include "prim_assert.sv"

module prim_lc_sync #(
  // Number of separately buffered output signals.
  // The buffer cells have a don't touch constraint
  // on them such that synthesis tools won't collapse
  // all copies into one signal.
  parameter int NumCopies = 1,
  // This instantiates the synchronizer flops if set to 1.
  // In special cases where the receiver is in the same clock domain as the sender,
  // this can be set to 0. However, it is recommended to leave this at 1.
  parameter bit AsyncOn = 1
) (
  input                                       clk_i,
  input                                       rst_ni,
  input  lc_ctrl_pkg::lc_tx_t                 lc_en_i,
  output lc_ctrl_pkg::lc_tx_t [NumCopies-1:0] lc_en_o
);

  `ASSERT_INIT(NumCopiesMustBeGreaterZero_A, NumCopies > 0)

  logic [lc_ctrl_pkg::TxWidth-1:0] lc_en;
  if (AsyncOn) begin : gen_flops
    prim_flop_2sync #(
      .Width(lc_ctrl_pkg::TxWidth),
      .ResetValue(lc_ctrl_pkg::TxWidth'(lc_ctrl_pkg::Off))
    ) u_prim_flop_2sync (
      .clk_i,
      .rst_ni,
      .d_i(lc_en_i),
      .q_o(lc_en)
    );
  end else begin : gen_no_flops
    logic unused_clk;
    logic unused_rst;
    assign unused_clk = clk_i;
    assign unused_rst = rst_ni;
    assign lc_en = lc_en_i;
  end

  for (genvar j = 0; j < NumCopies; j++) begin : gen_buffs
    logic [lc_ctrl_pkg::TxWidth-1:0] lc_en_out;
    for (genvar k = 0; k < lc_ctrl_pkg::TxWidth; k++) begin : gen_bits
      prim_buf u_prim_buf (
        .in_i(lc_en[k]),
        .out_o(lc_en_out[k])
      );
    end
    assign lc_en_o[j] = lc_ctrl_pkg::lc_tx_t'(lc_en_out);
  end

  ////////////////
  // Assertions //
  ////////////////

  // The outputs should be known at all times.
  `ASSERT_KNOWN(OutputsKnown_A, lc_en_o)

  // If the multibit signal is in a transient state, we expect it
  // to be stable again within one clock cycle.
  `ASSERT(CheckTransients_A,
      !(lc_en_i inside {lc_ctrl_pkg::On, lc_ctrl_pkg::Off})
      |=>
      (lc_en_i inside {lc_ctrl_pkg::On, lc_ctrl_pkg::Off}))

  // If a signal departs from passive state, we expect it to move to the active state
  // with only one transient cycle in between.
  `ASSERT(CheckTransients0_A,
      $past(lc_en_i == lc_ctrl_pkg::Off) &&
      !(lc_en_i inside {lc_ctrl_pkg::On, lc_ctrl_pkg::Off})
      |=>
      (lc_en_i == lc_ctrl_pkg::On))

  `ASSERT(CheckTransients1_A,
      $past(lc_en_i == lc_ctrl_pkg::On) &&
      !(lc_en_i inside {lc_ctrl_pkg::On, lc_ctrl_pkg::Off})
      |=>
      (lc_en_i == lc_ctrl_pkg::Off))

endmodule : prim_lc_sync
