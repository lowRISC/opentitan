// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// WARNING: DO NOT USE THIS MODULE IF YOU DO NOT HAVE A GOOD REASON TO DO SO.
//
// This module is only meant to be used in special cases where a handshake synchronizer
// is not viable (this is for instance the case for the multibit life cycle signals).
// For handshake-based synchronization, consider using prim_sync_reqack_data.
//
//
// Description:
//
// This module implements a multibit synchronizer that employs a data consistency check to
// decide whether the synchronized multibit signal is stable and can be output or not.
//
// The number of consistency checkers can be controlled via NumChecks. Each check adds another
// delay register after the 2-flop synchronizer, and corresponding comparator that checks whether
// the register input is equal to the output of the last register in the chain. If all checks are
// successful, the output register is enabled such that the data can propagate to the output.
//
// This is illustrated bellow for NumChecks = 1:
//
//                  /--------\        /--------\        /--------\
//                  |        |        |        |        |        |
//    data_i --/--> |  flop  | --x--> |  flop  | --x--> |  flop  | --/--> data_o
//           Width  | 2 sync |   |    |        |   |    |        |
//                  |        |   |    |        |   |    |   en   |
//                  \--------/   |    \--------/   |    \--------/
//                               |                 v        ^
//                               |               /----\     |
//                               \-------------> | == | ----/
//                                               \----/
//
// Note: CDC tools will likely flag this module due to re-convergent logic.
//

`include "prim_assert.sv"

module prim_multibit_sync #(
  // Width of the multibit signal.
  parameter int               Width = 8,
  // Number of cycles the synchronized multi-bit signal needs to
  // be stable until it is relased to the output. Each check adds
  // a comparator and an additional delay register.
  parameter int               NumChecks = 1,
  // Reset value of the multibit signal.
  parameter logic [Width-1:0] ResetValue = '0
) (
  input clk_i,
  input rst_ni,
  input  logic [Width-1:0] data_i,
  output logic [Width-1:0] data_o
);

  `ASSERT_INIT(NumChecks_A, NumChecks >= 1)

  // First, synchronize the input data to this clock domain.
  logic [NumChecks:0][Width-1:0]   data_check_d;
  logic [NumChecks-1:0][Width-1:0] data_check_q;

  prim_flop_2sync #(
    .Width(Width),
    .ResetValue(ResetValue)
  ) i_prim_flop_2sync (
    .clk_i,
    .rst_ni,
    .d_i(data_i),
    .q_o(data_check_d[0])
  );

  // Shift register.
  assign data_check_d[NumChecks:1] = data_check_q[NumChecks-1:0];

  // Consistency check. Always compare to the output of the last register.
  logic [NumChecks-1:0] checks;
  for (genvar k = 0; k < NumChecks; k++) begin : gen_checks
    assign checks[k] = (data_check_d[k] == data_check_d[NumChecks]);
    // Output is only allowed to change when all checks have passed.
    `ASSERT(StableCheck_A,
          data_o != $past(data_o)
          |->
          $past(data_check_d[k]) == $past(data_check_d[NumChecks]))
  end : gen_checks

  // Only propagate to output register if all checks have passed.
  logic [Width-1:0] data_synced_d, data_synced_q;
  assign data_synced_d = (&checks) ? data_check_d[NumChecks] : data_synced_q;
  assign data_o = data_synced_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      data_synced_q <= ResetValue;
      data_check_q  <= {NumChecks{ResetValue}};
    end else begin
      data_synced_q <= data_synced_d;
      data_check_q  <= data_check_d[NumChecks-1:0];
    end
  end

  `ASSERT_KNOWN(DataKnown_A, data_o)

endmodule : prim_multibit_sync
