// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Perform logical OR or AND between two life cycle multibit signals.

module prim_lc_combine #(
  // 0: use the ON value as active value for the logical combination
  // 1: use the OFF value as active value for the logical combination
  parameter bit ActiveLow = 0,
  // 0: logical combination is an OR function
  // 1: logical combination is an AND function
  parameter bit CombineMode = 0
) (
  input  lc_ctrl_pkg::lc_tx_t lc_en_a_i,
  input  lc_ctrl_pkg::lc_tx_t lc_en_b_i,
  output lc_ctrl_pkg::lc_tx_t lc_en_o
);

  // Determine whether which multibit value is considered "active" for the
  // purpose of the logical function below.
  localparam lc_ctrl_pkg::lc_tx_t ActiveValue = (ActiveLow) ? lc_ctrl_pkg::Off : lc_ctrl_pkg::On;
  // Truth tables:
  //
  // ActiveLow: 0, CombineMode: 0 (active-high "OR")
  //
  // A    | B    | OUT
  //------+------+-----
  // !On  | !On  | !On
  // On   | !On  | On
  // !On  | On   | On
  // On   | On   | On
  //
  // ActiveLow: 0, CombineMode: 1 (active-high "AND")
  //
  // A    | B    | OUT
  //------+------+-----
  // !On  | !On  | !On
  // On   | !On  | !On
  // !On  | On   | !On
  // On   | On   | On
  //
  // ActiveLow: 1, CombineMode: 0 (active-low "OR")
  //
  // A    | B    | OUT
  //------+------+-----
  // !Off | !Off | !Off
  // Off  | !Off | Off
  // !Off | Off  | Off
  // Off  | Off  | Off
  //
  // ActiveLow: 1, CombineMode: 1 (active-low "AND")
  //
  // A    | B    | OUT
  //------+------+-----
  // !Off | !Off | !Off
  // Off  | !Off | !Off
  // !Off | Off  | !Off
  // Off  | Off  | Off
  //
  // Note: the inactive value (e.g. !On) can be any multibit value
  // different from the active value.
  //
  for (genvar k = 0; k < $bits(ActiveValue); k++) begin : gen_loop
    if (CombineMode && ActiveValue[k] ||
       (!CombineMode && !ActiveValue[k])) begin : gen_and_gate
      assign lc_en_o[k] = lc_en_a_i[k] && lc_en_b_i[k];
    end else begin : gen_or_gate
      assign lc_en_o[k] = lc_en_a_i[k] || lc_en_b_i[k];
    end
  end

endmodule : prim_lc_combine
