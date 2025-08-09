// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module gpio_strap_check #(parameter int NUM_GPIOS = 32)
(
  input logic                 clk_i,
  input logic                 rst_ni,
  input logic                 strap_en_i,
  input logic                 strap_valid,
  input logic [NUM_GPIOS-1:0] strap_data,
  input logic [NUM_GPIOS-1:0] gpio_i
);

  // Ensure `strap_valid` is high one clock cycle after `strap_en_i` is high.
  `ASSERT(StrapValid_A, strap_en_i |=> strap_valid);
  // Check if strap output data is mirrored from gpio_i input data,
  // one clock cycle after the strap_en is high.
  `ASSERT(StrapSamples_A, $rose(strap_valid) |-> (strap_data == $past(gpio_i)));
  `ASSERT(StrapDataStable_A, strap_valid && $stable(strap_valid) -> $stable(strap_data));
  // Check if the strap_valid never fell.
  `ASSERT(StrapValidStable_A, ##1 !$fell(strap_valid));
  // Check if we have a strap valid signal high, then the strap en
  // must be high one clock cycle before.
  `ASSERT(StrapValidLow_A, $rose(strap_valid) |-> $past(strap_en_i));
  // Ensure that strap_valid is low after reset.
  `ASSERT(StrapValidReset_A, $rose(rst_ni) |-> !strap_valid);

endmodule
