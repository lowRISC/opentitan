// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface rng_if ();

  logic clk;
  logic rst_n;

  // interface pins
  logic enable;
  logic entropy_ok;
  logic [3:0] entropy;

endinterface
