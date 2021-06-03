// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Bound into the otbn_mac_bignum and used to help collect ISPR information for coverage.

interface otbn_mac_bignum_if (
  input         clk_i,
  input         rst_ni,

  // Signal names from the otbn_mac_bignum module (where we are bound)
  input logic [255:0] adder_op_a,
  input logic [255:0] adder_op_b
);

  // Return the intermediate sum (the value of ACC before it gets truncated back down to 256 bits).
  function automatic logic [256:0] get_sum_value();
    return {1'b0, adder_op_a} + {1'b0, adder_op_b};
  endfunction

endinterface
