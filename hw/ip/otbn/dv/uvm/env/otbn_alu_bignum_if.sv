// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Bound into the otbn_alu_bignum and used to help collect ISPR information for coverage.

interface otbn_alu_bignum_if (
  input         clk_i,
  input         rst_ni,

  // Signal names from the otbn_alu_bignum module (where we are bound)
  input [255:0] mod_q
);

endinterface
