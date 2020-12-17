// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module prim_generic_buf (
  input in_i,
  output logic out_o
);

  assign out_o = in_i;

endmodule : prim_generic_buf
