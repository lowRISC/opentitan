// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module prim_xilinx_buf (
  input in_i,
  (* keep = "true" *) output logic out_o
);

  assign out_o = in_i;

endmodule : prim_xilinx_buf
