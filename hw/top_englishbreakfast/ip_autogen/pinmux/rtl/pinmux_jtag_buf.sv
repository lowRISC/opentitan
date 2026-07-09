// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module pinmux_jtag_buf (
  // Gates TCK/TRSTN below. Holds this TAP's clock off and reset asserted when deselected.
  input  logic                en_i,
  input  jtag_pkg::jtag_req_t req_i,
  output jtag_pkg::jtag_req_t req_o,
  input  jtag_pkg::jtag_rsp_t rsp_i,
  output jtag_pkg::jtag_rsp_t rsp_o
);

  logic tck_gated;
  prim_and2 #(.Width(1)) u_prim_and2_tck (
    .in0_i(en_i),
    .in1_i(req_i.tck),
    .out_o(tck_gated)
  );
  // This buffer is used in the constraints to define a generated clock
  prim_clock_buf prim_clock_buf_tck (
    .clk_i(tck_gated),
    .clk_o(req_o.tck)
  );

  prim_and2 #(.Width(1)) u_prim_and2_trst_n (
    .in0_i(en_i),
    .in1_i(req_i.trst_n),
    .out_o(req_o.trst_n)
  );
  prim_buf prim_buf_tms (
    .in_i (req_i.tms),
    .out_o(req_o.tms)
  );
  prim_buf prim_buf_tdi (
    .in_i (req_i.tdi),
    .out_o(req_o.tdi)
  );
  prim_buf prim_buf_tdo (
    .in_i (rsp_i.tdo),
    .out_o(rsp_o.tdo)
  );
  prim_buf prim_buf_tdo_oe (
    .in_i (rsp_i.tdo_oe),
    .out_o(rsp_o.tdo_oe)
  );

endmodule : pinmux_jtag_buf
