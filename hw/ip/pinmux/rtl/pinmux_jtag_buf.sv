// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module pinmux_jtag_buf (
  input  jtag_pkg::jtag_req_t req_i,
  output jtag_pkg::jtag_req_t req_o,
  input  jtag_pkg::jtag_rsp_t rsp_i,
  output jtag_pkg::jtag_rsp_t rsp_o
);

  prim_clock_buf prim_clock_buf_tck (
    .clk_i(req_i.tck),
    .clk_o(req_o.tck)
  );
  prim_buf prim_buf_trst_n (
    .in_i (req_i.trst_n),
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
