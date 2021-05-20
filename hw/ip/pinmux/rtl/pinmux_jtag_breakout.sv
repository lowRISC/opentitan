// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module pinmux_jtag_breakout (
  input  jtag_pkg::jtag_req_t req_i,
  output jtag_pkg::jtag_rsp_t rsp_o,

  output logic tck_o,
  output logic trst_no,
  output logic tms_o,
  output logic tdi_o,
  input        tdo_i,
  input        tdo_oe_i
);

  assign tck_o        = req_i.tck;
  assign trst_no      = req_i.trst_n;
  assign tms_o        = req_i.tms;
  assign tdi_o        = req_i.tdi;
  assign rsp_o.tdo    = tdo_i;
  assign rsp_o.tdo_oe = tdo_oe_i;

endmodule : pinmux_jtag_breakout
