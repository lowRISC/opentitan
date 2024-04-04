// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Convert i2c's o/oe signaling to an inout port for easier integration
module i2c_port_conv (
  input scl_oe_i,
  input sda_oe_i,
  output logic scl_o,
  output logic sda_o,
  inout wire scl_io,
  inout wire sda_io
);

  assign scl_o = scl_io;
  assign sda_o = sda_io;
  assign scl_io = scl_oe_i ? 1'b0 : 1'bz;
  assign sda_io = sda_oe_i ? 1'b0 : 1'bz;

endmodule // i2c_port_conv
