// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES MixColumns

module aes_mix_columns (
  input  aes_pkg::mode_e mode_i,
  input  logic [7:0]     data_i [16],
  output logic [7:0]     data_o [16]
);

import aes_pkg::*;

// dummy only
mode_e unused_mode;
assign unused_mode = mode_i;
assign data_o      = data_i;

endmodule
