// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package ascon_model_dpi_pkg;

  // FIXME: 5x2x32 vs 5x6x8

  import "DPI-C" context function void c_dpi_ascon_round(
    input  bit[4:0][7:0][7:0] data_i,
    input  bit[7:0] round_i,
    output bit[4:0][7:0][7:0] data_o
  );
endpackage
