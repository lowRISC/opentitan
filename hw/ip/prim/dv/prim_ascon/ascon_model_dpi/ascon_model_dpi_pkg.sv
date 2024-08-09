// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package ascon_model_dpi_pkg;


  import "DPI-C" context function void c_dpi_ascon_round(
    input  bit[4:0][7:0][7:0] data_i,
    input  bit[7:0] round_i,
    output bit[4:0][7:0][7:0] data_o
  );
endpackage
