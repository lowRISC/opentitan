// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * Data integrity decoder for bus integrity scheme
 */

module tlul_data_integ_dec import tlul_pkg::*; (
  // TL-UL interface
  input        [DataMaxWidth+DataIntgWidth-1:0] data_intg_i,
  output logic                                  data_err_o
);

  logic [1:0] data_err;
  prim_secded_inv_39_32_dec u_data_chk (
    .data_i(data_intg_i),
    .data_o(),
    .syndrome_o(),
    .err_o(data_err)
  );

  assign data_err_o = |data_err;

endmodule : tlul_data_integ_dec
