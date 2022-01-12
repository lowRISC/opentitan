// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * Data integrity encoder for bus integrity scheme
 */

module tlul_data_integ_enc import tlul_pkg::*; (
  // TL-UL interface
  input        [DataMaxWidth-1:0]               data_i,
  output logic [DataMaxWidth+DataIntgWidth-1:0] data_intg_o
);

  prim_secded_inv_39_32_enc u_data_gen (
    .data_i,
    .data_o(data_intg_o)
  );

endmodule : tlul_data_integ_enc
