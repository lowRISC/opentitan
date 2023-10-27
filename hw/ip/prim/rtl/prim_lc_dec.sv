// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Decoder for life cycle control signals with additional
// input buffers.

module prim_lc_dec (
  input lc_ctrl_pkg::lc_tx_t lc_en_i,
  output logic lc_en_dec_o
);

logic [lc_ctrl_pkg::TxWidth-1:0] lc_en;
logic [lc_ctrl_pkg::TxWidth-1:0] lc_en_out;
assign lc_en = lc_en_i;

// The buffer cells have a don't touch constraint on them
// such that synthesis tools won't collapse them
for (genvar k = 0; k < lc_ctrl_pkg::TxWidth; k++) begin : gen_bits
  prim_buf u_prim_buf (
    .in_i ( lc_en[k] ),
    .out_o ( lc_en_out[k] )
  );
end

assign lc_en_dec_o = (lc_en_out == lc_ctrl_pkg::On);

endmodule : prim_lc_dec
