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

  // Individually mix columns
  for (genvar i = 0; i < 4; i++) begin : gen_mix_column
    aes_mix_single_column aes_mix_column_i (
      .mode_i ( mode_i            ),
      .data_i ( data_i[4*i:4*i+3] ),
      .data_o ( data_o[4*i:4*i+3] )
    );
  end

endmodule
