// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for prim_packer. Intended to be used with a formal tool.
// To reduce the runtime for prim_packer, we limited the width parameter.

module prim_packer_fpv #(
  parameter int unsigned MaxInW = 64,
  parameter int unsigned MaxOutW = 64
) (
  input clk_i ,
  input rst_ni,

  input                      valid_i,
  input        [MaxInW-1:0]  data_i,
  input        [MaxInW-1:0]  mask_i,
  output                     ready_o,

  output logic               valid_o,
  output logic [MaxOutW-1:0] data_o,
  output logic [MaxOutW-1:0] mask_o,
  input                      ready_i,

  input                      flush_i,
  output logic               flush_done_o
);

  for (genvar k = 1; k <= 16; k++) begin : gen_prim_packer
    prim_packer #(.InW(k), .OutW(17-k)
    ) i_prim_packer (
      .clk_i,
      .rst_ni,
      .valid_i,
      .data_i (data_i[k-1:0]),
      .mask_i (mask_i[k-1:0]),
      .ready_o,
      .valid_o,
      .data_o (data_o[16-k:0]),
      .mask_o (mask_o[16-k:0]),
      .ready_i,
      .flush_i,
      .flush_done_o
    );
  end

  prim_packer #(.InW(MaxInW), .OutW(MaxOutW)
    ) i_prim_packer_max (
      .clk_i,
      .rst_ni,
      .valid_i,
      .data_i (data_i),
      .mask_i (mask_i),
      .ready_o,
      .valid_o,
      .data_o (data_o),
      .mask_o (mask_o),
      .ready_i,
      .flush_i,
      .flush_done_o
  );

endmodule : prim_packer_fpv
