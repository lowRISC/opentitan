// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for prim_lfsr. Intended to be used with a formal tool.

module prim_lfsr_fpv #(
  parameter int unsigned   InDw     = 1,
  parameter int unsigned   OutDw    = 1,
  parameter int unsigned   GalXorMinLfsrDw  = 4,
  parameter int unsigned   GalXorMaxLfsrDw  = 64,
  parameter int unsigned   FibXnorMinLfsrDw = 3,
  parameter int unsigned   FibXnorMaxLfsrDw = 168,
  parameter int unsigned   NumDuts  = FibXnorMaxLfsrDw - FibXnorMinLfsrDw + 1 +
                                      GalXorMaxLfsrDw  - GalXorMinLfsrDw  + 1,
  // LFSRs up to this bitwidth are checked for maximum length
  parameter int unsigned   MaxLenSVAThresh = 10
) (
  input                                 clk_i,
  input                                 rst_ni,
  input        [NumDuts-1:0]            en_i,
  input        [NumDuts-1:0][InDw-1:0]  data_i,
  output logic [NumDuts-1:0][OutDw-1:0] data_o
);

  for (genvar k = GalXorMinLfsrDw; k <= GalXorMaxLfsrDw; k++) begin : gen_gal_xor_duts
    prim_lfsr #(
      .LfsrType("GAL_XOR"),
      .LfsrDw(k),
      .InDw(InDw),
      .OutDw(OutDw),
      .Seed(1),
      .Custom('0),
      // disabled for large LFSRs since this becomes prohibitive in runtime
      .MaxLenSVA(k <= MaxLenSVAThresh)
    ) i_prim_lfsr (
      .clk_i,
      .rst_ni,
      .en_i(en_i[k-GalXorMinLfsrDw]),
      .data_i(data_i[k-GalXorMinLfsrDw]),
      .data_o(data_o[k-GalXorMinLfsrDw])
    );
  end

  for (genvar k = FibXnorMinLfsrDw; k <= FibXnorMaxLfsrDw; k++) begin : gen_fib_xnor_duts
    prim_lfsr #(
      .LfsrType("FIB_XNOR"),
      .LfsrDw(k),
      .InDw(InDw),
      .OutDw(OutDw),
      .Seed(1),
      .Custom('0),
      // disabled for large LFSRs since this becomes prohibitive in runtime
      .MaxLenSVA(k <= MaxLenSVAThresh)
    ) i_prim_lfsr (
      .clk_i,
      .rst_ni,
      .en_i(en_i[k - FibXnorMinLfsrDw + GalXorMaxLfsrDw - GalXorMinLfsrDw + 1]),
      .data_i(data_i[k - FibXnorMinLfsrDw + GalXorMaxLfsrDw - GalXorMinLfsrDw + 1]),
      .data_o(data_o[k - FibXnorMinLfsrDw + GalXorMaxLfsrDw - GalXorMinLfsrDw + 1])
    );
  end

endmodule : prim_lfsr_fpv
