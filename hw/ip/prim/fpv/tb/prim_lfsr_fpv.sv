// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for prim_lfsr. Intended to be used with a formal tool.

module prim_lfsr_fpv #(
  // LFSR entropy and output bitwidths (set to 1 here as they are unused)
  parameter int unsigned EntropyDw        = 1,
  parameter int unsigned StateOutDw       = 1,
  // this specifies the range of differently
  // parameterized LFSRs to instantiate and check
  parameter int unsigned GalXorMinLfsrDw  = 4,
  parameter int unsigned GalXorMaxLfsrDw  = 64,
  parameter int unsigned FibXnorMinLfsrDw = 3,
  parameter int unsigned FibXnorMaxLfsrDw = 168,
  // LFSRs up to this bitwidth are checked for maximum length
  parameter int unsigned MaxLenSVAThresh  = 10,
  // derived params
  localparam int unsigned GalMaxGtFibMax  = GalXorMaxLfsrDw > FibXnorMaxLfsrDw,
  localparam int unsigned MaxLfsrDw       = GalXorMaxLfsrDw * GalMaxGtFibMax +
                                            FibXnorMaxLfsrDw * (1 - GalMaxGtFibMax),
  localparam int unsigned NumDuts         = FibXnorMaxLfsrDw - FibXnorMinLfsrDw + 1 +
                                            GalXorMaxLfsrDw - GalXorMinLfsrDw + 1
) (
  input                                      clk_i,
  input                                      rst_ni,
  input [NumDuts-1:0]                        load_ext_en_i,
  input [NumDuts-1:0][MaxLfsrDw-1:0]         seed_ext_i,
  input [NumDuts-1:0]                        lfsr_en_i,
  input [NumDuts-1:0][EntropyDw-1:0]         entropy_i,
  output logic [NumDuts-1:0][StateOutDw-1:0] state_o
);

  for (genvar k = GalXorMinLfsrDw; k <= GalXorMaxLfsrDw; k++) begin : gen_gal_xor_duts
    localparam int unsigned idx = k - GalXorMinLfsrDw;
    prim_lfsr #(.LfsrType("GAL_XOR"),
      .LfsrDw      ( k          ),
      .EntropyDw   ( EntropyDw  ),
      .StateOutDw  ( StateOutDw ),
      .DefaultSeed ( 1          ),
      // disabled for large LFSRs since this becomes prohibitive in runtime
      .MaxLenSVA   ( k <= MaxLenSVAThresh )
    ) i_prim_lfsr (
      .clk_i,
      .rst_ni,
      .seed_en_i ( load_ext_en_i[idx]  ),
      .seed_i    ( k'(seed_ext_i[idx]) ),
      .lfsr_en_i ( lfsr_en_i[idx]      ),
      .entropy_i ( entropy_i[idx]      ),
      .state_o   ( state_o[idx]        )
    );
  end

  for (genvar k = FibXnorMinLfsrDw; k <= FibXnorMaxLfsrDw; k++) begin : gen_fib_xnor_duts
    localparam int unsigned idx = k - FibXnorMinLfsrDw + GalXorMaxLfsrDw - GalXorMinLfsrDw + 1;
    prim_lfsr #(.LfsrType("FIB_XNOR"),
      .LfsrDw      ( k          ),
      .EntropyDw   ( EntropyDw  ),
      .StateOutDw  ( StateOutDw ),
      .DefaultSeed ( 1          ),
      // disabled for large LFSRs since this becomes prohibitive in runtime
      .MaxLenSVA   ( k <= MaxLenSVAThresh )
    ) i_prim_lfsr (
      .clk_i,
      .rst_ni,
      .seed_en_i ( load_ext_en_i[idx]  ),
      .seed_i    ( k'(seed_ext_i[idx]) ),
      .lfsr_en_i ( lfsr_en_i[idx]      ),
      .entropy_i ( entropy_i[idx]      ),
      .state_o   ( state_o[idx]        )
    );
  end

endmodule : prim_lfsr_fpv
