// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for rv_plic. Intended to use with a formal tool.

module rv_plic_fpv import rv_plic_reg_pkg::*; #(
  // test all implementations
  localparam int unsigned NumInstances = 2
) (
  input                                          clk_i,
  input                                          rst_ni,
  input  tlul_pkg::tl_h2d_t [NumInstances-1:0]   tl_i,
  output tlul_pkg::tl_d2h_t [NumInstances-1:0]   tl_o,
  input  [NumInstances-1:0][NumSrc-1:0]          intr_src_i,
  output [NumInstances-1:0][NumTarget-1:0]       irq_o,
  output [$clog2(NumSrc+1)-1:0]                  irq_id_o [NumInstances-1:0][NumTarget],
  output logic [NumInstances-1:0][NumTarget-1:0] msip_o
);

  // TODO: once the PLIC is fully parameterizable in RTL, generate
  // several instances with different NumSrc and NumTarget configs here
  // (in a similar way as this has been done in prim_lfsr_fpv)
  // for (genvar k = 0; k < NumInstances; k++) begin : geNumInstances
  rv_plic #(
    .FIND_MAX("SEQUENTIAL")
  ) i_rv_plic_sequential (
    .clk_i      ,
    .rst_ni     ,
    .tl_i       (tl_i[0]),
    .tl_o       (tl_o[0]),
    .intr_src_i (intr_src_i[0]),
    .irq_o      (irq_o[0]),
    .irq_id_o   (irq_id_o[0]),
    .msip_o     (msip_o[0])
  );

  rv_plic #(
    .FIND_MAX("MATRIX")
  ) i_rv_plic_matrix (
    .clk_i      ,
    .rst_ni     ,
    .tl_i       (tl_i[1]),
    .tl_o       (tl_o[1]),
    .intr_src_i (intr_src_i[1]),
    .irq_o      (irq_o[1]),
    .irq_id_o   (irq_id_o[1]),
    .msip_o     (msip_o[1])
  );

endmodule : rv_plic_fpv
