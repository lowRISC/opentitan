// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
//
// *Name: sys_clk
// *Module Description: System Clock
//
//############################################################################
`timescale 1ns / 1ps

module sys_clk #(
    // synopsys translate_off
    parameter time SYS_EN_RDLY = 10us,
    parameter time SYS_EN_FDLY = 100ns,
    parameter time SYS_JEN_RDLY = 80ns,
    parameter time SYS_JEN_FDLY = 80ns
// synopsys translate_on
) (
    input        clk_src_sys_en_i,  // System Source Clock Enable
    input        clk_src_sys_jen_i,  // System Source Clock Jitter Enable
    input        rst_ni,  // SYS Reset
    output logic clk_src_sys_o,  // System Source Clock
    output logic clk_src_sys_val_o  // System Source Clock Valid
);

  logic clk, sys_en, clk_en;

  // Behavioral Model

  // Clock Oscilator
  sys_osc #(
      // synopsys translate_off
      /*P*/.SYS_EN_RDLY(SYS_EN_RDLY),
      /*P*/.SYS_EN_FDLY(SYS_EN_FDLY),
      /*P*/.SYS_JEN_RDLY(SYS_JEN_RDLY),
      /*P*/.SYS_JEN_FDLY(SYS_JEN_FDLY)
  // synopsys translate_on
  ) i_sys_osc (
      /*I*/.sys_en_i    (clk_src_sys_en_i),
      /*I*/.sys_jen_i   (clk_src_sys_jen_i),
      /*O*/.sys_clk_o   (clk),
      /*O*/.sys_clk_en_o(sys_en)
  );

  always_ff @(posedge clk, negedge rst_ni) begin
    if (!rst_ni) clk_en <= 1'b0;
    else clk_en <= sys_en;
  end

  // Clock & Valid
  assign clk_src_sys_o = clk_en ? ~clk : 1'b0;
  assign clk_src_sys_val_o = clk_en;


endmodule  // of sys_clk
