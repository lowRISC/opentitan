// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: sys_clk
// *Module Description: System Clock
//############################################################################
`timescale 1ns / 10ps

module sys_clk
#(
`ifndef VERILATOR
// synopsys translate_off
  parameter time SYS_EN_RDLY = 5us
// synopsys translate_on
`endif
) (
  input clk_src_sys_en_i,           // System Source Clock Enable
  input clk_src_sys_jen_i,          // System Source Clock Jitter Enable
  input clk_sys_pd_ni,              // System Clock Power-down
  input rst_sys_clk_ni,             // System Clock Logic reset
  input vcore_pok_h_i,              // VCORE POK @3.3V (for OSC)
  output logic clk_src_sys_o,       // System Source Clock
  output logic clk_src_sys_val_o    // System Source Clock Valid
);

logic clk, sys_clk_en, sys_clk_val, rst_n;

assign rst_n = rst_sys_clk_ni;

assign sys_clk_en = clk_src_sys_en_i && clk_sys_pd_ni;

// Behavioral Model

// Clock Oscilator
sys_osc #(
`ifndef VERILATOR
// synopsys translate_off
/*P*/ .SYS_EN_RDLY ( SYS_EN_RDLY )
// synopsys translate_on
`endif
) u_sys_osc (
/*I*/ .vcore_pok_h_i ( vcore_pok_h_i ),
/*I*/ .sys_en_i ( sys_clk_en ),
/*I*/ .sys_jen_i ( clk_src_sys_jen_i ),
/*O*/ .sys_clk_o ( clk )
);


// Clock & Valid
assign clk_src_sys_o = clk;

wire rst_val_n = rst_n && sys_clk_en;

// 2-stage deassertion
always_ff @( posedge clk, negedge rst_val_n ) begin
  if ( !rst_val_n ) begin
    sys_clk_val       <= 1'b0;
    clk_src_sys_val_o <= 1'b0;
  end else begin
    sys_clk_val       <= 1'b1;
    clk_src_sys_val_o <= sys_clk_val;
  end
end


endmodule  // of sys_clk
