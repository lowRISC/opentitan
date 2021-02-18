// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: aon_clk
// *Module Description: Always ON Clock
//############################################################################
`timescale 1ns / 10ps

module aon_clk #(
`ifndef VERILATOR
// synopsys translate_off
  parameter time AON_EN_RDLY = 5us
// synopsys translate_on
`endif
) (
  input clk_src_aon_en_i,         // AON Source Clock Enable
  input clk_aon_pd_ni,            // AON Clock Power-down
  input rst_aon_clk_ni,           // AON Clock Logic reset
  input vcore_pok_h_i,            // VCORE POK @3.3V (for OSC)
  output logic clk_src_aon_o,     // AON Source Clock
  output logic clk_src_aon_val_o  // AON Source Clock Valid
);

logic clk, aon_clk_en, aon_clk_val, rst_n;

assign rst_n = rst_aon_clk_ni;

assign aon_clk_en = clk_src_aon_en_i && clk_aon_pd_ni;

// Behavioral Model

aon_osc #(
`ifndef VERILATOR
// synopsys translate_off
/*P*/ .AON_EN_RDLY ( AON_EN_RDLY )
// synopsys translate_on
`endif
) u_aon_osc (
/*I*/ .vcore_pok_h_i ( vcore_pok_h_i ),
/*I*/ .aon_en_i ( aon_clk_en ),
/*O*/ .aon_clk_o ( clk )
);


// Clock & Valid
assign clk_src_aon_o = clk;

wire rst_val_n = rst_n && clk_aon_pd_ni;

// 2-stage deassertion
always_ff @( posedge clk, negedge rst_val_n ) begin
  if ( !rst_val_n )  begin
    aon_clk_val       <= 1'b0;
    clk_src_aon_val_o <= 1'b0;
  end else begin
    aon_clk_val       <= 1'b1;
    clk_src_aon_val_o <= aon_clk_val;
  end
end


endmodule  // of aon_clk
