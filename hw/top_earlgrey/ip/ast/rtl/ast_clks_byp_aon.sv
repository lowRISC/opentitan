// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
//############################################################################
// *Name: ast_clks_byp_aon
// *Module Description: AST Clocks Bypass - AON Power Domain
//
// Contains AON clock mux and associated reset logic. Self-sufficient when
// main domain is powered down - automatically selects internal oscillator
// via rst_clk_ext_aon_n tied directly to vcmain_pok_i.
//############################################################################

`include "prim_assert.sv"

module ast_clks_byp_aon
  import ast_aon_main_pkg::*;
(
  // Power OK signals
  input  logic vcaon_pok_i,                 // VCAON POK
  input  logic vcmain_pok_i,                // VCMAIN POK (direct - safety mechanism)
  // Scan signals
  input  logic scan_mode_i,                 // Scan Mode
  input  logic scan_reset_ni,               // Scan Reset
  // Oscillator clock inputs
  input  logic clk_osc_aon_i,               // AON Oscillator Clock
  input  logic clk_osc_aon_val_i,           // AON Oscillator Clock Valid
  // Interface from main domain
  input  clks_byp_main_to_aon_t main_to_aon_i,
  // Interface to main domain
  output clks_byp_aon_to_main_t aon_to_main_o
);

////////////////////////////////////////
// Reset Generation
////////////////////////////////////////
// Key safety mechanism: rst_clk_ext_aon_n is directly tied to vcmain_pok_i
// When main powers down, this immediately disables external clock path
// in the mux, forcing internal oscillator selection regardless of control signals.

logic vcaon_pok;  // For Spyglass waiver
assign vcaon_pok = vcaon_pok_i;

logic rst_clk_osc_n, aon_rst_clk_ext_n;
assign rst_clk_osc_n = scan_mode_i ? scan_reset_ni : vcaon_pok;
assign aon_rst_clk_ext_n = scan_mode_i ? scan_reset_ni : vcmain_pok_i;

////////////////////////////////////////
// Reset Buffers
////////////////////////////////////////
logic rst_clk_osc_aon_n, rst_clk_ext_aon_n;

prim_buf u_rst_clk_osc_aon (
  .in_i ( rst_clk_osc_n ),
  .out_o ( rst_clk_osc_aon_n )
);

prim_buf u_rst_clk_ext_aon (
  .in_i ( aon_rst_clk_ext_n ),
  .out_o ( rst_clk_ext_aon_n )
);

////////////////////////////////////////
// AON Clock Bypass Mux
////////////////////////////////////////
logic clk_src_aon, clk_src_aon_val;
logic aon_clk_osc_en, aon_clk_byp_en;

gfr_clk_mux2 u_clk_src_aon_sel (
  .clk_osc_i ( clk_osc_aon_i ),
  .clk_osc_val_i ( clk_osc_aon_val_i ),
  .rst_clk_osc_ni ( rst_clk_osc_aon_n ),
  .clk_ext_i ( main_to_aon_i.clk_ext_aon ),
  .clk_ext_val_i ( 1'b1 ),  // Always ON clock
  .rst_clk_ext_ni ( rst_clk_ext_aon_n ),
  .ext_sel_i ( main_to_aon_i.aon_select_ext ),
  .clk_osc_en_o ( aon_clk_osc_en ),
  .clk_ext_en_o ( aon_clk_byp_en ),
  .clk_val_o ( clk_src_aon_val ),
  .clk_o ( clk_src_aon )
);

////////////////////////////////////////
// Output Assignments
////////////////////////////////////////
assign aon_to_main_o.clk_src_aon_o = clk_src_aon;
assign aon_to_main_o.clk_src_aon_val_o = clk_src_aon_val;
assign aon_to_main_o.aon_clk_byp_en = aon_clk_byp_en;

// Unused signal
logic unused_aon_clk_osc_en;
assign unused_aon_clk_osc_en = aon_clk_osc_en;

endmodule : ast_clks_byp_aon
