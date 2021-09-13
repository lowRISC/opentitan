// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: ast_dft
// *Module Description: AST DFT
//############################################################################

`include "prim_assert.sv"

module ast_dft (
  input clk_i,                              // TLUL Clock
  input rst_ni,                             // TLUL Reset
  input clk_io_osc_i,                       // IO Oscillator Clock
  input clk_io_osc_val_i,                   // IO Oscillator Clock Valid
  input rst_io_clk_ni,                      // IO Oscillator Clock Reset
  input clk_ast_ext_i,                      // External (Reference) Clock
  input lc_ctrl_pkg::lc_tx_t lc_clk_byp_req_i, // External clock mux override for OTP bootstrap
  output logic clk_src_io_o,                // IO Source Clock
  output logic clk_src_io_val_o,            // IO Source Clock Valid
  output lc_ctrl_pkg::lc_tx_t lc_clk_byp_ack_o, // Switch clocks to External clock
  // memories read-write margins
  output ast_pkg::dpm_rm_t dpram_rmf_o,     // Dual Port RAM Read-write Margin Fast
  output ast_pkg::dpm_rm_t dpram_rml_o,     // Dual Port RAM Read-write Margin sLow
  output ast_pkg::spm_rm_t spram_rm_o,      // Single Port RAM Read-write Margin
  output ast_pkg::spm_rm_t sprgf_rm_o,      // Single Port Reg-File Read-write Margin
  output ast_pkg::spm_rm_t sprom_rm_o       // Single Port ROM Read-write Margin
);


////////////////////////////////////////
// IO Source Clock Selection
////////////////////////////////////////
logic lc_clk_byp_sel, lc_clk_byp_en;

assign lc_clk_byp_sel = (lc_clk_byp_req_i == lc_ctrl_pkg::On);

logic clks_aoff, clk_osc_en_q, clk_byp_en_q;

assign clks_aoff = !(clk_osc_en_q || clk_byp_en_q);

// Clock IO Oscillator
////////////////////////////////////////
logic rst_clk_osc_n, clk_osc_sel, clk_osc_aoff, clk_osc;

assign rst_clk_osc_n = clk_io_osc_val_i;

always_ff @( posedge clk_io_osc_i, negedge rst_clk_osc_n ) begin
  if ( !rst_clk_osc_n ) begin
    clk_osc_sel  <= 1'b0;
    clk_osc_aoff <= 1'b0;
  end else begin
    clk_osc_sel  <= !lc_clk_byp_sel;
    clk_osc_aoff <= clks_aoff;
  end
end

always_ff @( posedge clk_io_osc_i, negedge rst_clk_osc_n ) begin
  if ( !rst_clk_osc_n ) begin
    clk_osc_en_q <= 1'b0;
  end else if ( !clk_osc_sel ) begin
    clk_osc_en_q <= 1'b0;
  end else if ( clk_osc_sel && clk_osc_aoff ) begin
    clk_osc_en_q <= 1'b1;
  end
end

logic clk_osc_en;
assign clk_osc_en = clk_osc_sel && (clk_osc_en_q || clk_osc_aoff);

prim_clock_gating #(
  .NoFpgaGate(1'b1)
) u_clk_osc_ckgt (
  .clk_i ( clk_io_osc_i ),
  .en_i ( clk_osc_en ),
  .test_en_i ( 1'b0 ),
  .clk_o ( clk_osc )
);

// Clock IO Bypass
////////////////////////////////////////
logic rst_clk_byp_n, clk_byp_sel, clk_byp_aoff, clk_byp;

assign rst_clk_byp_n = rst_io_clk_ni;

always_ff @( posedge clk_ast_ext_i, negedge rst_clk_byp_n ) begin
  if ( !rst_clk_byp_n ) begin
    clk_byp_sel  <= 1'b0;
    clk_byp_aoff <= 1'b0;
  end else begin
    clk_byp_sel  <= lc_clk_byp_sel;
    clk_byp_aoff <= clks_aoff;
  end
end

always_ff @( posedge clk_ast_ext_i, negedge rst_clk_byp_n ) begin
  if ( !rst_clk_byp_n ) begin
    clk_byp_en_q <= 1'b0;
  end else if ( !clk_byp_sel ) begin
    clk_byp_en_q <= 1'b0;
  end else if ( clk_byp_sel && clk_byp_aoff ) begin
    clk_byp_en_q <= 1'b1;
  end
end

logic clk_byp_en;
assign clk_byp_en = clk_byp_sel && (clk_byp_en_q || clk_byp_aoff);

prim_clock_gating #(
  .NoFpgaGate(1'b1)
) u_clk_byp_ckgt (
  .clk_i ( clk_ast_ext_i ),
  .en_i ( clk_byp_en ),
  .test_en_i ( 1'b0 ),
  .clk_o ( clk_byp )
);

// IO Clock Source
////////////////////////////////////////
assign lc_clk_byp_en = clk_byp_en;
assign clk_src_io_o  = clk_osc || clk_byp;

assign clk_src_io_val_o = clk_io_osc_val_i || lc_clk_byp_en;
assign lc_clk_byp_ack_o = lc_clk_byp_en ? lc_ctrl_pkg::On :
                                          lc_ctrl_pkg::Off;




////////////////////////////////////////
// Memories Read-write Margins
////////////////////////////////////////
assign dpram_rmf_o = 10'h000;
assign dpram_rml_o = 10'h000;
assign spram_rm_o  = 5'h00;
assign sprgf_rm_o  = 5'h00;
assign sprom_rm_o  = 5'h00;


///////////////////////
// Unused Signals
///////////////////////
logic unused_sigs;
assign unused_sigs = ^{ clk_i,       // Used in ASIC implementation
                        rst_ni       // Used in ASIC implementation
                      };

endmodule : ast_dft
