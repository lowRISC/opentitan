// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: ast_clks_byp
// *Module Description: AST Clocks Bypass
//############################################################################

`include "prim_assert.sv"

module ast_clks_byp (
  input vcaon_pok_i,                        // VCAON POK
  input vcaon_pok_por_i,                    // VCAON POK POR
  input deep_sleep_i,                       // Deep Sleep (main regulator & switch are off)
  input clk_src_sys_en_i,                   // SYS Source Clock Enable
  input clk_osc_sys_i,                      // SYS Oscillator Clock
  input clk_osc_sys_val_i,                  // SYS Oscillator Clock Valid
  input clk_src_io_en_i,                    // IO Source Clock Enable
  input clk_osc_io_i,                       // IO Oscillator Clock
  input clk_osc_io_val_i,                   // IO Oscillator Clock Valid
  input clk_osc_aon_i,                      // AON Oscillator Clock
  input clk_osc_aon_val_i,                  // AON Oscillator Clock Valid
`ifdef AST_BYPASS_CLK
  input clk_ext_sys_i,
  input clk_ext_io_i,
  input clk_ext_aon_i,
`endif // of AST_BYPASS_CLK
  input prim_mubi_pkg::mubi4_t io_clk_byp_req_i,    // External IO clock mux for OTP bootstrap
  input prim_mubi_pkg::mubi4_t all_clk_byp_req_i,   // External all clock mux override
  output prim_mubi_pkg::mubi4_t io_clk_byp_ack_o,   // Switch IO clock to External clock
  output prim_mubi_pkg::mubi4_t all_clk_byp_ack_o,  // Switch all clocks to External clock
  output logic clk_src_sys_o,               // SYS Source Clock
  output logic clk_src_sys_val_o,           // SYS Source Clock Valid
  output logic clk_src_io_o,                // IO Source Clock
  output logic clk_src_io_val_o,            // IO Source Clock Valid
  output logic clk_src_aon_o,               // AON Source Clock
  output logic clk_src_aon_val_o            // AON Source Clock Valid
);

logic scan_mode_i, scan_reset_ni;

assign scan_mode_i   = 1'b0;
assign scan_reset_ni = 1'b1;

////////////////////////////////////////
// Local AON clock buffer
////////////////////////////////////////
logic clk_aon, rst_aon_n;

prim_clock_buf #(
  .NoFpgaBuf ( 1'b1 )
) u_clk_aon_buf (
  .clk_i ( clk_src_aon_o ),
  .clk_o ( clk_aon )
);

logic vcaon_pok;  // For Spyglass waiver!!!

assign vcaon_pok = vcaon_pok_i;
assign rst_aon_n = scan_mode_i ? scan_reset_ni : vcaon_pok;


////////////////////////////////////////
// External Clocks Generation
////////////////////////////////////////
// Enable External Clock for SW Bypass
logic sw_all_clk_byp, sw_io_clk_byp;



logic rst_sw_ckbpe_n, clk_ast_ext_scn;

assign rst_sw_ckbpe_n = scan_reset_ni;
`ifndef AST_BYPASS_CLK
assign clk_ast_ext_scn = clk_osc_sys_i;
`else // of AST_BYPASS_CLK
assign clk_ast_ext_scn = scan_mode_i ? clk_osc_sys_i : clk_ext_sys_i;
`endif // of AST_BYPASS_CLK

logic rst_aon_exda_n;
assign rst_aon_exda_n = scan_reset_ni;


////////////////////////////////////////
// Deep-Sleep/Enables Gates
////////////////////////////////////////

// Deep-Sleep Sync to External clock
////////////////////////////////////////
logic deep_sleep, deep_sleep_n;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_deep_sleep_sync (
  .clk_i ( clk_ext ),
  .rst_ni ( rst_aon_exda_n ),
  .d_i ( deep_sleep_i ),
  .q_o ( deep_sleep )
);

assign deep_sleep_n = !deep_sleep;

// SYS External Clock Enable
////////////////////////////////////////
logic clk_ext_sys, clk_ext_sys_en, clk_ext_sys_val;
logic clk_src_sys_en;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_no_scan_clk_src_sys_en_sync (
  .clk_i ( clk_ext ),
  .rst_ni ( rst_aon_exda_n ),
  .d_i ( clk_src_sys_en_i ),
  .q_o ( clk_src_sys_en )
);

assign clk_ext_sys_en  = deep_sleep_n && clk_src_sys_en;
assign clk_ext_sys_val = clk_ext_sys_en;

prim_clock_gating #(
  .NoFpgaGate ( 1'b1)
) u_clk_ext_sys_ckgt (
  .clk_i ( clk_ext ),
  .en_i ( clk_ext_sys_en ),
  .test_en_i ( scan_mode_i ),
  .clk_o ( clk_ext_sys )
);

// IO External Clock Enable
////////////////////////////////////////
logic clk_ext_io, clk_ext_io_en, clk_ext_io_val;
logic clk_src_io_en;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_no_scan_clk_src_io_en_sync (
  .clk_i ( clk_ext ),
  .rst_ni ( rst_aon_exda_n ),
  .d_i ( clk_src_io_en_i ),
  .q_o ( clk_src_io_en )
);

assign clk_ext_io_en  = deep_sleep_n && clk_src_io_en;
assign clk_ext_io_val = clk_ext_io_en;

prim_clock_gating #(
  .NoFpgaGate ( 1'b1)
) u_clk_ext_io_ckgt (
`ifndef AST_BYPASS_CLK
  .clk_i ( clk_ext ),
`else // of AST_BYPASS_CLK
  .clk_i ( clk_ext_io_i ),
`endif // of AST_BYPASS_CLK
  .en_i ( clk_ext_io_en ),
  .test_en_i ( scan_mode_i ),
  .clk_o ( clk_ext_io )
);


////////////////////////////////////////
// SW Bypass select logic
////////////////////////////////////////
// Sync to local AON clock
prim_mubi_pkg::mubi4_t ot_io_clk_byp_req, ot_all_clk_byp_req;

prim_mubi4_sync #(
  .StabilityCheck ( 1 ),
  .ResetValue ( prim_mubi_pkg::MuBi4False )
) u_io_clk_byp_req (
  .clk_i ( clk_aon ),
  .rst_ni ( rst_aon_n ),
  .mubi_i ( io_clk_byp_req_i ),
  .mubi_o ( {ot_io_clk_byp_req} )
);

prim_mubi4_sync #(
  .StabilityCheck ( 1 ),
  .ResetValue ( prim_mubi_pkg::MuBi4False )
) u_all_clk_byp_req (
  .clk_i ( clk_aon ),
  .rst_ni ( rst_aon_n ),
  .mubi_i ( all_clk_byp_req_i ),
  .mubi_o ( {ot_all_clk_byp_req} )
);

// Decode logic
logic ot_all_clk_byp, ot_sys_clk_byp, ot_io_clk_byp, ot_aon_clk_byp;

prim_mubi4_dec u_all_byp_sel ( .mubi_i ( ot_all_clk_byp_req ), .mubi_dec_o ( ot_all_clk_byp ) );
prim_mubi4_dec u_sys_byp_sel ( .mubi_i ( ot_all_clk_byp_req ), .mubi_dec_o ( ot_sys_clk_byp ) );
prim_mubi4_dec u_io_byp_sel  ( .mubi_i ( ot_io_clk_byp_req ),  .mubi_dec_o ( ot_io_clk_byp ) );
prim_mubi4_dec u_aon_byp_sel ( .mubi_i ( ot_all_clk_byp_req ), .mubi_dec_o ( ot_aon_clk_byp ) );

// De-Glitch selects (decode "noise")
logic sw_sys_clk_byp, sw_aon_clk_byp;

prim_flop #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_sw_all_clk_byp_dgl (
  .clk_i ( clk_aon ),
  .rst_ni ( rst_aon_n ),
  .d_i ( ot_all_clk_byp ),
  .q_o ( sw_all_clk_byp )
);

prim_flop #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_sw_sys_clk_byp_dgl (
  .clk_i ( clk_aon ),
  .rst_ni ( rst_aon_n ),
  .d_i ( ot_sys_clk_byp ),
  .q_o ( sw_sys_clk_byp )
);

prim_flop #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_sw_io_clk_byp_dgl (
  .clk_i ( clk_aon ),
  .rst_ni ( rst_aon_n ),
  .d_i ( ot_io_clk_byp ),
  .q_o ( sw_io_clk_byp )
);

prim_flop #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_sw_aon_clk_byp_dgl (
  .clk_i ( clk_aon ),
  .rst_ni ( rst_aon_n ),
  .d_i ( ot_aon_clk_byp ),
  .q_o ( sw_aon_clk_byp )
);

logic sys_clk_byp;

assign sys_clk_byp = sw_sys_clk_byp;

logic sel_io_clk_byp, io_clk_byp;

assign sel_io_clk_byp = sw_io_clk_byp || sw_all_clk_byp;

// De-Glitch IO Clock Bypass Select
////////////////////////////////////////
prim_flop #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_io_clk_byp_dgl (
  .clk_i ( clk_aon ),
  .rst_ni ( rst_aon_n ),
  .d_i ( sel_io_clk_byp ),
  .q_o ( io_clk_byp )
);


logic aon_clk_byp;
assign aon_clk_byp = sw_aon_clk_byp;

// Block changes during scan mode
////////////////////////////////////////
logic sys_clk_byp_sel, io_clk_byp_sel, aon_clk_byp_sel;

`ifndef AST_BYPASS_CLK
always_latch begin
  if ( !scan_mode_i ) begin
    sys_clk_byp_sel = sys_clk_byp;
    io_clk_byp_sel  = io_clk_byp;
    aon_clk_byp_sel = aon_clk_byp;
  end
end
`else // of AST_BYPASS_CLK
assign sys_clk_byp_sel = sys_clk_byp;
assign io_clk_byp_sel  = io_clk_byp;
assign aon_clk_byp_sel = aon_clk_byp;
`endif // of AST_BYPASS_CLK


////////////////////////////////////////
// Clocks Bypass Muxes
////////////////////////////////////////
logic sys_clk_osc_en, io_clk_osc_en, aon_clk_osc_en;
logic sys_clk_byp_en, io_clk_byp_en, aon_clk_byp_en;
logic rst_clk_osc_n, rst_clk_ext_n, aon_rst_clk_ext_n;

assign rst_clk_osc_n = vcaon_pok;
assign rst_clk_ext_n = vcaon_pok_por_i;
assign aon_rst_clk_ext_n = vcaon_pok;

// DV Hooks for IO clocks
logic io_clk_byp_select, io_clk_byp_sel_buf, io_clk_osc_en_buf, io_clk_byp_en_buf;

assign io_clk_byp_select = io_clk_byp_sel;

prim_buf u_io_clk_byp_sel (
  .in_i ( io_clk_byp_select ),
  .out_o ( io_clk_byp_sel_buf )
);

prim_buf u_io_clk_osc_en (
  .in_i ( io_clk_osc_en ),
  .out_o ( io_clk_osc_en_buf )
);

prim_buf u_io_clk_byp_en (
  .in_i ( io_clk_byp_en ),
  .out_o ( io_clk_byp_en_buf )
);

logic rst_clk_osc_sys_n, rst_clk_ext_sys_n, rst_clk_osc_io_n, rst_clk_ext_io_n;
logic rst_clk_osc_aon_n, rst_clk_ext_aon_n;

prim_buf u_rst_clk_osc_sys (
  .in_i ( rst_clk_osc_n ),
  .out_o ( rst_clk_osc_sys_n )
);

prim_buf u_rst_clk_ext_sys (
  .in_i ( rst_clk_ext_n ),
  .out_o ( rst_clk_ext_sys_n )
);

prim_buf u_rst_clk_osc_io (
  .in_i ( rst_clk_osc_n ),
  .out_o ( rst_clk_osc_io_n )
);

prim_buf u_rst_clk_ext_io (
  .in_i ( rst_clk_ext_n ),
  .out_o ( rst_clk_ext_io_n )
);

prim_buf u_rst_clk_osc_aon (
  .in_i ( rst_clk_osc_n ),
  .out_o ( rst_clk_osc_aon_n )
);

prim_buf u_rst_clk_ext_aon (
  .in_i ( aon_rst_clk_ext_n ),
  .out_o ( rst_clk_ext_aon_n )
);

// rst_aon_n deassert to io clock
////////////////////////////////////////
logic rst_aon_n_ioda, rst_aon_ioda_n;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_rst_aon_n_ioda_sync (
  .clk_i ( clk_src_io_o ),
  .rst_ni ( rst_aon_n ),
  .d_i ( 1'b1 ),
  .q_o ( rst_aon_n_ioda )
);

assign rst_aon_ioda_n = scan_mode_i ? scan_reset_ni : rst_aon_n_ioda;

// SYS Clock Bypass Mux
////////////////////////////////////////
gfr_clk_mux2 u_clk_src_sys_sel (
  .clk_osc_i ( clk_osc_sys_i ),
  .clk_osc_val_i ( clk_osc_sys_val_i ),
  .rst_clk_osc_ni ( rst_clk_osc_sys_n ),
  .clk_ext_i ( clk_ext_sys ),
  .clk_ext_val_i ( clk_ext_sys_val ),
  .rst_clk_ext_ni ( rst_clk_ext_sys_n ),
  .ext_sel_i ( sys_clk_byp_sel ),
  .clk_osc_en_o ( sys_clk_osc_en ),
  .clk_ext_en_o ( sys_clk_byp_en ),
  .clk_val_o ( clk_src_sys_val_o ),
  .clk_o ( clk_src_sys_o )
);

// IO Clock Bypass Mux
////////////////////////////////////////
logic clk_src_io, clk_src_io_val;

gfr_clk_mux2 u_clk_src_io_sel (
  .clk_osc_i ( clk_osc_io_i ),
  .clk_osc_val_i ( clk_osc_io_val_i ),
  .rst_clk_osc_ni ( rst_clk_osc_io_n ),
  .clk_ext_i ( clk_ext_io ),
  .clk_ext_val_i ( clk_ext_io_val ),
  .rst_clk_ext_ni ( rst_clk_ext_io_n ),
  .ext_sel_i ( io_clk_byp_sel ),
  .clk_osc_en_o ( io_clk_osc_en ),
  .clk_ext_en_o ( io_clk_byp_en ),
  .clk_val_o ( clk_src_io_val ),
  .clk_o ( clk_src_io )
);

assign clk_src_io_val_o = clk_src_io_val;
assign clk_src_io_o = clk_src_io;

// AON Clock Bypass Mux
////////////////////////////////////////
gfr_clk_mux2 u_clk_src_aon_sel (
  .clk_osc_i ( clk_osc_aon_i ),
  .clk_osc_val_i ( clk_osc_aon_val_i ),
  .rst_clk_osc_ni ( rst_clk_osc_aon_n ),
  .clk_ext_i ( clk_ext_aon ),
  .clk_ext_val_i ( clk_ext_aon_val ),
  .rst_clk_ext_ni ( rst_clk_ext_aon_n ),
  .ext_sel_i ( aon_clk_byp_sel ),
  .clk_osc_en_o ( aon_clk_osc_en ),
  .clk_ext_en_o ( aon_clk_byp_en ),
  .clk_val_o ( clk_src_aon_val_o ),
  .clk_o ( clk_src_aon_o )
);

// All Clocks Bypass Acknowledge
////////////////////////////////////////
logic all_clks_byp_en_src, all_clks_byp_en;

always_ff @( posedge clk_aon, negedge rst_aon_n ) begin
  if ( !rst_aon_n ) begin
    all_clks_byp_en_src <= 1'b0;
  end else begin
    all_clks_byp_en_src <= sw_all_clk_byp && sys_clk_byp_en && io_clk_byp_en &&
                             aon_clk_byp_en;
  end
end

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_all_clks_byp_en_sync (
  .clk_i ( clk_src_io_o ),
  .rst_ni ( rst_aon_ioda_n ),
  .d_i ( all_clks_byp_en_src ),
  .q_o ( all_clks_byp_en )
);

prim_mubi4_sender #(
  .ResetValue ( prim_mubi_pkg::MuBi4False )
) u_all_clk_byp_ack (
  .clk_i ( clk_src_io_o ),
  .rst_ni ( rst_aon_ioda_n ),
  .mubi_i ( prim_mubi_pkg::mubi4_bool_to_mubi(all_clks_byp_en) ),
  .mubi_o ( {all_clk_byp_ack_o} )
);

// IO Clock Bypass Acknowledge
////////////////////////////////////////
logic only_io_clk_byp_en_src, only_io_clk_byp_en;

always_ff @( posedge clk_aon, negedge rst_aon_n ) begin
  if ( !rst_aon_n ) begin
    only_io_clk_byp_en_src <= 1'b0;
  end else begin
    only_io_clk_byp_en_src <= sw_io_clk_byp && io_clk_byp_en;
  end
end

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_only_io_clk_byp_en_sync (
  .clk_i ( clk_src_io_o ),
  .rst_ni ( rst_aon_ioda_n ),
  .d_i ( only_io_clk_byp_en_src ),
  .q_o ( only_io_clk_byp_en )
);

prim_mubi4_sender #(
  .ResetValue ( prim_mubi_pkg::MuBi4False )
) u_io_clk_byp_ack (
  .clk_i ( clk_src_io_o ),
  .rst_ni ( rst_aon_ioda_n ),
  .mubi_i ( prim_mubi_pkg::mubi4_bool_to_mubi(only_io_clk_byp_en) ),
  .mubi_o ( {io_clk_byp_ack_o} )
);

/////////////////////
// Unused Signals  //
/////////////////////
logic unused_sigs;

assign unused_sigs = ^{ io_clk_byp_sel_buf,
                        io_clk_byp_en_buf,
                        io_clk_osc_en_buf,
                        sys_clk_osc_en,
                        io_clk_osc_en,
                        aon_clk_osc_en
                      };

endmodule : ast_clks_byp
