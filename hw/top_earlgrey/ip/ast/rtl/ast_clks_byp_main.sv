// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
//############################################################################
// *Name: ast_clks_byp_main
// *Module Description: AST Clocks Bypass - Main Power Domain
//
// Contains external clock generation, SW bypass control logic, and
// SYS/IO/USB clock bypass muxes. Communicates with ast_clks_byp_aon
// for AON clock bypass coordination.
//############################################################################

`include "prim_assert.sv"

module ast_clks_byp_main
  import ast_aon_main_pkg::*;
(
  input  logic vcmain_pok_i,                       // VCMAIN POK
  input  logic vcmain_pok_por_i,                   // VCMAIN POK POR
  input  logic deep_sleep_i,                       // Deep Sleep (main regulator & switch are off)
  input  logic scan_mode_i,                        // Scan Mode
  input  logic scan_reset_ni,                      // Scan Reset
  input  logic clk_ast_tlul_i,                     // TLUL Clock
  input  logic dft_clks_byp_i,                     // DFT Clocks bypass for Tester (Patterns)
  input  logic dft_ext_is_96m_i,                   // DFT External clock is 96MHz (else 48MHz)
  input  logic clk_src_io_pre_occ_i,               // pre occ output for force scan_rst feature
  input  logic clk_src_sys_en_i,                   // SYS Source Clock Enable
  input  logic clk_osc_sys_i,                      // SYS Oscillator Clock
  input  logic clk_osc_sys_val_i,                  // SYS Oscillator Clock Valid
  input  logic clk_src_io_en_i,                    // IO Source Clock Enable
  input  logic clk_osc_io_i,                       // IO Oscillator Clock
  input  logic clk_osc_io_val_i,                   // IO Oscillator Clock Valid
  input  logic clk_src_usb_en_i,                   // USB Source Clock Enable
  input  logic clk_osc_usb_i,                      // USB Oscillator Clock
  input  logic clk_osc_usb_val_i,                  // USB Oscillator Clock Valid
  input  logic clk_ast_ext_i,                      // External Clock
`ifdef AST_BYPASS_CLK
  input clk_ext_sys_i,
  input clk_ext_io_i,
  input clk_ext_usb_i,
  input clk_ext_aon_i,
`endif // of AST_BYPASS_CLK
  input  prim_mubi_pkg::mubi4_t io_clk_byp_req_i,  // External IO clock mux for OTP bootstrap
  input  prim_mubi_pkg::mubi4_t all_clk_byp_req_i, // External all clock mux override
  input  prim_mubi_pkg::mubi4_t ext_freq_is_96m_i, // External Clock Frequency is 96MHz (else 48MHz)
  // Interface from AON domain
  input  clks_byp_aon_to_main_t aon_to_main_i,
  // Interface to AON domain
  output clks_byp_main_to_aon_t main_to_aon_o,
  // Outputs
  output prim_mubi_pkg::mubi4_t io_clk_byp_ack_o,  // Switch IO clock to External clock
  output prim_mubi_pkg::mubi4_t all_clk_byp_ack_o, // Switch all clocks to External clock
  output logic force_scan_reset_o,                 // Force Scan Reset on Scan mode RE.
  output logic clk_src_sys_o,                      // SYS Source Clock
  output logic clk_src_sys_val_o,                  // SYS Source Clock Valid
  output logic clk_src_io_o,                       // IO Source Clock
  output logic clk_src_io_val_o,                   // IO Source Clock Valid
  output prim_mubi_pkg::mubi4_t clk_src_io_48m_o,  // IO Source Clock is 48Mhz
  output logic clk_src_usb_o,                      // USB Source Clock
  output logic clk_src_usb_val_o                   // USB Source Clock Valid
);

////////////////////////////////////////
// Local AON clock buffer
////////////////////////////////////////
logic clk_aon, rst_main_in_n, rst_main_da_n, rst_main_n;

prim_clock_buf #(
  .NoFpgaBuf ( 1'b1 )
) u_clk_aon_buf (
  .clk_i ( aon_to_main_i.clk_src_aon_o ),
  .clk_o ( clk_aon )
);

assign rst_main_in_n = scan_mode_i ? scan_reset_ni : vcmain_pok_i;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_rst_main_da (
  .clk_i ( clk_aon ),
  .rst_ni ( rst_main_in_n ),
  .d_i ( 1'b1 ),
  .q_o ( rst_main_da_n )
);

assign rst_main_n = scan_mode_i ? scan_reset_ni : rst_main_da_n;

logic dft_clks_byp;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_dft_clks_byp_sync (
  .clk_i ( clk_aon ),
  .rst_ni ( rst_main_n ),
  .d_i ( dft_clks_byp_i ),
  .q_o ( dft_clks_byp )
);

logic dft_ext_is_96m;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b1 )
) u_dft_ext_is_96m_sync (
  .clk_i ( clk_aon ),
  .rst_ni ( rst_main_n ),
  .d_i ( dft_ext_is_96m_i ),
  .q_o ( dft_ext_is_96m )
);


////////////////////////////////////////
// External Clocks Generation
////////////////////////////////////////
// Enable External Clock for SW Bypass
logic rst_sw_clk_byp_en, sw_all_clk_byp, sw_io_clk_byp;

always_ff @( posedge clk_aon, negedge rst_main_n ) begin
  if ( !rst_main_n ) begin
    rst_sw_clk_byp_en <= 1'b0;
  end else if ( sw_all_clk_byp || sw_io_clk_byp || dft_clks_byp ) begin
    rst_sw_clk_byp_en <= 1'b1;
  end
end

logic rst_sw_ckbpe_n, clk_ast_ext_scn, sw_ckbpe_sync_n, rst_sw_ckbpe_syn_n, sw_clk_byp_en;

assign rst_sw_ckbpe_n = scan_mode_i ? scan_reset_ni : rst_sw_clk_byp_en;
`ifdef AST_BYPASS_CLK
assign clk_ast_ext_scn = scan_mode_i ? clk_osc_sys_i : clk_ext_sys_i;
`else // of AST_BYPASS_CLK
assign clk_ast_ext_scn = scan_mode_i ? clk_osc_sys_i : clk_ast_ext_i;
`endif // of AST_BYPASS_CLK

// De-Assert Sync
prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_no_scan_rst_sw_ckbpe_dasrt (
  .clk_i ( clk_ast_ext_scn ),
  .rst_ni ( rst_sw_ckbpe_n ),
  .d_i ( 1'b1 ),
  .q_o ( sw_ckbpe_sync_n )
);

assign rst_sw_ckbpe_syn_n = scan_mode_i ? scan_reset_ni : sw_ckbpe_sync_n;

// De-assert with external clock input
always_ff @( negedge clk_ast_ext_scn, negedge rst_sw_ckbpe_syn_n ) begin
  if ( !rst_sw_ckbpe_syn_n ) begin
    sw_clk_byp_en <= 1'b0;
  end else begin
    sw_clk_byp_en <= 1'b1;
  end
end

logic clk_ext_en, clk_ext_scn;

assign clk_ext_en = sw_clk_byp_en;
`ifdef AST_BYPASS_CLK
logic clk_ast_ext;

prim_clock_gating #(
  .NoFpgaGate(1'b1)
) u_clk_ast_ext_gating (
  .clk_i( clk_ext_sys_i ),
  .en_i( clk_ext_en ),
  .test_en_i( 1'b0 ),
  .clk_o( clk_ast_ext )
);

assign clk_ext_scn = scan_mode_i ? clk_osc_sys_i : clk_ast_ext;
`else
//we can't use prim_clock_gating here for the following reason:
//prim_clock_gating default behavior at wakeup: clk_i=1'bx, en_i=don't care --> clk_o=1'bx
//we want to mask that 1'bx as some tests doesn't use clk_ast_ext_i
assign clk_ext_scn = scan_mode_i ? clk_osc_sys_i : (clk_ast_ext_i && clk_ext_en);
`endif

// Local EXT clock buffer
////////////////////////////////////////
logic clk_ext;

prim_clock_buf #(
  .NoFpgaBuf ( 1'b1 )
) u_clk_ext_buf (
  .clk_i ( clk_ext_scn ),
  .clk_o ( clk_ext )
);

logic rst_main_da_n_exda, rst_aon_exda_n;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_rst_main_da_n_exda_sync (
  .clk_i ( clk_ext ),
  .rst_ni ( rst_main_n ),
  .d_i ( 1'b1 ),
  .q_o ( rst_main_da_n_exda )
);

assign rst_aon_exda_n = scan_mode_i ? scan_reset_ni : rst_main_da_n_exda;

// External USB & AON clocks genaration
////////////////////////////////////////
`ifdef AST_BYPASS_CLK
logic clk_src_ext_usb, ext_freq_is_96m;
assign clk_src_ext_usb = clk_ext_usb_i;
`else // of AST_BYPASS_CLK
logic clk_src_ext_usb, ext_freq_is_96m, ext_freq_is_96m_sync;

prim_flop_2sync #(
  .Width ( 1 ),
  // Assume external clock is 96Hhz on reset
  .ResetValue ( 1'b1 )
) u_no_scan_ext_freq_is_96m_sync (
  .clk_i ( clk_ext ),
  .rst_ni ( rst_aon_exda_n ),
  .d_i ( ext_freq_is_96m ),
  .q_o ( ext_freq_is_96m_sync )
);

prim_clock_div #(
  .Divisor( 2 )
) u_no_scan_clk_ext_d1ord2 (
  .clk_i ( clk_ext ),
  .rst_ni ( rst_aon_exda_n ),
  .step_down_req_i( !ext_freq_is_96m_sync ),
  .step_down_ack_o ( ),
  .test_en_i ( scan_mode_i ),
  .clk_o ( clk_src_ext_usb )
);
`endif // of AST_BYPASS_CLK

logic clk_ext_aon;

`ifdef AST_BYPASS_CLK
assign clk_ext_aon = clk_ext_aon_i;
`else // of AST_BYPASS_CLK
prim_clock_div #(
  .Divisor( 240 )
) u_no_scan_clk_usb_div240_div (
  .clk_i ( clk_src_ext_usb ),
  .rst_ni ( rst_aon_exda_n ),
  .step_down_req_i( 1'b0 ),
  .step_down_ack_o ( ),
  .test_en_i ( scan_mode_i ),
  .clk_o ( clk_ext_aon )
);
`endif // of AST_BYPASS_CLK

////////////////////////////////////////
// Deep-Sleep/Enables Gators
////////////////////////////////////////

// Deep-Sleep Sync to External clcok
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
`ifdef AST_BYPASS_CLK
  .clk_i ( clk_ext_io_i ),
`else // of AST_BYPASS_CLK
  .clk_i ( clk_ext ),
`endif // of AST_BYPASS_CLK
  .en_i ( clk_ext_io_en ),
  .test_en_i ( scan_mode_i ),
  .clk_o ( clk_ext_io )
);

// USB External Clock Enable
////////////////////////////////////////
logic clk_ext_usb, clk_ext_usb_en, clk_ext_usb_val;
logic clk_src_usb_en;
logic clk_src_ext_usb_n;

assign clk_src_ext_usb_n = ~clk_src_ext_usb;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_no_scan_clk_src_usb_en_sync (
  .clk_i ( clk_src_ext_usb_n ),
  .rst_ni ( rst_aon_exda_n ),
  .d_i ( clk_src_usb_en_i ),
  .q_o ( clk_src_usb_en )
);

assign clk_ext_usb_en  = deep_sleep_n && clk_src_usb_en;
assign clk_ext_usb_val = clk_ext_usb_en;

prim_clock_gating #(
  .NoFpgaGate ( 1'b1)
) u_clk_ext_usb_ckgt (
  .clk_i ( clk_src_ext_usb ),
  .en_i ( clk_ext_usb_en ),
  .test_en_i ( scan_mode_i ),
  .clk_o ( clk_ext_usb )
);


////////////////////////////////////////
// SW Bypass select logic
////////////////////////////////////////
// Sync to local AON clock
prim_mubi_pkg::mubi4_t ot_io_clk_byp_req, ot_all_clk_byp_req, ot_ext_freq_is_96m;

prim_mubi4_sync #(
  .StabilityCheck ( 1 ),
  .ResetValue ( prim_mubi_pkg::MuBi4False )
) u_io_clk_byp_req (
  .clk_i ( clk_aon ),
  .rst_ni ( rst_main_n ),
  .mubi_i ( io_clk_byp_req_i ),
  .mubi_o ( {ot_io_clk_byp_req} )
);

prim_mubi4_sync #(
  .StabilityCheck ( 1 ),
  .ResetValue ( prim_mubi_pkg::MuBi4False )
) u_all_clk_byp_req (
  .clk_i ( clk_aon ),
  .rst_ni ( rst_main_n ),
  .mubi_i ( all_clk_byp_req_i ),
  .mubi_o ( {ot_all_clk_byp_req} )
);

prim_mubi4_sync #(
  .StabilityCheck ( 1 ),
  .ResetValue ( prim_mubi_pkg::MuBi4False )
) u_ext_freq_is_96m (
  .clk_i ( clk_aon ),
  .rst_ni ( rst_main_n ),
  .mubi_i ( ext_freq_is_96m_i ),
  .mubi_o ( {ot_ext_freq_is_96m} )
);

// Decode logic
logic ot_all_clk_byp, ot_sys_clk_byp, ot_io_clk_byp, ot_usb_clk_byp, ot_aon_clk_byp;

prim_mubi4_dec u_all_byp_sel ( .mubi_i ( ot_all_clk_byp_req ), .mubi_dec_o ( ot_all_clk_byp ) );
prim_mubi4_dec u_sys_byp_sel ( .mubi_i ( ot_all_clk_byp_req ), .mubi_dec_o ( ot_sys_clk_byp ) );
prim_mubi4_dec u_io_byp_sel  ( .mubi_i ( ot_io_clk_byp_req ),  .mubi_dec_o ( ot_io_clk_byp ) );
prim_mubi4_dec u_usb_byp_sel ( .mubi_i ( ot_all_clk_byp_req ), .mubi_dec_o ( ot_usb_clk_byp ) );
prim_mubi4_dec u_aon_byp_sel ( .mubi_i ( ot_all_clk_byp_req ), .mubi_dec_o ( ot_aon_clk_byp ) );

// De-Glitch selects (decode "noise")
logic sw_sys_clk_byp, sw_usb_clk_byp, sw_aon_clk_byp, sw_exfr_is_96m;

prim_flop #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_sw_all_clk_byp_dgl (
  .clk_i ( clk_aon ),
  .rst_ni ( rst_main_n ),
  .d_i ( ot_all_clk_byp ),
  .q_o ( sw_all_clk_byp )
);

prim_flop #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_sw_sys_clk_byp_dgl (
  .clk_i ( clk_aon ),
  .rst_ni ( rst_main_n ),
  .d_i ( ot_sys_clk_byp ),
  .q_o ( sw_sys_clk_byp )
);

prim_flop #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_sw_io_clk_byp_dgl (
  .clk_i ( clk_aon ),
  .rst_ni ( rst_main_n ),
  .d_i ( ot_io_clk_byp ),
  .q_o ( sw_io_clk_byp )
);

prim_flop #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_sw_usb_clk_byp_dgl (
  .clk_i ( clk_aon ),
  .rst_ni ( rst_main_n ),
  .d_i ( ot_usb_clk_byp ),
  .q_o ( sw_usb_clk_byp )
);

prim_flop #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_sw_aon_clk_byp_dgl (
  .clk_i ( clk_aon ),
  .rst_ni ( rst_main_n ),
  .d_i ( ot_aon_clk_byp ),
  .q_o ( sw_aon_clk_byp )
);

prim_flop #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_sw_exfr_is_96m_dgl (
  .clk_i ( clk_aon ),
  .rst_ni ( rst_main_n ),
  .d_i ( prim_mubi_pkg::mubi4_test_true_strict(ot_ext_freq_is_96m) ),
  .q_o ( sw_exfr_is_96m )
);

logic sys_clk_byp;
logic sel_sys_clk_byp;

assign sel_sys_clk_byp = dft_clks_byp || sw_sys_clk_byp;

// De-Glitch System Clock Bypass Select
////////////////////////////////////////
prim_flop #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_sys_clk_byp_dgl (
  .clk_i ( clk_aon ),
  .rst_ni ( rst_main_n ),
  .d_i ( sel_sys_clk_byp ),
  .q_o ( sys_clk_byp )
);

logic sel_io_clk_byp, io_clk_byp;

assign sel_io_clk_byp = dft_clks_byp || sw_io_clk_byp || sw_all_clk_byp;

// De-Glitch IO Clock Bypass Select
////////////////////////////////////////
prim_flop #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_io_clk_byp_dgl (
  .clk_i ( clk_aon ),
  .rst_ni ( rst_main_n ),
  .d_i ( sel_io_clk_byp ),
  .q_o ( io_clk_byp )
);

logic usb_clk_byp;
logic sel_usb_clk_byp;

assign sel_usb_clk_byp = dft_clks_byp || sw_usb_clk_byp;

// De-Glitch USB Clock Bypass Select
////////////////////////////////////////
prim_flop #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_usb_clk_byp_dgl (
  .clk_i ( clk_aon ),
  .rst_ni ( rst_main_n ),
  .d_i ( sel_usb_clk_byp ),
  .q_o ( usb_clk_byp )
);

logic aon_clk_byp;
logic sel_aon_clk_byp;

assign sel_aon_clk_byp = dft_clks_byp || sw_aon_clk_byp;

// De-Glitch AON Clock Bypass Select
////////////////////////////////////////
prim_flop #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_aon_clk_byp_dgl (
  .clk_i ( clk_aon ),
  .rst_ni ( rst_main_n ),
  .d_i ( sel_aon_clk_byp ),
  .q_o ( aon_clk_byp )
);

logic extfreq_is_96m;

// De-Glitch Extrnal Frequecy Indication
////////////////////////////////////////
always_ff @( posedge clk_aon, negedge rst_main_n ) begin
  if ( !rst_main_n ) begin
    extfreq_is_96m <= 1'b1;
  end else if ( dft_clks_byp ) begin
    extfreq_is_96m <= dft_ext_is_96m;      // DFT
  end else if ( sw_io_clk_byp || sw_all_clk_byp ) begin
    extfreq_is_96m <= sw_exfr_is_96m;      // SW
  end
end

// Block changes during scan mode
////////////////////////////////////////
logic sys_clk_byp_sel, io_clk_byp_sel, usb_clk_byp_sel, aon_clk_byp_sel;

`ifdef AST_BYPASS_CLK
assign sys_clk_byp_sel = sys_clk_byp;
assign io_clk_byp_sel  = io_clk_byp;
assign usb_clk_byp_sel = usb_clk_byp;
assign aon_clk_byp_sel = aon_clk_byp;
assign ext_freq_is_96m = extfreq_is_96m;
`else // of AST_BYPASS_CLK
always_latch begin
  if ( !scan_mode_i ) begin
    sys_clk_byp_sel = sys_clk_byp;
    io_clk_byp_sel  = io_clk_byp;
    usb_clk_byp_sel = usb_clk_byp;
    aon_clk_byp_sel = aon_clk_byp;
    ext_freq_is_96m = extfreq_is_96m;
  end
end
`endif // of AST_BYPASS_CLK

////////////////////////////////////////
// Clocks Bypass Muxes
////////////////////////////////////////
logic sys_clk_osc_en, io_clk_osc_en, usb_clk_osc_en;
logic sys_clk_byp_en, io_clk_byp_en, usb_clk_byp_en;
logic rst_clk_osc_n, rst_clk_ext_n;

assign rst_clk_osc_n = scan_mode_i ? scan_reset_ni : vcmain_pok_i;
//  assign rst_clk_osc_n = scan_mode_i ? scan_reset_ni : vcaon_pok;
//  assign rst_clk_ext_n = scan_mode_i ? scan_reset_ni : vcaon_pok_por_i;
assign rst_clk_ext_n = scan_mode_i ? scan_reset_ni : vcmain_pok_por_i;

logic sys_select_ext, io_select_ext, usb_select_ext, aon_select_ext;

assign sys_select_ext = sys_clk_byp_sel;
assign io_select_ext  =  io_clk_byp_sel;
assign usb_select_ext = usb_clk_byp_sel;
assign aon_select_ext = aon_clk_byp_sel;

// DV Hooks for IO clocks
logic io_clk_byp_select, io_clk_byp_sel_buf, io_clk_osc_en_buf, io_clk_byp_en_buf;

assign io_clk_byp_select = io_select_ext;

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
logic rst_clk_osc_usb_n, rst_clk_ext_usb_n;

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

prim_buf u_rst_clk_osc_usb (
  .in_i ( rst_clk_osc_n ),
  .out_o ( rst_clk_osc_usb_n )
);

prim_buf u_rst_clk_ext_usb (
  .in_i ( rst_clk_ext_n ),
  .out_o ( rst_clk_ext_usb_n )
);

// rst_main_n deasset to io clock
////////////////////////////////////////
logic rst_main_da_n_ioda, rst_aon_ioda_n;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_rst_main_da_n_ioda_sync (
  .clk_i ( clk_src_io_o ),
  .rst_ni ( rst_main_n ),
  .d_i ( 1'b1 ),
  .q_o ( rst_main_da_n_ioda )
);

assign rst_aon_ioda_n = scan_mode_i ? scan_reset_ni : rst_main_da_n_ioda;

// SYS Clock Bypass Mux
////////////////////////////////////////
gfr_clk_mux2 u_clk_src_sys_sel (
  .clk_osc_i ( clk_osc_sys_i ),
  .clk_osc_val_i ( clk_osc_sys_val_i ),
  .rst_clk_osc_ni ( rst_clk_osc_sys_n  ),
  .clk_ext_i ( clk_ext_sys ),
  .clk_ext_val_i ( clk_ext_sys_val ),
  .rst_clk_ext_ni ( rst_clk_ext_sys_n  ),
  .ext_sel_i ( sys_select_ext ),
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
  .rst_clk_osc_ni ( rst_clk_osc_io_n  ),
  .clk_ext_i ( clk_ext_io ),
  .clk_ext_val_i ( clk_ext_io_val ),
  .rst_clk_ext_ni ( rst_clk_ext_io_n  ),
  .ext_sel_i ( io_select_ext ),
  .clk_osc_en_o ( io_clk_osc_en ),
  .clk_ext_en_o ( io_clk_byp_en ),
  .clk_val_o ( clk_src_io_val ),
  .clk_o ( clk_src_io )
);

`ifndef AST_BYPASS_CLK
assign clk_src_io_val_o = clk_src_io_val;
assign clk_src_io_o = clk_src_io;
`else // of AST_BYPASS_CLK
// For FPGA, clk_ext is always the one frequency, so divide by 2 if downstream
// thinks it should be "48 MHz" instead of "96 MHz".
logic ext_freq_is_96m_io_sync;
logic rst_src_io_n;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_no_scan_rst_src_io_n_sync (
  .clk_i ( clk_src_io ),
  .rst_ni ( rst_main_n ),
  .d_i ( 1'b1 ),
  .q_o ( rst_src_io_n )
);

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_no_scan_ext_freq_is_96m_io_sync (
  .clk_i ( clk_src_io ),
  .rst_ni ( rst_src_io_n ),
  .d_i ( ext_freq_is_96m ),
  .q_o ( ext_freq_is_96m_io_sync )
);

logic clk_src_io_div2_sel;
assign clk_src_io_div2_sel = !ext_freq_is_96m_io_sync & io_clk_byp_sel;

prim_clock_div #(
  .Divisor( 2 )
) u_no_scan_clk_src_io_d1ord2 (
  .clk_i ( clk_src_io ),
  .rst_ni ( rst_src_io_n ),
  .step_down_req_i( !clk_src_io_div2_sel ),
  .step_down_ack_o ( ),
  .test_en_i ( scan_mode_i ),
  .clk_o ( clk_src_io_o )
);

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_no_scan_clk_src_io_val_sync (
  .clk_i ( clk_src_io_o ),
  .rst_ni ( rst_aon_ioda_n ),
  .d_i ( clk_src_io_val ),
  .q_o ( clk_src_io_val_o )
);
`endif // of AST_BYPASS_CLK

// USB Clock Bypass Mux
////////////////////////////////////////
gfr_clk_mux2 u_clk_src_usb_sel (
  .clk_osc_i ( clk_osc_usb_i ),
  .clk_osc_val_i ( clk_osc_usb_val_i ),
  .rst_clk_osc_ni ( rst_clk_osc_usb_n  ),
  .clk_ext_i ( clk_ext_usb ),
  .clk_ext_val_i ( clk_ext_usb_val ),
  .rst_clk_ext_ni ( rst_clk_ext_usb_n  ),
  .ext_sel_i ( usb_select_ext ),
  .clk_osc_en_o ( usb_clk_osc_en ),
  .clk_ext_en_o ( usb_clk_byp_en ),
  .clk_val_o ( clk_src_usb_val_o ),
  .clk_o ( clk_src_usb_o )
);

// All Clocks Bypass Acknowledge
////////////////////////////////////////
// Use aon_clk_byp_en from AON domain via interface
logic all_clks_byp_en_src, all_clks_byp_en;

always_ff @( posedge clk_aon, negedge rst_main_n ) begin
  if ( !rst_main_n ) begin
    all_clks_byp_en_src <= 1'b0;
  end else begin
    all_clks_byp_en_src <= sw_all_clk_byp && sys_clk_byp_en && io_clk_byp_en &&
                             usb_clk_byp_en && aon_to_main_i.aon_clk_byp_en;
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

always_ff @( posedge clk_aon, negedge rst_main_n ) begin
  if ( !rst_main_n ) begin
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

// IO Clock Source is 48MHz
////////////////////////////////////////
logic io_clk_byp_is_48m_src, io_clk_byp_is_48m;

// Oscillator source is always 96MHz.
// External Bypass source is assume to be 96MHz until it is ebabled as 48MHz
always_ff @( posedge clk_aon, negedge rst_main_n ) begin
  if ( !rst_main_n ) begin
    io_clk_byp_is_48m_src <= 1'b0;
  end else begin
    io_clk_byp_is_48m_src <= io_clk_byp_en && !ext_freq_is_96m;
  end
end

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_io_clk_byp_is_48m_sync (
  .clk_i ( clk_src_io_o ),
  .rst_ni ( rst_aon_ioda_n ),
  .d_i ( io_clk_byp_is_48m_src ),
  .q_o ( io_clk_byp_is_48m )
);

prim_mubi4_sender #(
  .ResetValue ( prim_mubi_pkg::MuBi4False )
) u_clk_src_io_48m_sync (
  .clk_i ( clk_src_io_o ),
  .rst_ni ( rst_aon_ioda_n ),
  .mubi_i ( prim_mubi_pkg::mubi4_bool_to_mubi(io_clk_byp_is_48m) ),
  .mubi_o ( {clk_src_io_48m_o} )
);


////////////////////////////////////////
// Scan reset pulse on scan mode RE.
////////////////////////////////////////
logic scan_mode_d1, scan_mode_d2, scan_mode_da;

prim_flop #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_no_scan_scan_mode_d1 (
  .clk_i ( clk_src_io_pre_occ_i ),
  .rst_ni ( vcmain_pok_i ),
  .d_i ( scan_mode_i ),
  .q_o ( scan_mode_d1 )
);

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_no_scan_scan_mode_d2 (
  .clk_i ( clk_src_io_pre_occ_i ),
  .rst_ni ( vcmain_pok_i ),
  .d_i ( scan_mode_d1 ),
  .q_o ( scan_mode_d2 )
);

// De-Assert Sync
prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_no_scan_scmd_dasrt (
  .clk_i ( clk_src_io_pre_occ_i ),
  .rst_ni ( scan_mode_d2 ),
  .d_i ( 1'b1 ),
  .q_o ( scan_mode_da )
);

assign force_scan_reset_o = scan_mode_d1 && !scan_mode_da;


////////////////////////////////////////
// Interface to AON domain
////////////////////////////////////////
assign main_to_aon_o.clk_ext_aon = clk_ext_aon;
assign main_to_aon_o.aon_select_ext = aon_select_ext;


/////////////////////
// Unused Signals  //
/////////////////////
logic unused_sigs;

assign unused_sigs = ^{ io_clk_byp_sel_buf,
                        io_clk_byp_en_buf,
                        io_clk_osc_en_buf,
                        sys_clk_osc_en,
                        io_clk_osc_en,
                        usb_clk_osc_en,
                        clk_ast_tlul_i,
                        aon_to_main_i.clk_src_aon_val_o
                      };

endmodule : ast_clks_byp_main
