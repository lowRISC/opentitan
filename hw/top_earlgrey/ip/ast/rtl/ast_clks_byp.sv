// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: ast_clks_byp
// *Module Description: AST Clocks Bypass
//############################################################################

`include "prim_assert.sv"

module ast_clks_byp (
  input clk_i,                              // TLUL Clock
  input rst_ni,                             // TLUL Reset
  input vcaon_pok_i,                        // VCAON POK
  input deep_sleep_i,                       // Deep Sleep (main regulator & switch are off)
  input clk_osc_sys_i,                      // SYS Oscillator Clock
  input clk_osc_sys_val_i,                  // SYS Oscillator Clock Valid
  input clk_osc_io_i,                       // IO Oscillator Clock
  input clk_osc_io_val_i,                   // IO Oscillator Clock Valid
  input clk_osc_usb_i,                      // USB Oscillator Clock
  input clk_osc_usb_val_i,                  // USB Oscillator Clock Valid
  input clk_osc_aon_i,                      // AON Oscillator Clock
  input clk_osc_aon_val_i,                  // AON Oscillator Clock Valid
  input clk_ast_ext_i,                      // External Clock
  input prim_mubi_pkg::mubi4_t io_clk_byp_req_i,  // External IO clock mux for OTP bootstrap
  input prim_mubi_pkg::mubi4_t all_clk_byp_req_i, // External all clock mux override
  input ext_freq_is_96m_i,                  // External Clock Frequecy is 96MHz (else 48MHz)
  output prim_mubi_pkg::mubi4_t io_clk_byp_ack_o,   // Switch IO clock to External clock
  output prim_mubi_pkg::mubi4_t all_clk_byp_ack_o,  // Switch all clocks to External clock
  output logic clk_src_sys_o,               // SYS Source Clock
  output logic clk_src_sys_val_o,           // SYS Source Clock Valid
  output logic clk_src_io_o,                // IO Source Clock
  output logic clk_src_io_val_o,            // IO Source Clock Valid
  output logic clk_src_usb_o,               // USB Source Clock
  output logic clk_src_usb_val_o,           // USB Source Clock Valid
  output logic clk_src_aon_o,               // AON Source Clock
  output logic clk_src_aon_val_o            // AON Source Clock Valid
);

logic ext_clk, rst_aon_n;

logic scan_mode_i;

assign scan_mode_i = 1'b0;
assign ext_clk     = clk_ast_ext_i;
assign rst_aon_n   = vcaon_pok_i;


////////////////////////////////////////
// Source Clocks Selection
////////////////////////////////////////



// SW Bypass select logic
////////////////////////////////////////

// Sync to local TLUL clcok
prim_mubi_pkg::mubi4_t io_clk_byp_req, all_clk_byp_req;
logic sw_ext_freq_is_96m;

prim_mubi4_sync #(
  .StabilityCheck ( 1 ),
  .ResetValue ( prim_mubi_pkg::MuBi4False )
) u_io_clk_byp_req (
  .clk_i,
  .rst_ni,
  .mubi_i ( io_clk_byp_req_i ),
  .mubi_o ( io_clk_byp_req )
);

prim_mubi4_sync #(
  .StabilityCheck ( 1 ),
  .ResetValue ( prim_mubi_pkg::MuBi4False )
) u_all_clk_byp_req (
  .clk_i,
  .rst_ni,
  .mubi_i ( all_clk_byp_req_i ),
  .mubi_o ( all_clk_byp_req )
);

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_sw_ext_freq_sync (
  .clk_i ( ext_clk ),
  .rst_ni ( rst_aon_n ),
  .d_i ( ext_freq_is_96m_i ),
  .q_o ( sw_ext_freq_is_96m )
);

// Decode logic
prim_mubi_pkg::mubi4_t io_clk_byp_sel_req;
logic all_clk_byp, sys_clk_byp, io_clk_byp, usb_clk_byp, aon_clk_byp;

assign io_clk_byp_sel_req = prim_mubi_pkg::mubi4_test_true_strict( all_clk_byp_req ) ?
                            prim_mubi_pkg::MuBi4True : io_clk_byp_req;

prim_mubi4_dec u_all_byp_sel ( .mubi_i ( all_clk_byp_req ), .mubi_dec_o ( all_clk_byp ) );
prim_mubi4_dec u_sys_byp_sel ( .mubi_i ( all_clk_byp_req ), .mubi_dec_o ( sys_clk_byp ) );
prim_mubi4_dec u_io_byp_sel  ( .mubi_i ( io_clk_byp_sel_req ), .mubi_dec_o ( io_clk_byp ) );
prim_mubi4_dec u_usb_byp_sel ( .mubi_i ( all_clk_byp_req ), .mubi_dec_o ( usb_clk_byp ) );
prim_mubi4_dec u_aon_byp_sel ( .mubi_i ( all_clk_byp_req ), .mubi_dec_o ( aon_clk_byp ) );

// De-Glitch selects (decode "noise")
logic sw_all_clk_byp, sw_sys_clk_byp, sw_io_clk_byp, sw_usb_clk_byp, sw_aon_clk_byp;

always_ff @ ( posedge clk_i, negedge rst_ni ) begin
  if ( !rst_ni ) begin
    sw_all_clk_byp <= 1'b0;
    sw_sys_clk_byp <= 1'b0;
    sw_io_clk_byp <= 1'b0;
    sw_usb_clk_byp <= 1'b0;
    sw_aon_clk_byp <= 1'b0;
  end else begin
    sw_all_clk_byp <= all_clk_byp;
    sw_sys_clk_byp <= sys_clk_byp;
    sw_io_clk_byp <= io_clk_byp;
    sw_usb_clk_byp <= usb_clk_byp;
    sw_aon_clk_byp <= aon_clk_byp;
  end
end

logic sys_clk_byp_sel, io_clk_byp_sel, usb_clk_byp_sel, aon_clk_byp_sel, ext_freq_is_96m;

assign sys_clk_byp_sel = sw_sys_clk_byp;
assign io_clk_byp_sel  = sw_io_clk_byp;
assign usb_clk_byp_sel = sw_usb_clk_byp;
assign aon_clk_byp_sel = sw_aon_clk_byp;
assign ext_freq_is_96m = sw_ext_freq_is_96m;


// External USB & AON clocks genaration
////////////////////////////////////////
logic ext_clk_usb, clk_usb_ext;

prim_clock_div #(
  .Divisor( 2 )
) u_clk_ext_div2_div (
  .clk_i ( ext_clk ),
  .rst_ni ( rst_aon_n ),
  .step_down_req_i( !ext_freq_is_96m ),
  .step_down_ack_o ( ),
  .test_en_i ( scan_mode_i ),
  .clk_o ( ext_clk_usb )
);

assign clk_usb_ext = ext_clk_usb;

logic clk_usb_ext_d240, clk_ext_aon;

prim_clock_div #(
  .Divisor( 240 )
) u_clk_usb_div240_div (
  .clk_i ( clk_usb_ext ),
  .rst_ni ( rst_aon_n ),
  .step_down_req_i( 1'b0 ),
  .step_down_ack_o ( ),
  .test_en_i ( scan_mode_i ),
  .clk_o ( clk_usb_ext_d240 )
);

assign clk_ext_aon = clk_usb_ext_d240;


// Deep Slepp Gators
////////////////////////////////////////
logic deep_sleep_n;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_deep_sleep_sync (
  .clk_i ( ext_clk ),
  .rst_ni ( rst_aon_n ),
  .d_i ( !deep_sleep_i ),
  .q_o ( deep_sleep_n )
);

// SYS & IO
logic clk_ext_sys, clk_ext_io;

prim_clock_gating #(
  .NoFpgaGate ( 1'b1)
) u_clk_ext_sys_ckgt (
  .clk_i ( ext_clk ),
  .en_i ( deep_sleep_n ),
  .test_en_i ( scan_mode_i ),
  .clk_o ( clk_ext_sys )
);

assign clk_ext_io = clk_ext_sys;

// USB SYS
logic clk_ext_usb;

prim_clock_gating #(
  .NoFpgaGate ( 1'b1)
) u_clk_ext_usb_ckgt (
  .clk_i ( clk_usb_ext ),
  .en_i ( deep_sleep_n ),
  .test_en_i ( scan_mode_i ),
  .clk_o ( clk_ext_usb )
);

logic sys_clk_osc_en, io_clk_osc_en, usb_clk_osc_en, aon_clk_osc_en;
logic sys_clk_byp_en, io_clk_byp_en, usb_clk_byp_en, aon_clk_byp_en;

logic rst_clk_osc_n, rst_clk_ext_n;
assign rst_clk_osc_n = vcaon_pok_i;
assign rst_clk_ext_n = vcaon_pok_i;

// SYS Clock Bypass Mux
////////////////////////////////////////
gfr_clk_mux2 u_clk_src_sys_sel (
  .clk_osc_i ( clk_osc_sys_i ),
  .rst_clk_osc_ni ( rst_clk_osc_n ),
  .clk_ext_i ( clk_ext_sys ),
  .rst_clk_ext_ni ( rst_clk_ext_n ),
  .ext_sel_i ( sys_clk_byp_sel ),
  .clk_osc_en_o ( sys_clk_osc_en ),
  .clk_ext_en_o ( sys_clk_byp_en ),
  .clk_o ( clk_src_sys_o )
);

// IO Clock Bypass Mux
////////////////////////////////////////
gfr_clk_mux2 u_clk_src_io_sel (
  .clk_osc_i ( clk_osc_io_i ),
  .rst_clk_osc_ni ( rst_clk_osc_n ),
  .clk_ext_i ( clk_ext_io ),
  .rst_clk_ext_ni ( rst_clk_ext_n ),
  .ext_sel_i ( io_clk_byp_sel ),
  .clk_osc_en_o ( io_clk_osc_en ),
  .clk_ext_en_o ( io_clk_byp_en ),
  .clk_o ( clk_src_io_o )
);

// USB Clock Bypass Mux
////////////////////////////////////////
gfr_clk_mux2 u_clk_src_usb_sel (
  .clk_osc_i ( clk_osc_usb_i ),
  .rst_clk_osc_ni ( rst_clk_osc_n ),
  .clk_ext_i ( clk_ext_usb ),
  .rst_clk_ext_ni ( rst_clk_ext_n ),
  .ext_sel_i ( usb_clk_byp_sel ),
  .clk_osc_en_o ( usb_clk_osc_en ),
  .clk_ext_en_o ( usb_clk_byp_en ),
  .clk_o ( clk_src_usb_o )
);

// AON Clock Bypass Mux
////////////////////////////////////////
gfr_clk_mux2 u_clk_src_aon_sel (
  .clk_osc_i ( clk_osc_aon_i ),
  .rst_clk_osc_ni ( rst_clk_osc_n ),
  .clk_ext_i ( clk_ext_aon ),
  .rst_clk_ext_ni ( rst_clk_ext_n ),
  .ext_sel_i ( aon_clk_byp_sel ),
  .clk_osc_en_o ( aon_clk_osc_en ),
  .clk_ext_en_o ( aon_clk_byp_en ),
  .clk_o ( clk_src_aon_o )
);

assign clk_src_sys_val_o = sys_clk_byp_sel ? sys_clk_byp_en : sys_clk_osc_en && clk_osc_sys_val_i;
assign clk_src_io_val_o  = io_clk_byp_sel  ? io_clk_byp_en  : io_clk_osc_en && clk_osc_io_val_i;
assign clk_src_usb_val_o = usb_clk_byp_sel ? usb_clk_byp_en : usb_clk_osc_en && clk_osc_usb_val_i;
assign clk_src_aon_val_o = aon_clk_byp_sel ? aon_clk_byp_en : aon_clk_osc_en && clk_osc_aon_val_i;

logic all_clks_byp_en;
prim_mubi_pkg::mubi4_t all_clk_byp_ack;

assign all_clks_byp_en = sw_all_clk_byp && sys_clk_byp_en && io_clk_byp_en &&
                         usb_clk_byp_en && aon_clk_byp_en;

assign all_clk_byp_ack = all_clks_byp_en ? prim_mubi_pkg::MuBi4True :
                                           prim_mubi_pkg::MuBi4False;

prim_mubi4_sender #(
  .ResetValue ( prim_mubi_pkg::MuBi4False )
) u_all_clk_byp_ack (
  .clk_i,
  .rst_ni,
  .mubi_i ( all_clk_byp_ack ),
  .mubi_o ( all_clk_byp_ack_o )
);

logic only_io_clk_byp_en;
prim_mubi_pkg::mubi4_t io_clk_byp_ack;

assign only_io_clk_byp_en = !sw_all_clk_byp && sw_io_clk_byp && io_clk_byp_en;

assign io_clk_byp_ack = only_io_clk_byp_en ? prim_mubi_pkg::MuBi4True :
                                             prim_mubi_pkg::MuBi4False;

prim_mubi4_sender #(
  .ResetValue ( prim_mubi_pkg::MuBi4False )
) u_io_clk_byp_ack (
  .clk_i,
  .rst_ni,
  .mubi_i ( io_clk_byp_ack ),
  .mubi_o ( io_clk_byp_ack_o )
);

endmodule : ast_clks_byp
