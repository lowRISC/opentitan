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
  input vcaon_pok_i,                        // AON POK
  input clk_osc_sys_i,                      // SYS Oscillator Clock
  input clk_osc_sys_val_i,                  // SYS Oscillator Clock Valid
  input clk_osc_io_i,                       // IO Oscillator Clock
  input clk_osc_io_val_i,                   // IO Oscillator Clock Valid
  input clk_osc_usb_i,                      // USB Oscillator Clock
  input clk_osc_usb_val_i,                  // USB Oscillator Clock Valid
  input clk_osc_aon_i,                      // AON Oscillator Clock
  input clk_osc_aon_val_i,                  // AON Oscillator Clock Valid
  input prim_mubi_pkg::mubi4_t io_clk_byp_req_i,  // External IO clock mux for OTP bootstrap
  input prim_mubi_pkg::mubi4_t all_clk_byp_req_i, // External all clock mux override
  input ext_freq_is_96m_i,                  // External Clock Frequecy is 96MHz (else 48MHz)
  input clk_ast_ext_i,                      // External Clock
  output logic clk_src_sys_o,               // SYS Source Clock
  output logic clk_src_sys_val_o,           // SYS Source Clock Valid
  output logic clk_src_io_o,                // IO Source Clock
  output logic clk_src_io_val_o,            // IO Source Clock Valid
  output logic clk_src_usb_o,               // USB Source Clock
  output logic clk_src_usb_val_o,           // USB Source Clock Valid
  output logic clk_src_aon_o,               // AON Source Clock
  output logic clk_src_aon_val_o,           // AON Source Clock Valid
  output prim_mubi_pkg::mubi4_t io_clk_byp_ack_o,   // Switch IO clock to External clock
  output prim_mubi_pkg::mubi4_t all_clk_byp_ack_o,  // Switch all clocks to External clock
  // memories read-write margins
  output ast_pkg::dpm_rm_t dpram_rmf_o,     // Dual Port RAM Read-write Margin Fast
  output ast_pkg::dpm_rm_t dpram_rml_o,     // Dual Port RAM Read-write Margin sLow
  output ast_pkg::spm_rm_t spram_rm_o,      // Single Port RAM Read-write Margin
  output ast_pkg::spm_rm_t sprgf_rm_o,      // Single Port Reg-File Read-write Margin
  output ast_pkg::spm_rm_t sprom_rm_o       // Single Port ROM Read-write Margin
);

logic ext_clk, rst_aon_n;

logic scan_mode_i;
assign scan_mode_i = 1'b0;

assign ext_clk   = clk_ast_ext_i;
assign rst_aon_n = vcaon_pok_i;


////////////////////////////////////////
// Source Clocks Selection
////////////////////////////////////////



// SW Bypass select logic
////////////////////////////////////////
prim_mubi_pkg::mubi4_t  io_clk_byp_req;

assign io_clk_byp_req = prim_mubi_pkg::mubi4_test_true_strict( all_clk_byp_req_i ) ?
                          prim_mubi_pkg::MuBi4True : io_clk_byp_req_i;

logic all_clk_byp, sys_clk_byp, io_clk_byp, usb_clk_byp, aon_clk_byp;

prim_mubi4_dec u_all_byp_sel ( .mubi_i ( all_clk_byp_req_i ), .mubi_dec_o ( all_clk_byp ) );
prim_mubi4_dec u_sys_byp_sel ( .mubi_i ( all_clk_byp_req_i ), .mubi_dec_o ( sys_clk_byp ) );
prim_mubi4_dec u_io_byp_sel  ( .mubi_i ( io_clk_byp_req ), .mubi_dec_o ( io_clk_byp ) );
prim_mubi4_dec u_usb_byp_sel ( .mubi_i ( all_clk_byp_req_i ), .mubi_dec_o ( usb_clk_byp ) );
prim_mubi4_dec u_aon_byp_sel ( .mubi_i ( all_clk_byp_req_i ), .mubi_dec_o ( aon_clk_byp ) );

// Sync to De-Glitch selects
logic sw_all_clk_byp, sw_sys_clk_byp, sw_io_clk_byp, sw_usb_clk_byp, sw_aon_clk_byp;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_sw_all_clk_byp (
  .clk_i,
  .rst_ni,
  .d_i ( all_clk_byp ),
  .q_o ( sw_all_clk_byp )
);

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_sw_sys_clk_byp (
  .clk_i,
  .rst_ni,
  .d_i ( sys_clk_byp ),
  .q_o ( sw_sys_clk_byp )
);

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_sw_io_clk_byp (
  .clk_i,
  .rst_ni,
  .d_i ( io_clk_byp ),
  .q_o ( sw_io_clk_byp )
);

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_sw_usb_clk_byp (
  .clk_i,
  .rst_ni,
  .d_i ( usb_clk_byp ),
  .q_o ( sw_usb_clk_byp )
);

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_sw_aon_clk_byp (
  .clk_i,
  .rst_ni,
  .d_i ( aon_clk_byp ),
  .q_o ( sw_aon_clk_byp )
);

logic sw_ext_freq_is_96m;

prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_ (
  .clk_i ( ext_clk ),
  .rst_ni ( rst_aon_n ),
  .d_i ( ext_freq_is_96m_i ),
  .q_o ( sw_ext_freq_is_96m )
);

logic sys_clk_byp_sel, io_clk_byp_sel, usb_clk_byp_sel, aon_clk_byp_sel, ext_freq_is_96m;

assign sys_clk_byp_sel = sw_sys_clk_byp;
assign io_clk_byp_sel  = sw_io_clk_byp;
assign usb_clk_byp_sel = sw_usb_clk_byp;
assign aon_clk_byp_sel = sw_aon_clk_byp;
assign ext_freq_is_96m = sw_ext_freq_is_96m;


// External USB & AON clocks genaration
////////////////////////////////////////
logic clk_usb_ext_d2, clk_usb_ext;

prim_clock_div #(
  .Divisor( 2 )
) u_clk_ext_div2_div (
  .clk_i ( ext_clk ),
  .rst_ni ( rst_aon_n ),
  .step_down_req_i( ext_freq_is_96m ),
  .step_down_ack_o ( ),
  .test_en_i ( scan_mode_i ),
  .clk_o ( clk_usb_ext_d2 )
);

assign clk_usb_ext = clk_usb_ext_d2;

logic clk_usb_ext_d240, clk_aon_ext;

prim_clock_div #(
  .Divisor( 240 )
) u_clk_usb_div240_div (
  .clk_i ( clk_usb_ext ),
  .rst_ni ( rst_aon_n ),
  .step_down_req_i( 1'b1 ),
  .step_down_ack_o ( ),
  .test_en_i ( scan_mode_i ),
  .clk_o ( clk_usb_ext_d240 )
);

assign clk_aon_ext = clk_usb_ext_d240;

logic sys_clk_byp_en, io_clk_byp_en, usb_clk_byp_en, aon_clk_byp_en;

logic rst_clk_osc_n, rst_clk_ext_n;
assign rst_clk_osc_n = vcaon_pok_i;
assign rst_clk_ext_n = vcaon_pok_i;

// SYS Clock Bypass Mux
////////////////////////////////////////
gfr_clk_mux2 u_clk_src_sys_sel (
  .clk_osc_i ( clk_osc_sys_i ),
  .rst_clk_osc_ni ( rst_clk_osc_n ),
  .clk_ext_i ( ext_clk ),
  .rst_clk_ext_ni ( rst_clk_ext_n ),
  .ext_sel_i ( sys_clk_byp_sel ),
  .clk_osc_en_o ( ),
  .clk_ext_en_o ( sys_clk_byp_en ),
  .clk_o ( clk_src_sys_o )
);

// IO Clock Bypass Mux
////////////////////////////////////////
gfr_clk_mux2 u_clk_src_io_sel (
  .clk_osc_i ( clk_osc_io_i ),
  .rst_clk_osc_ni ( rst_clk_osc_n ),
  .clk_ext_i ( ext_clk ),
  .rst_clk_ext_ni ( rst_clk_ext_n ),
  .ext_sel_i ( io_clk_byp_sel ),
  .clk_osc_en_o ( ),
  .clk_ext_en_o ( io_clk_byp_en ),
  .clk_o ( clk_src_io_o )
);

// USB Clock Bypass Mux
////////////////////////////////////////
gfr_clk_mux2 u_clk_src_usb_sel (
  .clk_osc_i ( clk_osc_usb_i ),
  .rst_clk_osc_ni ( rst_clk_osc_n ),
  .clk_ext_i ( clk_usb_ext ),
  .rst_clk_ext_ni ( rst_clk_ext_n ),
  .ext_sel_i ( usb_clk_byp_sel ),
  .clk_osc_en_o ( ),
  .clk_ext_en_o ( usb_clk_byp_en ),
  .clk_o ( clk_src_usb_o )
);

// AON Clock Bypass Mux
////////////////////////////////////////
gfr_clk_mux2 u_clk_src_aon_sel (
  .clk_osc_i ( clk_osc_aon_i ),
  .rst_clk_osc_ni ( rst_clk_osc_n ),
  .clk_ext_i ( clk_aon_ext ),
  .rst_clk_ext_ni ( rst_clk_ext_n ),
  .ext_sel_i ( aon_clk_byp_sel ),
  .clk_osc_en_o ( ),
  .clk_ext_en_o ( aon_clk_byp_en ),
  .clk_o ( clk_src_aon_o )
);

assign clk_src_sys_val_o = sys_clk_byp_sel ? sys_clk_byp_en : clk_osc_sys_val_i;
assign clk_src_io_val_o  = io_clk_byp_sel  ? io_clk_byp_en  : clk_osc_io_val_i;
assign clk_src_usb_val_o = usb_clk_byp_sel ? usb_clk_byp_en : clk_osc_usb_val_i;
assign clk_src_aon_val_o = aon_clk_byp_sel ? aon_clk_byp_en : clk_osc_aon_val_i;

logic all_clks_byp_en, only_io_clk_byp_en;

assign all_clks_byp_en = sw_all_clk_byp && sys_clk_byp_en && io_clk_byp_en &&
                         usb_clk_byp_en && aon_clk_byp_en;

assign only_io_clk_byp_en = !sw_all_clk_byp && sw_io_clk_byp && io_clk_byp_en;


prim_mubi_pkg::mubi4_t all_clk_byp_ack;

assign all_clk_byp_ack = all_clks_byp_en ? prim_mubi_pkg::MuBi4True :
                                           prim_mubi_pkg::MuBi4False;

prim_mubi4_sync #(
  .ResetValue ( prim_mubi_pkg::MuBi4False )
) u_all_clk_byp_ack (
  .clk_i,
  .rst_ni,
  .mubi_i ( all_clk_byp_ack ),
  .mubi_o ( all_clk_byp_ack_o )
);

prim_mubi_pkg::mubi4_t io_clk_byp_ack;

assign io_clk_byp_ack = only_io_clk_byp_en ? prim_mubi_pkg::MuBi4True :
                                             prim_mubi_pkg::MuBi4False;

prim_mubi4_sync #(
  .ResetValue ( prim_mubi_pkg::MuBi4False )
) u_io_clk_byp_ack (
  .clk_i,
  .rst_ni,
  .mubi_i ( io_clk_byp_ack ),
  .mubi_o ( io_clk_byp_ack_o )
);




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
