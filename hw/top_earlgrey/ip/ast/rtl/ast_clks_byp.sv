// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: ast_clks_byp
// *Module Description: AST Clocks Bypass
//############################################################################

`include "prim_assert.sv"

module ast_clks_byp (
  input vcaon_pok_i,                        // VCAON POK
  input deep_sleep_i,                       // Deep Sleep (main regulator & switch are off)
  input clk_src_sys_en_i,                   // SYS Source Clock Enable
  input clk_osc_sys_i,                      // SYS Oscillator Clock
  input clk_osc_sys_val_i,                  // SYS Oscillator Clock Valid
  input clk_src_io_en_i,                    // IO Source Clock Enable
  input clk_osc_io_i,                       // IO Oscillator Clock
  input clk_osc_io_val_i,                   // IO Oscillator Clock Valid
  input clk_src_usb_en_i,                   // USB Source Clock Enable
  input clk_osc_usb_i,                      // USB Oscillator Clock
  input clk_osc_usb_val_i,                  // USB Oscillator Clock Valid
  input clk_osc_aon_i,                      // AON Oscillator Clock
  input clk_osc_aon_val_i,                  // AON Oscillator Clock Valid
  input clk_ast_ext_i,                      // External Clock
  input prim_mubi_pkg::mubi4_t io_clk_byp_req_i,    // External IO clock mux for OTP bootstrap
  input prim_mubi_pkg::mubi4_t all_clk_byp_req_i,   // External all clock mux override
  input prim_mubi_pkg::mubi4_t ext_freq_is_96m_i,   // External Clock Frequecy is 96MHz (else 48MHz)
  output prim_mubi_pkg::mubi4_t io_clk_byp_ack_o,   // Switch IO clock to External clock
  output prim_mubi_pkg::mubi4_t all_clk_byp_ack_o,  // Switch all clocks to External clock
  output logic clk_src_sys_o,               // SYS Source Clock
  output logic clk_src_sys_val_o,           // SYS Source Clock Valid
  output logic clk_src_io_o,                // IO Source Clock
  output logic clk_src_io_val_o,            // IO Source Clock Valid
  output prim_mubi_pkg::mubi4_t clk_src_io_48m_o,  // IO Source Clock is 48Mhz
  output logic clk_src_usb_o,               // USB Source Clock
  output logic clk_src_usb_val_o,           // USB Source Clock Valid
  output logic clk_src_aon_o,               // AON Source Clock
  output logic clk_src_aon_val_o            // AON Source Clock Valid
);

logic scan_mode_i, scan_clk_i, scan_reset_ni;

assign scan_mode_i = 1'b0;
assign scan_clk_i  = 1'b0;
assign scan_reset_ni = 1'b1;


////////////////////////////////////////
// External Clocks Generation
////////////////////////////////////////
logic clk_aon_scn, clk_aon, rst_aon_n;

assign clk_aon_scn = scan_mode_i ? scan_clk_i : clk_src_aon_o;

// Local AON clock buffer
////////////////////////////////////////
prim_clock_buf #(
  .NoFpgaBuf ( 1'b1 )
) u_clk_aon_buf (
  .clk_i ( clk_aon_scn ),
  .clk_o ( clk_aon )
);

logic vcaon_pok;  // For Spyglass waiver!!!
assign vcaon_pok = vcaon_pok_i;

assign rst_aon_n = scan_mode_i ? scan_reset_ni : vcaon_pok;

// Enable Exterbal Clocks when needed
////////////////////////////////////////
logic clk_ext_scn, clk_ext, clk_ext_en;
logic sw_clk_byp_en, all_clk_byp, io_clk_byp;

// Enable External Clock for SW Bypass
always_ff @( posedge clk_aon, negedge rst_aon_n ) begin
  if ( !rst_aon_n ) begin
    sw_clk_byp_en <= 1'b0;
  end else if ( all_clk_byp || io_clk_byp ) begin
    sw_clk_byp_en <= 1'b1;
  end
end

assign clk_ext_en = sw_clk_byp_en;
assign clk_ext_scn = scan_mode_i ? scan_clk_i : clk_ast_ext_i && clk_ext_en;

// Local EXR clock buffer
////////////////////////////////////////
prim_clock_buf #(
  .NoFpgaBuf ( 1'b1 )
) u_clk_ext_buf (
  .clk_i ( clk_ext_scn ),
  .clk_o ( clk_ext )
);

// External USB&AON clocks genaration
////////////////////////////////////////
logic clk_ext_d1ord2, clk_ext_usb_scn, ext_freq_is_96m;

prim_clock_div #(
  .Divisor( 2 )
) u_clk_ext_d1ord2 (
  .clk_i ( clk_ext ),
  .rst_ni ( rst_aon_n ),
  .step_down_req_i( !ext_freq_is_96m ),
  .step_down_ack_o ( ),
  .test_en_i ( scan_mode_i ),
  .clk_o ( clk_ext_d1ord2 )
);

assign clk_ext_usb_scn = clk_ext_d1ord2;

logic clk_ext_usb_d240, clk_ext_aon, clk_ext_aon_val;

prim_clock_div #(
  .Divisor( 240 )
) u_clk_usb_div240_div (
  .clk_i ( clk_ext_usb_scn ),
  .rst_ni ( rst_aon_n ),
  .step_down_req_i( 1'b0 ),
  .step_down_ack_o ( ),
  .test_en_i ( scan_mode_i ),
  .clk_o ( clk_ext_usb_d240 )
);

assign clk_ext_aon = clk_ext_usb_d240;
assign clk_ext_aon_val = 1'b1;  // Always ON clock


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
  .rst_ni ( rst_aon_n ),
  .d_i ( deep_sleep_i ),
  .q_o ( deep_sleep )
);

assign deep_sleep_n = !deep_sleep;

// SYS External Clock Enable
////////////////////////////////////////
logic clk_ext_sys, clk_ext_sys_en, clk_ext_sys_val;

assign clk_ext_sys_en  = deep_sleep_n && clk_src_sys_en_i;
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

assign clk_ext_io_en  = deep_sleep_n && clk_src_io_en_i;
assign clk_ext_io_val = clk_ext_io_en;

prim_clock_gating #(
  .NoFpgaGate ( 1'b1)
) u_clk_ext_io_ckgt (
  .clk_i ( clk_ext ),
  .en_i ( clk_ext_io_en ),
  .test_en_i ( scan_mode_i ),
  .clk_o ( clk_ext_io )
);

// USB External Clock Enable
////////////////////////////////////////
logic clk_ext_usb, clk_ext_usb_en, clk_ext_usb_val;

assign clk_ext_usb_en  = deep_sleep_n && clk_src_usb_en_i;
assign clk_ext_usb_val = clk_ext_usb_en;

prim_clock_gating #(
  .NoFpgaGate ( 1'b1)
) u_clk_ext_usb_ckgt (
  .clk_i ( clk_ext_usb_scn ),
  .en_i ( clk_ext_usb_en ),
  .test_en_i ( scan_mode_i ),
  .clk_o ( clk_ext_usb )
);


////////////////////////////////////////
// SW Bypass select logic
////////////////////////////////////////
// Sync to local AON clcok
prim_mubi_pkg::mubi4_t io_clk_byp_req, all_clk_byp_req;
prim_mubi_pkg::mubi4_t sw_ext_freq_is_96m;

prim_mubi4_sync #(
  .StabilityCheck ( 1 ),
  .ResetValue ( prim_mubi_pkg::MuBi4False )
) u_io_clk_byp_req (
  .clk_i ( clk_aon ),
  .rst_ni ( rst_aon_n ),
  .mubi_i ( io_clk_byp_req_i ),
  .mubi_o ( io_clk_byp_req )
);

prim_mubi4_sync #(
  .StabilityCheck ( 1 ),
  .ResetValue ( prim_mubi_pkg::MuBi4False )
) u_all_clk_byp_req (
  .clk_i ( clk_aon ),
  .rst_ni ( rst_aon_n ),
  .mubi_i ( all_clk_byp_req_i ),
  .mubi_o ( all_clk_byp_req )
);

prim_mubi4_sync #(
  .StabilityCheck ( 1 ),
  .ResetValue ( prim_mubi_pkg::MuBi4False )
) u_sw_ext_freq_sync (
  .clk_i ( clk_ext ),
  .rst_ni ( rst_aon_n ),
  .mubi_i ( ext_freq_is_96m_i ),
  .mubi_o ( sw_ext_freq_is_96m )
);

// Decode logic
logic sys_clk_byp, usb_clk_byp, aon_clk_byp;

prim_mubi4_dec u_all_byp_sel ( .mubi_i ( all_clk_byp_req ), .mubi_dec_o ( all_clk_byp ) );
prim_mubi4_dec u_sys_byp_sel ( .mubi_i ( all_clk_byp_req ), .mubi_dec_o ( sys_clk_byp ) );
prim_mubi4_dec u_io_byp_sel  ( .mubi_i ( io_clk_byp_req ),  .mubi_dec_o ( io_clk_byp ) );
prim_mubi4_dec u_usb_byp_sel ( .mubi_i ( all_clk_byp_req ), .mubi_dec_o ( usb_clk_byp ) );
prim_mubi4_dec u_aon_byp_sel ( .mubi_i ( all_clk_byp_req ), .mubi_dec_o ( aon_clk_byp ) );

// De-Glitch selects (decode "noise")
logic sw_all_clk_byp, sw_sys_clk_byp, sw_io_clk_byp, sw_usb_clk_byp, sw_aon_clk_byp;

always_ff @ ( posedge clk_src_aon_o, negedge rst_aon_n ) begin
  if ( !rst_aon_n ) begin
    sw_all_clk_byp <= 1'b0;
    sw_sys_clk_byp <= 1'b0;
    sw_io_clk_byp  <= 1'b0;
    sw_usb_clk_byp <= 1'b0;
    sw_aon_clk_byp <= 1'b0;
  end else begin
    sw_all_clk_byp <= all_clk_byp;
    sw_sys_clk_byp <= sys_clk_byp;
    sw_io_clk_byp  <= io_clk_byp;
    sw_usb_clk_byp <= usb_clk_byp;
    sw_aon_clk_byp <= aon_clk_byp;
  end
end

logic sys_clk_byp_sel, io_clk_byp_sel, usb_clk_byp_sel, aon_clk_byp_sel;

assign sys_clk_byp_sel = sw_sys_clk_byp;
assign io_clk_byp_sel  = sw_io_clk_byp || sw_all_clk_byp;
assign usb_clk_byp_sel = sw_usb_clk_byp;
assign aon_clk_byp_sel = sw_aon_clk_byp;
assign ext_freq_is_96m = prim_mubi_pkg::mubi4_test_true_strict(sw_ext_freq_is_96m);


////////////////////////////////////////
// Clocks Bypass Muxes
////////////////////////////////////////
logic sys_clk_osc_en, io_clk_osc_en, usb_clk_osc_en, aon_clk_osc_en;
logic sys_clk_byp_en, io_clk_byp_en, usb_clk_byp_en, aon_clk_byp_en;

logic rst_clk_osc_n, rst_clk_ext_n;
assign rst_clk_osc_n = vcaon_pok;
assign rst_clk_ext_n = vcaon_pok;

// SYS Clock Bypass Mux
////////////////////////////////////////
gfr_clk_mux2 u_clk_src_sys_sel (
  .clk_osc_i ( clk_osc_sys_i ),
  .clk_osc_val_i ( clk_osc_sys_val_i ),
  .rst_clk_osc_ni ( rst_clk_osc_n ),
  .clk_ext_i ( clk_ext_sys ),
  .clk_ext_val_i ( clk_ext_sys_val ),
  .rst_clk_ext_ni ( rst_clk_ext_n ),
  .ext_sel_i ( sys_clk_byp_sel ),
  .clk_osc_en_o ( sys_clk_osc_en ),
  .clk_ext_en_o ( sys_clk_byp_en ),
  .clk_val_o ( clk_src_sys_val_o ),
  .clk_o ( clk_src_sys_o )
);

// IO Clock Bypass Mux
////////////////////////////////////////
gfr_clk_mux2 u_clk_src_io_sel (
  .clk_osc_i ( clk_osc_io_i ),
  .clk_osc_val_i ( clk_osc_io_val_i ),
  .rst_clk_osc_ni ( rst_clk_osc_n ),
  .clk_ext_i ( clk_ext_io ),
  .clk_ext_val_i ( clk_ext_io_val ),
  .rst_clk_ext_ni ( rst_clk_ext_n ),
  .ext_sel_i ( io_clk_byp_sel ),
  .clk_osc_en_o ( io_clk_osc_en ),
  .clk_ext_en_o ( io_clk_byp_en ),
  .clk_val_o ( clk_src_io_val_o ),
  .clk_o ( clk_src_io_o )
);

// USB Clock Bypass Mux
////////////////////////////////////////
gfr_clk_mux2 u_clk_src_usb_sel (
  .clk_osc_i ( clk_osc_usb_i ),
  .clk_osc_val_i ( clk_osc_usb_val_i ),
  .rst_clk_osc_ni ( rst_clk_osc_n ),
  .clk_ext_i ( clk_ext_usb ),
  .clk_ext_val_i ( clk_ext_usb_val ),
  .rst_clk_ext_ni ( rst_clk_ext_n ),
  .ext_sel_i ( usb_clk_byp_sel ),
  .clk_osc_en_o ( usb_clk_osc_en ),
  .clk_ext_en_o ( usb_clk_byp_en ),
  .clk_val_o ( clk_src_usb_val_o ),
  .clk_o ( clk_src_usb_o )
);

// AON Clock Bypass Mux
////////////////////////////////////////
gfr_clk_mux2 u_clk_src_aon_sel (
  .clk_osc_i ( clk_osc_aon_i ),
  .clk_osc_val_i ( clk_osc_aon_val_i ),
  .rst_clk_osc_ni ( rst_clk_osc_n ),
  .clk_ext_i ( clk_ext_aon ),
  .clk_ext_val_i ( clk_ext_aon_val ),
  .rst_clk_ext_ni ( rst_clk_ext_n ),
  .ext_sel_i ( aon_clk_byp_sel ),
  .clk_osc_en_o ( aon_clk_osc_en ),
  .clk_ext_en_o ( aon_clk_byp_en ),
  .clk_val_o ( clk_src_aon_val_o ),
  .clk_o ( clk_src_aon_o )
);

// All Clocks Bypass Acknowledge
////////////////////////////////////////
logic all_clks_byp_en;
prim_mubi_pkg::mubi4_t all_clk_byp_ack;

assign all_clks_byp_en = sw_all_clk_byp && sys_clk_byp_en && io_clk_byp_en &&
                         usb_clk_byp_en && aon_clk_byp_en;

assign all_clk_byp_ack = all_clks_byp_en ? prim_mubi_pkg::MuBi4True :
                                           prim_mubi_pkg::MuBi4False;

prim_mubi4_sender #(
  .ResetValue ( prim_mubi_pkg::MuBi4False )
) u_all_clk_byp_ack (
  .clk_i ( clk_aon ),
  .rst_ni ( rst_aon_n ),
  .mubi_i ( all_clk_byp_ack ),
  .mubi_o ( all_clk_byp_ack_o )
);

// IO Clock Bypass Acknowledge
////////////////////////////////////////
logic only_io_clk_byp_en;
prim_mubi_pkg::mubi4_t io_clk_byp_ack;

assign only_io_clk_byp_en = sw_io_clk_byp && io_clk_byp_en;

assign io_clk_byp_ack = only_io_clk_byp_en ? prim_mubi_pkg::MuBi4True :
                                             prim_mubi_pkg::MuBi4False;

prim_mubi4_sender #(
  .ResetValue ( prim_mubi_pkg::MuBi4False )
) u_io_clk_byp_ack (
  .clk_i ( clk_aon ),
  .rst_ni ( rst_aon_n ),
  .mubi_i ( io_clk_byp_ack ),
  .mubi_o ( io_clk_byp_ack_o )
);

// IO Clock Source is 48MHz
////////////////////////////////////////
// Oscillator source is always 96MHz.
// External Bypass source is assume to
// be 96MHz until it is ebabled as 48MHz
////////////////////////////////////////
logic io_clk_byp_is_48m;
prim_mubi_pkg::mubi4_t clk_src_io_is_48m;

always_ff @ ( posedge clk_src_io_o, negedge rst_aon_n ) begin
  if ( !rst_aon_n ) begin
    io_clk_byp_is_48m <= 1'b0;
  end else begin
    io_clk_byp_is_48m <= (io_clk_byp_sel && io_clk_byp_en && !ext_freq_is_96m);
  end
end

assign clk_src_io_is_48m = io_clk_byp_is_48m ? prim_mubi_pkg::MuBi4True :  // 48MHz
                                               prim_mubi_pkg::MuBi4False;  // 96MHz

prim_mubi4_sender #(
  .ResetValue ( prim_mubi_pkg::MuBi4False )
) u_clk_src_io_48m_sync (
  .clk_i ( clk_src_io_o ),
  .rst_ni ( rst_aon_n ),
  .mubi_i ( clk_src_io_is_48m ),
  .mubi_o ( clk_src_io_48m_o )
);


/////////////////////
// Unused Signals  //
/////////////////////
logic unused_sigs;

assign unused_sigs = ^{ sys_clk_osc_en,
                        io_clk_osc_en,
                        usb_clk_osc_en,
                        aon_clk_osc_en
                      };

endmodule : ast_clks_byp
