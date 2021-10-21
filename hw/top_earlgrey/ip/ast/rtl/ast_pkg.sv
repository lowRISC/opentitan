// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: ast_pkg
// *Module Description: AST Package
//############################################################################
`ifdef __AST_PKG_SV
`else
`define __AST_PKG_SV

package ast_pkg;

  // Alerts
  parameter int NumAlerts  = 13;
  parameter int NumIoRails = 2;
  parameter int AsSel      = 0;
  parameter int CgSel      = 1;
  parameter int GdSel      = 2;
  parameter int TsHiSel    = 3;
  parameter int TsLoSel    = 4;
  parameter int FlaSel     = 5;
  parameter int OtpSel     = 6;
  parameter int Ot0Sel     = 7;
  parameter int Ot1Sel     = 8;
  parameter int Ot2Sel     = 9;
  parameter int Ot3Sel     = 10;
  parameter int Ot4Sel     = 11;
  parameter int Ot5Sel     = 12;
  //
  parameter int EntropyStreams  = 4;
  parameter int AdcChannels     = 2;
  parameter int AdcDataWidth    = 10;
  parameter int UsbCalibWidth   = 16;
  parameter int Ast2PadOutWidth = 9;
  parameter int Pad2AstInWidth  = 7;

  // These LFSR parameters have been generated with
  // $ ./util/design/gen-lfsr-seed.py --width 64 --seed 691876113 --prefix ""
  parameter int LfsrWidth = 64;
  typedef logic [LfsrWidth-1:0] lfsr_seed_t;
  typedef logic [LfsrWidth-1:0][$clog2(LfsrWidth)-1:0] lfsr_perm_t;
  parameter lfsr_seed_t RndCnstLfsrSeedDefault = 64'h22d326255bd24320;
  parameter lfsr_perm_t RndCnstLfsrPermDefault = {
    128'h16108c9f9008aa37e5118d1ec1df64a7,
    256'h24f3f1b73537f42d38383ee8f897286df81d49ab54b6bbbb666cbd1a16c41252
  };

  // Memories Read-Write Margin Interface
  typedef struct packed {
    logic          marg_en_a;
    logic [4-1:0]  marg_a;
    logic          marg_en_b;
    logic [4-1:0]  marg_b;
  } dpm_rm_t;

  typedef struct packed {
    logic          marg_en;
    logic [4-1:0]  marg;
  } spm_rm_t;

  // ADC Interface
  typedef struct packed {
    logic [AdcChannels-1:0] channel_sel;
    logic pd;
  } adc_ast_req_t;

  typedef struct packed {
    logic [AdcDataWidth-1:0] data;
    logic data_valid;
  } adc_ast_rsp_t;

  // Analog Signal
  `ifdef ANALOGSIM
  typedef real  awire_t;
  `else
  typedef logic awire_t;
  `endif

  // Clock & Resets Interface
  typedef struct packed {
    logic clk_sys;
    logic clk_io;
    logic clk_usb;
    logic clk_aon;
  } ast_clks_t;

  typedef struct packed {
    logic aon_pok;
  } ast_rst_t;

  parameter ast_rst_t AST_RST_DEFAULT = '{
    aon_pok: 1'b1
  };

  typedef struct packed {
    logic [NumIoRails-1:0] io_pok;
  } ast_status_t;

  typedef struct packed {
    logic                  aon_pok;
    logic                  vcc_pok;
    logic                  main_pok;
    logic [NumIoRails-1:0] io_pok;
  } ast_pwst_t;

  // Alerts Interface
  typedef struct packed {
    logic        p;
    logic        n;
  } ast_dif_t;

  typedef struct packed {
    ast_dif_t [NumAlerts-1:0] alerts;
  } ast_alert_req_t;

  typedef struct packed {
    ast_dif_t [NumAlerts-1:0] alerts_ack;
    ast_dif_t [NumAlerts-1:0] alerts_trig;
  } ast_alert_rsp_t;

  // Ack mode enumerations
  typedef enum logic {
    ImmAck = 0,
    SwAck  = 1
  } ast_ack_mode_e;

  // Clocks Oschillator Bypass
  typedef struct packed {
    logic     usb;
    logic     sys;
    logic     io;
    logic     aon;
  } clks_osc_byp_t;

endpackage  // of ast_pkg
`endif  // of __AST_PKG_SV
