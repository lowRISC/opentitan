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

  parameter int NumAlerts       = top_pkg::NUM_AST_ALERTS;
  parameter int NumIoRails      = top_pkg::NUM_IO_RAILS;
  parameter int EntropyStreams  = top_pkg::ENTROPY_STREAM;
  parameter int AdcChannels     = top_pkg::ADC_CHANNELS;
  parameter int AdcDataWidth    = top_pkg::ADC_DATAW;
  parameter int UsbCalibWidth   = 16;
  parameter int Ast2PadOutWidth = 10;
  parameter int Pad2AstInWidth  = 10;

  // Memories Read-Write Margin Interface
  typedef struct packed {
    logic       marg_en_a;
    logic [3:0] marg_a;
    logic       marg_en_b;
    logic [3:0] marg_b;
  } dpm_rm_t;

  typedef struct packed {
    logic       marg_en;
    logic [3:0] marg;
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


endpackage  // of ast_pkg
`endif  // of __AST_PKG_SV
