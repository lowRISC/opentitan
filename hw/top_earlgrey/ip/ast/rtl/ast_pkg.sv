// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: ast_pkg
// *Module Description: AST Package
//############################################################################

`ifdef __AST_PKG
`else
`define __AST_PKG
package ast_pkg;

  parameter int NumAlerts       = top_pkg::NUM_AST_ALERTS;
  parameter int NumIoRails      = top_pkg::NUM_IO_RAILS;
  parameter int EntropyStreams  = top_pkg::ENTROPY_STREAM;
  parameter int AdcChannels     = top_pkg::ADC_CHANNELS;
  parameter int AdcDataWidth    = top_pkg::ADC_DATAW;
  parameter int UsbCalibWidth   = 16;
  parameter int Ast2PadOutWidth = 10;
  parameter int Pad2AstInWidth  = 10;

  typedef struct packed {
    logic [AdcChannels-1:0] channel_sel;
    logic pd;
  } adc_ast_req_t;

  typedef struct packed {
    logic [AdcDataWidth-1:0] data;
    logic data_valid;
  } adc_ast_rsp_t;

  typedef struct packed {
    logic aon_pok;
  } ast_rst_t;

  parameter ast_rst_t AST_RST_DEFAULT = '{
    aon_pok: 1'b1
  };

  typedef struct packed {
    logic clk_sys;
    logic clk_io;
    logic clk_usb;
    logic clk_aon;
  } ast_clks_t;

  // Alert interface
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

  typedef struct packed {
    logic [NumIoRails-1:0] io_pok;
  } ast_status_t;

  // Ack mode enumerations
  typedef enum logic {
    ImmAck = 0,
    SwAck  = 1
  } ast_ack_mode_e;

  // Read-Write Margin interface
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

`ifndef VERILATOR
// synopsys translate_off
/////////////////////////////////
// Delay Parameters from Spec
/////////////////////////////////
// POKs
parameter time VCC_POK_RDLY    = 3us;
parameter time VCC_POK_FDLY    = 500ns;
parameter time VCAON_POK_RDLY  = 3us;
parameter time VCAON_POK_FDLY  = 500ns;
parameter time VCMAIN_POK_RDLY = 3us;
parameter time VCMAIN_POK_FDLY = 500ns;
parameter time VIOA_POK_RDLY   = 3us;
parameter time VIOA_POK_FDLY   = 500ns;
parameter time VIOB_POK_RDLY   = 3us;
parameter time VIOB_POK_FDLY   = 500ns;
// Main Regulator
parameter time MPVCC_RDLY      = 5us;
parameter time MPVCC_FDLY      = 100ns;
parameter time MPPD_RDLY       = 50us;
parameter time MPPD_FDLY       = 1us;
// Clocks
parameter time SYS_EN_RDLY     = 5us;
parameter time USB_EN_RDLY     = 5us;
parameter time USB_VAL_RDLY    = 80ns;   // Reduced for simulation from 50ms
parameter time USB_VAL_FDLY    = 80ns;
parameter time IO_EN_RDLY      = 5us;
parameter time AON_EN_RDLY     = 5us;
parameter time RNG_EN_RDLY     = 5us;
// synopsys translate_on
`endif
// ADC
parameter int AdcCnvtClks      = 22;

endpackage  // of ast_pkg
`endif  // of __AST_PKG
