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

parameter int unsigned NumIoRails = 2;
// Alerts
parameter int unsigned NumAlerts  = 11;
parameter int unsigned AsSel      = 0;
parameter int unsigned CgSel      = 1;
parameter int unsigned GdSel      = 2;
parameter int unsigned TsHiSel    = 3;
parameter int unsigned TsLoSel    = 4;
parameter int unsigned Ot0Sel     = 5;
parameter int unsigned Ot1Sel     = 6;
parameter int unsigned Ot2Sel     = 7;
parameter int unsigned Ot3Sel     = 8;
parameter int unsigned Ot4Sel     = 9;
parameter int unsigned Ot5Sel     = 10;
//
parameter int unsigned Lc2HcTrCyc = 102;  // ((99+1)+(3+1))x5 = 520 us
parameter int unsigned Hc2LcTrCyc = 38;   // ((35+1)+(3+1))x5 = 200 us
//
parameter int unsigned EntropyStreams   = 4;
parameter int unsigned AdcChannels      = 2;
parameter int unsigned AdcDataWidth     = 10;
parameter int unsigned UsbCalibWidth    = 20;
parameter int unsigned Ast2PadOutWidth  = 9;
parameter int unsigned Pad2AstInWidth   = 9;
//
// AstRegsNum is the number of AST registers programmed during initialization. It includes
// the register that marks the finalization of init, which asserts the ast_init_done_o.
// The offset of this register is represented with the AstLastRegOffset parameter.
parameter int unsigned AstRegsNum       = 39;
parameter int unsigned AstLastRegOffset = (AstRegsNum-1)*4;

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

typedef enum logic [4-1:0] {
  ObsNon = 4'h0,  // No module observed (disable)
  ObsAst = 4'h1,  // Observe AST
  ObsFla = 4'h2,  // Observe FLASH
  ObsOtp = 4'h3,  // Observe OTP
  ObsOt0 = 4'h4,  // Observe OT0
  ObsOt1 = 4'h5,  // Observe OT1
  ObsOt2 = 4'h6,  // Observe OT2
  ObsOt3 = 4'h7,  // Observe OT3
  ObsRs0 = 4'h8,  // RESERVED
  ObsRs1 = 4'h9,  // RESERVED
  ObsRs2 = 4'hA,  // RESERVED
  ObsRs3 = 4'hB,  // RESERVED
  ObsRs4 = 4'hC,  // RESERVED
  ObsRs5 = 4'hD,  // RESERVED
  ObsRs6 = 4'hE,  // RESERVED
  ObsRs7 = 4'hF   // RESERVED
} ast_omdl_e;

typedef struct packed {
  logic [4-1:0]          obgsl;
  ast_omdl_e             obmsl;
  prim_mubi_pkg::mubi4_t obmen;
} ast_obs_ctrl_t;

endpackage  // of ast_pkg
`endif  // of __AST_PKG_SV
