// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package ast_wrapper_pkg;

  parameter int NumAlerts      = top_pkg::NUM_AST_ALERTS;
  parameter int NumIoRails     = top_pkg::NUM_IO_RAILS;
  parameter int EntropyStreams = top_pkg::ENTROPY_STREAM;
  parameter int AdcChannels    = top_pkg::ADC_CHANNELS;
  parameter int AdcDataWidth   = top_pkg::ADC_DATAW;
  parameter int UsbCalibWidth  = 16;

  // The following structs should eventually be relocted to other modules
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

  typedef struct packed {
    logic [NumAlerts-1:0] alerts_p;
    logic [NumAlerts-1:0] alerts_n;
  } ast_alert_req_t;

  typedef struct packed {
    logic [NumAlerts-1:0] alerts_ack;
    logic [NumAlerts-1:0] alerts_trig;
  } ast_alert_rsp_t;

  typedef struct packed {
    logic [NumIoRails-1:0] io_pok;
  } ast_status_t;

  // Ack mode enumerations
  typedef enum logic {
    ImmAck = 0,
    SwAck  = 1
  } ast_ack_mode_e;

  parameter ast_alert_req_t AST_ALERT_REQ_DEFAULT = '{
    alerts_p: '0,
    alerts_n: {NumAlerts{1'b1}}
  };

  typedef struct packed {
    logic flash_bist_enable;
    logic flash_power_down_h;
    logic flash_power_ready_h;
  } ast_eflash_t;

endpackage // ast_wrapper_pkg
