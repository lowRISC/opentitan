// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface ast_adc_if #(
  parameter int AdcChannels  = 2,
  parameter int AdcDataWidth = 10
  )(
  input clk_i,  // Clock
  input rst_ni  // Reset active low
  );

  // AST ADC interface types
  typedef struct packed {
    logic [AdcChannels-1:0] channel_sel;
    logic pd;
  } req_t;

  typedef struct packed {
    logic [AdcDataWidth-1:0] data;
    logic data_valid;
  } rsp_t;

  // interface pins
  req_t adc_o; // Request output from ADC_CTRL
  rsp_t adc_i; // Response input to ADC_CTRL

  // debug signals

  // Messages from driver and monitor

  // Make these static for easy wave dumping
  bit [7:0][39:0] driver_msg  = "";

  // Messages from monitor
  bit [7:0][39:0] monitor_msg  = "";

  // clocking blocks

  // Driver clocking block
  clocking driver_cb @(posedge clk_i);
    input  rst_ni;
    input  adc_o;
    output adc_i;
  endclocking

  // Monitor clocking block
  clocking monitor_cb @(posedge clk_i);
    input rst_ni;
    input adc_o;
    input adc_i;
  endclocking

  // Tasks and functions
  // Send a driver message by setting driver_msg string
  function automatic void send_driver_msg(string msg);
    driver_msg = msg;
  endfunction

  // Send a monitor message by setting monitor_msg string
  function automatic void send_monitor_msg(string msg);
    monitor_msg = msg;
  endfunction

endinterface
