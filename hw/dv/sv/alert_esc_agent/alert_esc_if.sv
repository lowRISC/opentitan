// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ---------------------------------------------
// Alert interface
// ---------------------------------------------
interface alert_esc_if(input clk, input rst_n);
  wire prim_alert_pkg::alert_tx_t alert_tx;
  wire prim_alert_pkg::alert_rx_t alert_rx;
  wire prim_esc_pkg::esc_tx_t     esc_tx;
  wire prim_esc_pkg::esc_rx_t     esc_rx;
  prim_alert_pkg::alert_tx_t      alert_tx_int; // internal alert_tx
  prim_alert_pkg::alert_rx_t      alert_rx_int; // internal alert_rx
  prim_esc_pkg::esc_tx_t          esc_tx_int;   // internal esc_tx
  prim_esc_pkg::esc_rx_t          esc_rx_int;   // internal esc_rx

  wire       sender_clk;
  bit        is_async, is_alert;
  dv_utils_pkg::if_mode_e  if_mode;
  clk_rst_if clk_rst_async_if(.clk(sender_clk), .rst_n(rst_n));

  // if alert sender is async mode, the clock will be drived in alert_esc_agent,
  // if it is sync mode, will assign to dut clk here
  assign sender_clk = (is_async) ? 'z : clk ;

  clocking sender_cb @(posedge sender_clk);
    input  rst_n;
    output alert_tx_int;
    input  alert_rx;
    output esc_tx_int;
    input  esc_rx;
  endclocking

  clocking receiver_cb @(posedge clk);
    input  rst_n;
    input  alert_tx;
    output alert_rx_int;
    input  esc_tx;
    output esc_rx_int;
  endclocking

  clocking monitor_cb @(posedge clk);
    input rst_n;
    input alert_tx;
    input alert_rx;
    input esc_tx;
    input esc_rx;
  endclocking

  task automatic wait_ack_complete();
    while (alert_rx.ack_p !== 1'b0) @(monitor_cb);
  endtask : wait_ack_complete

  task automatic wait_esc_complete();
    while (esc_tx.esc_p === 1'b1 && esc_tx.esc_n === 1'b0) @(monitor_cb);
  endtask : wait_esc_complete

  assign alert_tx = (if_mode == dv_utils_pkg::Host && is_alert)    ? alert_tx_int : 'z;
  assign alert_rx = (if_mode == dv_utils_pkg::Device && is_alert)  ? alert_rx_int : 'z;
  assign esc_tx   = (if_mode == dv_utils_pkg::Host && !is_alert)   ? esc_tx_int   : 'z;
  assign esc_rx   = (if_mode == dv_utils_pkg::Device && !is_alert) ? esc_rx_int   : 'z;

endinterface: alert_esc_if
