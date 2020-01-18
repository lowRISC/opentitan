// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ---------------------------------------------
// Alert interface
// ---------------------------------------------
interface alert_esc_if(input clk, input rst_n);
  wire prim_pkg::alert_tx_t alert_tx;
  wire prim_pkg::alert_rx_t alert_rx;
  wire prim_pkg::esc_tx_t esc_tx;
  wire prim_pkg::esc_rx_t esc_rx;

  clocking sender_cb @(posedge clk);
    input  rst_n;
    output alert_tx;
    input  alert_rx;
    output esc_tx;
    input  esc_rx;
  endclocking

  clocking receiver_cb @(posedge clk);
    input  rst_n;
    input  alert_tx;
    output alert_rx;
    input  esc_tx;
    output esc_rx;
  endclocking

  clocking monitor_cb @(posedge clk);
    input rst_n;
    input alert_tx;
    input alert_rx;
    input esc_tx;
    input esc_rx;
  endclocking

  // tasks for alert sender/receiver pairs

  task automatic wait_alert();
    while (alert_tx.alert_p !== 1'b1) @(monitor_cb);
  endtask : wait_alert

  task automatic wait_alert_complete();
    while (alert_tx.alert_p !== 1'b0) @(monitor_cb);
  endtask : wait_alert_complete

  task automatic wait_ping();
    logic ping_p_value = 0;
    while (alert_rx.ping_p === ping_p_value) begin
      @(monitor_cb);
      ping_p_value = alert_rx.ping_p;
    end
  endtask : wait_ping

  task automatic wait_ack();
    while (alert_rx.ack_p !== 1'b1) @(monitor_cb);
  endtask : wait_ack

  task automatic wait_ack_complete();
    while (alert_rx.ack_p !== 1'b0) @(monitor_cb);
  endtask : wait_ack_complete

  task automatic set_alert();
    sender_cb.alert_tx.alert_p <= 1'b1;
    sender_cb.alert_tx.alert_n <= 1'b0;
  endtask

  task automatic reset_alert();
    sender_cb.alert_tx.alert_p <= 1'b0;
    sender_cb.alert_tx.alert_n <= 1'b1;
  endtask

  task automatic set_ack();
    receiver_cb.alert_rx.ack_p <= 1'b1;
    receiver_cb.alert_rx.ack_n <= 1'b0;
  endtask

  task automatic reset_ack();
    receiver_cb.alert_rx.ack_p <= 1'b0;
    receiver_cb.alert_rx.ack_n <= 1'b1;
  endtask

  task automatic set_ping();
    receiver_cb.alert_rx.ping_p <= !alert_rx.ping_p;
    receiver_cb.alert_rx.ping_n <= !alert_rx.ping_n;
  endtask

  task automatic reset_ping();
    receiver_cb.alert_rx.ping_p <= 1'b0;
    receiver_cb.alert_rx.ping_n <= 1'b1;
  endtask

  function automatic bit get_ack_p();
    return monitor_cb.alert_rx.ack_p;
  endfunction

  function automatic bit get_alert_p();
    return monitor_cb.alert_tx.alert_p;
  endfunction

  function automatic bit get_ping_p();
    return monitor_cb.alert_rx.ping_p;
  endfunction

  // tasks for escalator sender/receiver pairs

  task automatic wait_esc();
    while (esc_tx.esc_p !== 1'b1) @(monitor_cb);
  endtask : wait_esc

  task automatic reset_esc();
    sender_cb.esc_tx.esc_p <= 1'b0;
    sender_cb.esc_tx.esc_n <= 1'b1;
  endtask

  task automatic set_resp();
    receiver_cb.esc_rx.resp_p <= 1'b1;
    receiver_cb.esc_rx.resp_n <= 1'b0;
  endtask

  task automatic reset_resp();
    receiver_cb.esc_rx.resp_p <= 1'b0;
    receiver_cb.esc_rx.resp_n <= 1'b1;
  endtask

  function automatic bit get_esc_p();
    return monitor_cb.esc_tx.esc_p;
  endfunction

  function automatic bit get_resp_p();
    return monitor_cb.esc_rx.resp_p;
  endfunction

endinterface: alert_esc_if
