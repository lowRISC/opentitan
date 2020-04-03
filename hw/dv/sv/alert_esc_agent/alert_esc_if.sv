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
  wire prim_esc_pkg::esc_tx_t esc_tx;
  wire prim_esc_pkg::esc_rx_t esc_rx;

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

  // alert_ping triggers upon level change
  task automatic wait_ping();
    logic ping_p_value = alert_rx.ping_p;
    while (alert_rx.ping_p === ping_p_value) begin
      ping_p_value = alert_rx.ping_p;
      @(monitor_cb);
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

  task automatic drive_alerts_high();
    sender_cb.alert_tx.alert_p <= 1'b1;
    sender_cb.alert_tx.alert_n <= 1'b1;
  endtask

  task automatic drive_alerts_low();
    sender_cb.alert_tx.alert_p <= 1'b0;
    sender_cb.alert_tx.alert_n <= 1'b0;
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

  function automatic bit get_alert_n();
    return monitor_cb.alert_tx.alert_n;
  endfunction

  function automatic bit get_alert();
    return monitor_cb.alert_tx.alert_p && !monitor_cb.alert_tx.alert_n;
  endfunction

  function automatic bit get_ping_p();
    return monitor_cb.alert_rx.ping_p;
  endfunction

  // tasks for escalator sender/receiver pairs

  task automatic wait_esc();
    while (esc_tx.esc_p === 1'b0 && esc_tx.esc_n === 1'b1) @(monitor_cb);
  endtask : wait_esc

  task automatic wait_esc_complete();
    while (esc_tx.esc_p === 1'b1 && esc_tx.esc_n === 1'b0) @(monitor_cb);
  endtask : wait_esc_complete

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

  function automatic bit get_esc();
    return monitor_cb.esc_tx.esc_p && !monitor_cb.esc_tx.esc_n;
  endfunction

  function automatic bit get_resp_p();
    return monitor_cb.esc_rx.resp_p;
  endfunction

  function automatic bit get_resp_n();
    return monitor_cb.esc_rx.resp_n;
  endfunction
endinterface: alert_esc_if
