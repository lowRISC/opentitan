// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface esc_if(input clk, input rst_n);
  import uvm_pkg::*;

  wire prim_esc_pkg::esc_tx_t     esc_tx;
  wire prim_esc_pkg::esc_rx_t     esc_rx;

  prim_esc_pkg::esc_tx_t     esc_tx_int;   // internal esc_tx
  prim_esc_pkg::esc_rx_t     esc_rx_int;   // internal esc_rx

  bit                     is_async, is_active;
  dv_utils_pkg::if_mode_e if_mode;
  clk_rst_if              clk_rst_async_if(.clk(async_clk), .rst_n(rst_n));

  clocking sender_cb @(posedge async_clk);
    output esc_tx_int;
    input  esc_rx;
  endclocking

  clocking receiver_cb @(posedge async_clk);
    input  esc_tx;
    output esc_rx_int;
  endclocking

  clocking monitor_cb @(posedge clk);
    input esc_tx;
    input esc_rx;
  endclocking

  assign esc_tx = (if_mode == dv_utils_pkg::Host && is_active)   ? esc_tx_int   : 'z;
  assign esc_rx = (if_mode == dv_utils_pkg::Device && is_active) ? esc_rx_int   : 'z;

  task automatic wait_esc_complete();
    while (esc_tx.esc_p === 1'b1 && esc_tx.esc_n === 1'b0) @(monitor_cb);
  endtask : wait_esc_complete

  // this task wait for esc_ping request.
  // esc_ping request is detected by toggling "esc_p/n" for one cycle:
  // one clock cycle set (esc_p = 1, esc_n = 0) and one clock cycle reset (esc_p = 0, esc_n = 1)
  task automatic wait_esc_ping();
    int cycle_cnt;
    do begin
      wait(rst_n === 1'b1);
      cycle_cnt = 0;
      // wait for esc_p and no sig_int_err
      while (esc_tx.esc_p === 1'b0 || esc_tx.esc_p === esc_tx.esc_n) @(monitor_cb);
      // count how many cycles the esc_p/n has lasted
      while (esc_tx.esc_p === 1'b1 && esc_tx.esc_n === 1'b0) begin
        @(monitor_cb);
        cycle_cnt++;
      end
    // if cycle is larger than one, then it is a real esc signal instead of ping request
    // so keep blocking until found the ping request
    end while (cycle_cnt > 1 || rst_n != 1'b1);
  endtask : wait_esc_ping
endinterface
