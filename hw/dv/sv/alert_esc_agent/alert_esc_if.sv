// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ---------------------------------------------
// Alert interface
// ---------------------------------------------
interface alert_esc_if(input clk, input rst_n);
  import uvm_pkg::*;

  wire prim_alert_pkg::alert_tx_t alert_tx;
  wire prim_alert_pkg::alert_rx_t alert_rx;
  wire prim_esc_pkg::esc_tx_t     esc_tx;
  wire prim_esc_pkg::esc_rx_t     esc_rx;

  prim_alert_pkg::alert_tx_t alert_tx_sync_dly2; // sync alert_tx 2 clk cycle delay flop
  prim_alert_pkg::alert_tx_t alert_tx_sync_dly1; // sync alert_tx 1 clk cycle delay flop
  // final alert_tx value depends if on async and host mode
  prim_alert_pkg::alert_tx_t alert_tx_final;

  prim_alert_pkg::alert_rx_t alert_rx_sync_dly2; // sync alert_rx 2 clk cycle delay flop
  prim_alert_pkg::alert_rx_t alert_rx_sync_dly1; // sync alert_rx 1 clk cycle delay flop
  // final alert_rx value depends if on async and device mode
  prim_alert_pkg::alert_rx_t alert_rx_final;

  prim_alert_pkg::alert_tx_t alert_tx_int; // internal alert_tx
  prim_alert_pkg::alert_rx_t alert_rx_int; // internal alert_rx
  prim_esc_pkg::esc_tx_t     esc_tx_int;   // internal esc_tx
  prim_esc_pkg::esc_rx_t     esc_rx_int;   // internal esc_rx

  wire                    async_clk;
  bit                     is_async, is_alert, is_active;
  dv_utils_pkg::if_mode_e if_mode;
  clk_rst_if              clk_rst_async_if(.clk(async_clk), .rst_n(rst_n));

  logic ping_pq;
  always_ff @(posedge clk or negedge rst_n) begin
    ping_pq <= alert_rx.ping_p;
  end

  // Code ping_request and alert_active so they will not assert for unknown values.
  logic ping_request;
  always_comb ping_request = (alert_rx.ping_p ^ ping_pq) === 1'b1;

  logic alert_active;
  always_comb alert_active = (alert_tx.alert_p ^ alert_tx.alert_n) === 1'b1 && alert_tx.alert_p;

  logic alert_inactive;
  always_comb alert_inactive = (alert_tx.alert_p ^ alert_tx.alert_n) === 1'b1 && alert_tx.alert_n;

  typedef enum logic [1:0] { IdleSt, PingSt, AlertSt } state_e;
  state_e state_d, state_q;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      state_q <= IdleSt;
    end else begin
      state_q <= state_d;
    end
  end

  always_comb begin
    state_d = state_q;
    unique case (state_q)
      IdleSt: if (ping_request) state_d = PingSt;
      PingSt: if (alert_active) state_d = AlertSt;
      AlertSt: if (alert_inactive) state_d = IdleSt;
      default: state_d = IdleSt;
    endcase // unique case (state_q)
  end

  logic ping_pending;
  always_comb ping_pending = state_q != IdleSt;

  // if alert sender is async mode, the clock will be driven in alert_esc_agent,
  // if it is sync mode, will assign to dut clk here
  assign async_clk = (is_async) ? 'z : clk ;

  // async interface for alert_tx has two_clock cycles delay
  // ICEBOX(#3275): this is not needed once the CDC module is implemented
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      alert_tx_sync_dly2 <= {2'b01};
      alert_tx_sync_dly1 <= {2'b01};
      alert_rx_sync_dly2 <= {4'b0101};
      alert_rx_sync_dly1 <= {4'b0101};
    end else begin
      alert_tx_sync_dly2 <= alert_tx_sync_dly1;
      alert_tx_sync_dly1 <= alert_tx;
      alert_rx_sync_dly2 <= alert_rx_sync_dly1;
      alert_rx_sync_dly1 <= alert_rx;
    end
  end
  assign alert_tx_final = (is_async && (if_mode == dv_utils_pkg::Host)) ?
                          alert_tx_sync_dly2 : alert_tx;
  assign alert_rx_final = (is_async && (if_mode == dv_utils_pkg::Device)) ?
                          alert_rx_sync_dly2 : alert_rx;

  clocking sender_cb @(posedge async_clk);
    input  rst_n;
    output alert_tx_int;
    input  alert_rx;
    output esc_tx_int;
    input  esc_rx;
  endclocking

  clocking receiver_cb @(posedge async_clk);
    input  rst_n;
    input  alert_tx;
    output alert_rx_int;
    input  esc_tx;
    output esc_rx_int;
  endclocking

  clocking monitor_cb @(posedge clk);
    input rst_n;
    input alert_tx_final;
    input alert_rx_final;
    input esc_tx;
    input esc_rx;
  endclocking

  assign alert_tx = (if_mode == dv_utils_pkg::Host && is_alert && is_active)   ? alert_tx_int : 'z;
  assign alert_rx = (if_mode == dv_utils_pkg::Device && is_alert && is_active) ? alert_rx_int : 'z;
  assign esc_tx = (if_mode == dv_utils_pkg::Host && !is_alert && is_active)   ? esc_tx_int   : 'z;
  assign esc_rx = (if_mode == dv_utils_pkg::Device && !is_alert && is_active) ? esc_rx_int   : 'z;

  task automatic wait_ack_complete();
    while (alert_tx_final.alert_p === 1'b1) @(monitor_cb);
    while (alert_rx_final.ack_p === 1'b1)   @(monitor_cb);
  endtask : wait_ack_complete

  task automatic wait_esc_complete();
    while (esc_tx.esc_p === 1'b1 && esc_tx.esc_n === 1'b0) @(monitor_cb);
  endtask : wait_esc_complete

  function automatic bit get_alert();
    if (alert_tx_final.alert_p === 1'b1 && ping_pending) begin
      `uvm_info("alert_esc_if::get_alert", $sformatf(
                "This alert is a ping response: alert_p:%b, alert_n:%b, ping_pending:%p",
                alert_tx_final.alert_p, alert_tx_final.alert_n, ping_pending),
                UVM_MEDIUM)
    end
    get_alert = (alert_tx_final.alert_p === 1'b1 && alert_tx_final.alert_n === 1'b0 &&
                 ! ping_pending);
  endfunction : get_alert

  function automatic bit is_alert_handshaking();
    return alert_tx_final.alert_p === 1'b1 || alert_rx_final.ack_p === 1'b1;
  endfunction : is_alert_handshaking

  // this task wait for alert_ping request.
  // alert_ping request is detected by level triggered "alert_rx.ping_p/n" signals pairs
  // and no sig_int_err
  task automatic wait_alert_ping();
    do begin
      logic ping_p;
      wait(rst_n === 1'b1);
      ping_p = alert_rx_final.ping_p;
      wait(alert_rx_final.ping_p !== ping_p && alert_rx_final.ping_p === !alert_rx_final.ping_n);
    end while (rst_n != 1'b1);
  endtask : wait_alert_ping

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

  logic alert_sva_active;
  always_comb alert_sva_active = is_alert && rst_n;

  // Check the differential alert signals have no unknown values.
  `ASSERT_KNOWN(PingKnown_A, alert_rx.ping_p ^ alert_rx.ping_n, clk, !alert_sva_active)
  `ASSERT_KNOWN(AckKnown_A, alert_rx.ack_p ^ alert_rx.ack_n, clk, !alert_sva_active)
  `ASSERT_KNOWN(AlertKnown_A, alert_tx.alert_p ^ alert_tx.alert_n, clk, !alert_sva_active)
endinterface: alert_esc_if
