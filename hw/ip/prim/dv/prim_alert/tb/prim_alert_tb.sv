// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for prim_alert_sender and prim_alert_receiver pair.
//
// This direct test has four test sequences:
// 1). Alert request sequence:
//     Send an alert request by driving `alert_req` pin to 1.
//     Check `alert_ack` signal is set and check alert handshake is completed.
//     If the alert is fatal, the alert should continuous firing until a reset is issued. To check
//     this property, the sequence waits a random number of clock cycles, then check if alert is
//     still firing.
// 2). Ping request sequence:
//     Send a ping request by driving `ping_req` pin to 1.
//     Check `ping_ok` signal is set and ping handshake is completed.
// 3). Ack_p/n integrity check sequence:
//     Send an alert reqeust by driving `alert_req` pin to 1.
//     Force `ack_p` signal to stay low to trigger an integrity error.
//     Check if `integ_fail_o` output is set to 1.
// 4). Ping_p/n integrity check sequence:
//     Send a ping request by driving `ping_req` to 1.
//     Because ping request is level triggered and sequence 2) has driven ping request once, in
//     this sequence, ping request will reset `ping_p` signal to 0, and set `ping_n` to 1.
//     Then force `ping_n` signal to stay low to trigger an integrity error.
//     Check if `integ_fail_o` output is set to 1.
//
// This direct sequence did not drive `ack_p/n` to trigger integrity error because this sequence is
// covered in alert_handler IP level test.

module prim_alert_tb;

  //////////////////////////////////////////////////////
  // config
  //////////////////////////////////////////////////////

  // this can be overriden on the command line
  `ifdef IS_SYNC
    localparam bit IsAsync = 0;
  `else
    localparam bit IsAsync = 1;
  `endif
  `ifdef IS_FATAL
    localparam bit IsFatal = 1;
  `else
    localparam bit IsFatal = 0;
  `endif

  localparam time ClkPeriod  = 10000;
  localparam int  WaitCycle = IsAsync ? 3 : 1;

  typedef enum bit [3:0]{
    AlertSet,
    AlertAckSet,
    AlertReset,
    AlertAckReset
  } alert_handshake_e;

  typedef enum bit[1:0] {
    PingPair,
    AlertPair,
    AckPair
  } alert_signal_pair_e;

  //////////////////////////////////////////////////////
  // Clock and Reset
  //////////////////////////////////////////////////////

  wire clk, rst_n;

  clk_rst_if main_clk (
    .clk,
    .rst_n
  );

  //////////////////////////////////////////////////////
  // DUTs
  //////////////////////////////////////////////////////

  logic alert_test, alert_req, alert_ack, alert_state;
  logic ping_req, ping_ok, integ_fail, alert_o;
  prim_alert_pkg::alert_rx_t alert_rx;
  prim_alert_pkg::alert_tx_t alert_tx;

  prim_alert_sender #(
    .AsyncOn(IsAsync),
    .IsFatal(IsFatal)
  ) i_alert_sender (
    .clk_i(clk),
    .rst_ni(rst_n),
    .alert_test_i(alert_test),
    .alert_req_i(alert_req),
    .alert_ack_o(alert_ack),
    .alert_state_o(alert_state),
    .alert_rx_i(alert_rx),
    .alert_tx_o(alert_tx)
  );

  prim_alert_receiver #(
    .AsyncOn(IsAsync)
  ) i_alert_receiver (
    .clk_i(clk),
    .rst_ni(rst_n),
    .ping_req_i(ping_req),
    .ping_ok_o(ping_ok),
    .integ_fail_o(integ_fail),
    .alert_o(alert_o),
    .alert_rx_o(alert_rx),
    .alert_tx_i(alert_tx)
  );

  //////////////////////////////////////////////////////
  // Helper Functions/Tasks and Variables
  //////////////////////////////////////////////////////

  logic error = 0;

  function automatic void check_diff_pair(bit exp_p, alert_signal_pair_e signal_pair);
    bit exp_n = ~exp_p;
    bit act_p, act_n;
    string err_msg;

    case (signal_pair)
      PingPair: begin
        act_p = alert_rx.ping_p;
        act_n = alert_rx.ping_n;
        err_msg = "alert_rx.ping mismatch";
      end
      AlertPair: begin
        act_p = alert_tx.alert_p;
        act_n = alert_tx.alert_n;
        err_msg = "alert_tx.alert mismatch";
      end
      AckPair: begin
        act_p = alert_rx.ack_p;
        act_n = alert_rx.ack_n;
        err_msg = "alert_rx.ack mismatch";
      end
      default: begin
        $error($sformatf("Invalid signal_pair value %0d", signal_pair));
        error = 1;
      end
    endcase

    if (exp_p != act_p) begin
      error = 1;
      $error($sformatf("%0s: exp_p=%0d act_p=%0d", err_msg, exp_p, act_p));
    end
    if (exp_n != act_n) begin
      error = 1;
      $error($sformatf("%0s: exp_n=%0d act_n=%0d", err_msg, exp_n, act_n));
    end
  endfunction

  function automatic void check_alert_rxtx(alert_handshake_e alert_handshake, bit exp_ping);
    case (alert_handshake)
      AlertSet: begin
        check_diff_pair(1, AlertPair);
        check_diff_pair(0, AckPair);
      end
      AlertAckSet: begin
        check_diff_pair(1, AlertPair);
        check_diff_pair(1, AckPair);
      end
      AlertReset: begin
        check_diff_pair(0, AlertPair);
        check_diff_pair(1, AckPair);
      end
      AlertAckReset: begin
        check_diff_pair(0, AlertPair);
        check_diff_pair(0, AckPair);
      end
      default: begin
        $error($sformatf("Invalid alert_handshake value %0d", alert_handshake));
        error = 1;
      end
    endcase
    check_diff_pair(exp_ping, PingPair);
  endfunction

  task automatic check_alert_handshake(bit exp_ping_value);
    check_alert_rxtx(AlertSet, exp_ping_value);
    main_clk.wait_clks(WaitCycle);
    check_alert_rxtx(AlertAckSet, exp_ping_value);
    main_clk.wait_clks(WaitCycle);
    check_alert_rxtx(AlertReset, exp_ping_value);
    main_clk.wait_clks(WaitCycle);
    check_alert_rxtx(AlertAckReset, exp_ping_value);
  endtask

  //////////////////////////////////////////////////////
  // Stimuli Application / Response Checking
  //////////////////////////////////////////////////////

  initial begin: p_stimuli
    alert_test = 0;
    alert_req  = 0;
    ping_req   = 0;
    main_clk.set_period_ps(ClkPeriod);
    main_clk.set_active();
    main_clk.apply_reset();

    // Check alert request.
    main_clk.wait_clks($urandom_range(0, 10));
    alert_req = 1;
    fork
      begin
        main_clk.wait_clks(1);
        check_alert_handshake(.exp_ping_value(0));
      end
      begin
        wait (alert_ack == 1);
        alert_req = 0;
      end
    join

    // If alert is fatal, check alert will continuously fire until reset.
    if (IsFatal) begin
      main_clk.wait_clks($urandom_range(10, 1000));
      wait (alert_tx.alert_p == 0);
      wait (alert_tx.alert_p == 1);
      main_clk.wait_clks(1);
      check_alert_handshake(.exp_ping_value(0));
      main_clk.apply_reset();
    end
    $display("Alert request sequence passed!");

    // Check ping request.
    // Wait at least two cycles between each alert handshake.
    main_clk.wait_clks($urandom_range(2, 10));
    ping_req = 1;
    fork
      begin
        main_clk.wait_clks(1);
        check_diff_pair(1, PingPair);
        main_clk.wait_clks(WaitCycle);
        check_alert_handshake(.exp_ping_value(1));
      end
      begin
        wait (ping_ok == 1);
        ping_req = 0;
      end
    join
    $display("Ping request sequence passed!");

    // Check alert_rx.ack_p/n signal integrity error from the alert_receiver side.
    // Note that alert_tx signal interigy errors are verified in alert_handler testbench.
    main_clk.wait_clks($urandom_range(2, 10));
    alert_req = 1;

    $assertoff(0, prim_alert_tb.i_alert_receiver.AckDiffOk_A);
    force i_alert_receiver.alert_rx_o.ack_p = 0;
    wait (integ_fail == 1);
    alert_req = 0;
    release i_alert_receiver.alert_rx_o.ack_p;
    $display("Ack signal integrity error sequence passed!");

    // Check alert_rx.ping_p/n signal integrity error from the alert_receiver side.
    main_clk.wait_clks($urandom_range(2, 10));
    ping_req = 1;

    $assertoff(0, prim_alert_tb.i_alert_receiver.PingDiffOk_A);
    force i_alert_receiver.alert_rx_o.ping_n = 0;
    wait (integ_fail == 1);
    ping_req = 0;
    release i_alert_receiver.alert_rx_o.ping_p;
    $display("Ping signal integrity error sequence passed!");

    dv_test_status_pkg::dv_test_status(.passed(!error));
    $finish();
  end
endmodule
