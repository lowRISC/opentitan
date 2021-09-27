// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for prim_alert_sender and prim_alert_receiver pair.
//
// This direct test has five test sequences:
// 1). Alert request sequence.
// 2). Alert test sequence.
// 3). Ping request sequence.
// 4). `Ack_p/n` integrity check sequence.
// 5). `Ping_p/n` integrity check sequence.
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

  // Minimal cycles to wait between each sequence.
  // The main concern here is the minimal wait cycles between each handshake.
  localparam int  MinHandshakeWait = 2 + WaitCycle;

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
    // TODO: randomly trigger this
    .init_trig_i(lc_ctrl_pkg::Off),
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

  // `Alert`, `Ack`, and `Ping` are all differential signal pairs with postfix `_p` and `_n`.
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

  // Check `alert`, `ack`, and `ping` differential pairs with given alert_handshake stage and
  // expected ping value.
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

  // Verify the alert handshake protocol with the following pattern:
  // 1). alert_p = 1, alert_n = 0;
  // 2). ack_p = 1, ack_n = 0;
  // 3). ack_p = 0, ack_n = 1;
  // 4). alert_p = 0, alert_n = 1;
  // There is a fixed cycles of delay between each sequence depending on if the alert is sync or
  // async mode.
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

    // Wait for initialization sequence to end
    // This should take no more than 20 cycles
    // if the sender / receiver clocks are on
    // the same clock domain.
    main_clk.wait_clks(20);

    // Sequence 1). Alert request sequence.
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
    $display("Alert request sequence finished!");

    // Sequence 2). Alert test sequence.
    main_clk.wait_clks($urandom_range(MinHandshakeWait, 10));
    alert_test = 1;
    fork : isolation_fork
      begin: isolation_fork
        fork
          begin
            main_clk.wait_clks(1);
            alert_test = 0;
            check_alert_handshake(.exp_ping_value(0));
            // wait random clocks to ensure alert_ack is not set after alert handshake finishes.
            main_clk.wait_clks($urandom_range(10, 20));
          end
          forever begin
            main_clk.wait_clks(1);
            if (alert_ack == 1) begin
              $error("Alert ack should not set high during alert_test sequence!");
              error = 1;
            end
          end
        join_any
        disable fork;
      end
    join
    $display("Alert test sequence finished!");

    // Sequence 3) Ping request sequence.
    // Loop the ping request twice to cover the alert_rx.ping_p/n toggle coverage.
    for (int i = 0; i < 2; i++) begin
      // Ping is level triggered, so the two exp_ping value should be 1 and 0.
      automatic bit exp_ping = (i == 0);
      main_clk.wait_clks($urandom_range(MinHandshakeWait, 10));
      ping_req = 1;
      fork
        begin
          main_clk.wait_clks(1);
          check_diff_pair(exp_ping, PingPair);
          main_clk.wait_clks(WaitCycle);
          check_alert_handshake(.exp_ping_value(exp_ping));
        end
        begin
          wait (ping_ok == 1);
          ping_req = 0;
        end
      join
      $display($sformatf("Ping request sequence[%0d] finished!", i));
    end

    // Sequence 4) `Ack_p/n` integrity check sequence.
    // Note that alert_tx signal interigy errors are verified in alert_handler testbench.
    main_clk.wait_clks($urandom_range(MinHandshakeWait, 10));
    alert_req = 1;

    $assertoff(0, prim_alert_tb.i_alert_receiver.AckDiffOk_A);
    force i_alert_receiver.alert_rx_o.ack_p = 0;
    wait (integ_fail == 1);
    alert_req = 0;
    release i_alert_receiver.alert_rx_o.ack_p;

    // Wait until async or sync signal propogate from alert to ack.
    main_clk.wait_clks(WaitCycle);
    $asserton(0, prim_alert_tb.i_alert_receiver.AckDiffOk_A);
    $display("Ack signal integrity error sequence finished!");

    // Sequence 5) `Ping_p/n` integrity check sequence.
    // Disable the assertion at least two clock cycles before sending the ping request, because the
    // `PingDiffOk_A` assertion has ##2 delay.
    $assertoff(2, prim_alert_tb.i_alert_receiver.PingDiffOk_A);
    main_clk.wait_clks($urandom_range(MinHandshakeWait, 10));
    ping_req = 1;

    force i_alert_receiver.alert_rx_o.ping_n = 1;
    wait (integ_fail == 1);
    ping_req = 0;
    release i_alert_receiver.alert_rx_o.ping_p;

    // Ping is the first signal of the handshake, so we can directly turn on the assertion once the
    // forced ping signal is released.
    $asserton(0, prim_alert_tb.i_alert_receiver.PingDiffOk_A);
    $display("Ping signal integrity error sequence finished!");

    dv_test_status_pkg::dv_test_status(.passed(!error));
    $finish();
  end
endmodule
