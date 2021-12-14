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

  import dv_utils_pkg::*;

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

  localparam time ClkPeriod  = 10_000;
  localparam int  WaitCycle = IsAsync ? 3 : 1;

  // Minimal cycles to wait between each sequence.
  // The main concern here is the minimal wait cycles between each handshake.
  localparam int MinHandshakeWait = 2 + WaitCycle;

  // Clock cycles for alert init handshake to finish.
  localparam int WaitAlertInitDone = 30;

  // Clock cycles for alert or ping handshake to finish.
  // Wait enough cycles to ensure assertions from design are checked.
  localparam int WaitAlertHandshakeDone = 20;

  uint default_spinwait_timeout_ns = 100_000;

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
  prim_mubi_pkg::mubi4_t     init_trig = prim_mubi_pkg::MuBi4False;
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
    .init_trig_i(init_trig),
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
    if ($urandom_range(0, 1)) begin
      main_clk.wait_clks($urandom_range(0, WaitAlertInitDone));
      if ($urandom_range(0, 1)) begin
        init_trig = prim_mubi_pkg::MuBi4True;
        main_clk.wait_clks(1);
        init_trig = prim_mubi_pkg::MuBi4False;
      end else begin
        main_clk.apply_reset();
      end
    end
    main_clk.wait_clks(WaitAlertInitDone);
    $display("Init sequence finish");

    // Sequence 1). Alert request sequence.
    for (int num_trans = 1; num_trans <= 10; num_trans++) begin
      fork
        begin
          main_clk.wait_clks($urandom_range(MinHandshakeWait, 10));
          alert_req = 1;
          `DV_SPINWAIT(wait (alert_ack == 1);, , , "Wait for alert_ack timeout");
          alert_req = 0;
          main_clk.wait_clks(WaitAlertHandshakeDone);
        end
        begin
          if ($urandom_range(0, 1)) begin
            main_clk.wait_clks($urandom_range(MinHandshakeWait, 10));
            init_trig = prim_mubi_pkg::MuBi4True;
            main_clk.wait_clks($urandom_range(1, 10));
            init_trig = prim_mubi_pkg::MuBi4False;
            main_clk.wait_clks(WaitAlertInitDone);
          end
        end
      join

      if (IsFatal) begin
        // For fatal alert, ensure alert keeps firing until reset.
        // If only alert_init is triggered, alert_sender side still expect fatal alert to fire.
        // This check is valid if the alert is fatal, and alert is requested before init request.
        main_clk.wait_clks($urandom_range(10, 100));
        `DV_SPINWAIT(wait (alert_tx.alert_p == 0);, , , "Wait for alert_p goes low");
        `DV_SPINWAIT(wait (alert_tx.alert_p == 1);, , , "Wait for alert_p goes high");
        main_clk.wait_clks(WaitAlertHandshakeDone);
        main_clk.apply_reset();
        main_clk.wait_clks(WaitAlertInitDone);
      end
      $display("[prim_alert_seq] Alert request sequence %0d/10 finished!", num_trans);
    end

    // Sequence 2). Alert test sequence.
    main_clk.wait_clks($urandom_range(MinHandshakeWait, 10));
    alert_test = 1;
    main_clk.wait_clks(1);
    alert_test = 0;
    repeat ($urandom_range(10, 20)) begin
      if (alert_ack == 1) begin
        $error("Alert ack should not set high during alert_test sequence!");
        error = 1;
      end
      main_clk.wait_clks(1);
    end
    $display("[prim_alert_seq] Alert test sequence finished!");

    // Sequence 3) Ping request sequence.
    for (int num_trans = 0; num_trans < 10; num_trans++) begin
      fork
        begin
          main_clk.wait_clks($urandom_range(MinHandshakeWait, 10));
          ping_req = 1;
          `DV_SPINWAIT(wait (ping_ok == 1);, , , "Wait for ping_ok timeout");
          ping_req = 0;
          main_clk.wait_clks(WaitCycle + WaitAlertHandshakeDone);
        end
        begin
          if ($urandom_range(0, 1)) begin
            main_clk.wait_clks($urandom_range(1, WaitAlertHandshakeDone + 10));
            init_trig = prim_mubi_pkg::MuBi4True;
            main_clk.wait_clks($urandom_range(0, 10));
            init_trig = prim_mubi_pkg::MuBi4False;
            main_clk.wait_clks(WaitAlertInitDone);
          end
        end
      join
      $display($sformatf("[prim_alert_seq] Ping request sequence[%0d] finished!", num_trans));
    end

    // Sequence 4) `Ack_p/n` integrity check sequence.
    // Note that alert_tx signal interigy errors are verified in alert_handler testbench.
    main_clk.wait_clks($urandom_range(MinHandshakeWait, 10));
    alert_req = 1;

    $assertoff(0, prim_alert_tb.i_alert_receiver.AckDiffOk_A);
    force i_alert_receiver.alert_rx_o.ack_p = 0;
    `DV_SPINWAIT(wait (integ_fail == 1);, , , "Wait for integrity error timeout");
    alert_req = 0;
    release i_alert_receiver.alert_rx_o.ack_p;

    // Wait until async or sync signal propogate from alert to ack.
    main_clk.wait_clks(WaitCycle);
    $asserton(0, prim_alert_tb.i_alert_receiver.AckDiffOk_A);
    $display("[prim_alert_seq] Ack signal integrity error sequence finished!");

    // Sequence 5) `Ping_p/n` integrity check sequence.
    // Disable the assertion at least two clock cycles before sending the ping request, because the
    // `PingDiffOk_A` assertion has ##2 delay.
    $assertoff(0, prim_alert_tb.i_alert_receiver.PingDiffOk_A);
    main_clk.wait_clks($urandom_range(MinHandshakeWait, 10));
    force i_alert_receiver.alert_rx_o.ping_n = i_alert_receiver.alert_rx_o.ping_n;
    ping_req = 1;

    wait (integ_fail == 1);
    ping_req = 0;
    release i_alert_receiver.alert_rx_o.ping_n;

    // Ping is the first signal of the handshake, so we can directly turn on the assertion once the
    // forced ping signal is released.
    $asserton(0, prim_alert_tb.i_alert_receiver.PingDiffOk_A);
    $display("[prim_alert_seq] Ping signal integrity error sequence finished!");

    dv_test_status_pkg::dv_test_status(.passed(!error));
    $finish();
  end
endmodule
