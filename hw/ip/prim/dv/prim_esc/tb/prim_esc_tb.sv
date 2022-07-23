// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for prim_esc_sender and prim_esc_receiver_pair.
//
// This test has five sequnces:
// 1). Random reset during escalation handshake sequence.
// 2). Escalation request sequence.
// 3). Ping request interrupted by escalation request sequence.
// 4). Integrity error sequence.
// 5). Escalation reverse ping timeout sequence.
// 6). Escalation receiver counter fail sequence.
// 7). Random esc_rx/tx signal without request error sequence.

module prim_esc_tb;

  import dv_utils_pkg::*;
  `include "dv_macros.svh"

  //////////////////////////////////////////////////////
  // config
  //////////////////////////////////////////////////////

  localparam time ClkPeriod  = 10000;
  localparam int  PING_CNT_DW = 1;
  localparam int  TIMEOUT_CYCLES = 1 << (PING_CNT_DW + 6);
  localparam string MSG_ID = $sformatf("%m");

  uint default_spinwait_timeout_ns = 100_000;

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

  logic ping_req, ping_ok, integ_fail, esc_req, esc_req_out;
  prim_esc_pkg::esc_tx_t esc_tx;
  prim_esc_pkg::esc_rx_t esc_rx;

  prim_esc_sender i_esc_sender (
    .clk_i(clk),
    .rst_ni(rst_n),
    .ping_req_i(ping_req),
    .ping_ok_o(ping_ok),
    .integ_fail_o(integ_fail),
    .esc_req_i(esc_req),
    .esc_rx_i(esc_rx),
    .esc_tx_o(esc_tx)
  );

  prim_esc_receiver #(
    .N_ESC_SEV(4),
    // Set to 1 to avoid long wait period to check ping request reverse timeout.
    .PING_CNT_DW(PING_CNT_DW)
  ) i_esc_receiver (
    .clk_i(clk),
    .rst_ni(rst_n),
    .esc_req_o(esc_req_out),
    .esc_rx_o(esc_rx),
    .esc_tx_i(esc_tx)
  );

  //////////////////////////////////////////////////////
  // Helper Functions/Tasks and Variables
  //////////////////////////////////////////////////////

  logic error = 0;

  function automatic void test_error(string msg);
    $error($sformatf("%time: %0s", $realtime, msg));
    error = 1;
  endfunction

  //////////////////////////////////////////////////////
  // Stimuli Application / Response Checking
  //////////////////////////////////////////////////////

  initial begin: p_stimuli
    time delay_ps;

    ping_req = 0;
    esc_req  = 0;
    main_clk.set_period_ps(ClkPeriod);
    main_clk.set_active();
    main_clk.apply_reset();

    // Sequence 1. Random reset during escalation handshake sequence.
    ping_req = 1;
    // Issue async reset between first and fifth clock cycle to reach FSM coverages.
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(delay_ps, delay_ps inside {[1:ClkPeriod]};, , MSG_ID)
    #((delay_ps + $urandom_range(1, 5) * ClkPeriod) * 1ps);
    main_clk.apply_reset();
    ping_req = 0;

    $display("[prim_esc_seq] Random reset during escalation handshake sequence finished!");

    // Sequence 2. Escalation request sequence.
    esc_req = 1;
    // Drive random length of esc_req and check `esc_req_out` and `integ_fail` outputs.
    main_clk.wait_clks($urandom_range(1, 20));
    if (integ_fail)   test_error("Esc_req unexpected signal integrity error!");
    if (!esc_req_out) test_error("Esc_req did not set esc_req!");
    esc_req = 0;

    $display("[prim_esc_seq] Escalation request sequence finished!");

    // Sequence 3. Ping request interrupted by escalation request.
    main_clk.wait_clks($urandom_range(2, 20));
    #1ns;
    ping_req = 1;
    `DV_SPINWAIT(wait (ping_ok == 1);, , , "Wait for ping_ok timeout");
    if (integ_fail) test_error("Expect no errors when trigger ping_req");
    main_clk.wait_clks($urandom_range(2, 20));
    ping_req = 0;

    main_clk.wait_clks($urandom_range(2, 20));
    ping_req = 1;
    // Wait a max of 5 clock cycle to ensure esc_req is send during ping handshake.
    main_clk.wait_clks($urandom_range(0, 5));
    esc_req = 1;
    `DV_SPINWAIT(wait (ping_ok == 1);, , , "Wait for ping_ok timeout");
    `DV_SPINWAIT(wait (esc_req_out == 1);, , , "Wait for esc_req_out timeout");
    main_clk.wait_clks(1);
    esc_req = 0;
    ping_req = 0;
    if (integ_fail) test_error("Expect no errors when esc_req interrupts ping_req");

    $display("[prim_esc_seq] Ping request interrupted by escalation request sequence finished!");

    // Sequence 4.1 Integrity error sequence during escalation request.
    main_clk.wait_clks($urandom_range(1, 20));
    esc_req = 1;
    // Randomly wait a few clock cycles then inject integrity error.
    main_clk.wait_clks($urandom_range(0, 5));
    // Force esc_tx signal to create a integrity fail error case.
    force esc_tx.esc_n = 1;
    `DV_SPINWAIT(wait (integ_fail == 1);, , , "Wait for esc_tx.esc_n integ_fail timeout");
    main_clk.wait_clks(1);
    release esc_tx.esc_n;
    // Wait #1ps to avoid a race condition on clock edge.
    #1ps;
    if (!esc_req_out) test_error("Signal integrity error should set esc_req!");
    esc_req = 0;
    $display("[prim_esc_seq] Integrity esc_tx error sequence finished [1/2]!");

    main_clk.wait_clks($urandom_range(1, 20));
    // Force esc_tx signal to create a integrity fail error case.
    force esc_rx.resp_n = 1;
    esc_req = 1;
    `DV_SPINWAIT(wait (integ_fail == 1);, , , "Wait for esc_rx.resp_n integ_fail timeout");
    main_clk.wait_clks(1);
    release esc_rx.resp_n;
    // Wait #1ps to avoid a race condition on clock edge.
    #1ps;
    if (!esc_req_out) test_error("Signal integrity error should set esc_req!");
    esc_req = 0;
    $display("[prim_esc_seq] Integrity esc_rx error sequence finished [2/2]!");

    // Sequence 4.1 `Esc_tx` integrity error sequence during ping request.
    main_clk.wait_clks($urandom_range(1, 20));
    ping_req = 1;
    // Force esc_tx signal to create a integrity fail error case.
    force esc_tx.esc_n = 1;
    `DV_SPINWAIT(wait (integ_fail == 1);, , , "Wait for ping request integ_fail timeout");
    release esc_tx.esc_n;
    // Wait #1ps to avoid a race condition on clock edge.
    #1ps;
    if (!esc_req_out) test_error("Signal integrity error should set esc_req!");
    if (ping_ok)      test_error("Ping error!");
    ping_req = 0;

    $display("[prim_esc_seq] Escalation esc_p/n integrity sequence during ping request finished!");

    // Sequence 5. Escalation reverse ping timeout sequence.
    // Wait at least two clock cycles for the previous sequence to finish its escalation request.
    main_clk.wait_clks($urandom_range(2, 20));
    ping_req = 1;
    fork
      begin
        // After one ping_req, esc_receiver will start a counter to expect next ping_req. If the
        // counter reaches its max value but no ping_req has been received, design will set
        // `esc_req_out` signal.
        main_clk.wait_clks(TIMEOUT_CYCLES + 1);
        if (!esc_req_out) test_error("Design failed to detect ping request timeout!");
      end
      begin
        // Wait for a ping handshake to complete.
        `DV_SPINWAIT(wait (ping_ok == 1);, , , "Wait for ping_ok timeout");
        main_clk.wait_clks(2);
        ping_req = 0;
        if (integ_fail)  test_error("Ping_req unexpected signal integrity error!");
        if (esc_req_out) test_error("Ping request should not set esc_req_out!");
      end
    join
    main_clk.apply_reset();

    $display("[prim_esc_seq] Escalation ping request timeout sequence finished!");

    // Sequence 6. Escalation receiver counter fail sequence.
    ping_req = 1;
    // Wait until ping request is acknowledged and counter starts to increment.
    `DV_SPINWAIT(wait (ping_ok == 1);, , , "Wait for ping_ok timeout");
    main_clk.wait_clks(2);
    ping_req = 0;
    // If duplicate counter values are inconsistent, the design will set the `esc_req_out` signal.
    force prim_esc_tb.i_esc_receiver.u_prim_count.cnt_q[1] = '0;
    `DV_SPINWAIT(wait (esc_req_out == 1);, , , "Wait for esc_req_out timeout");
    if (integ_fail) test_error("Escalation receiver counter unexpected signal integrity error!");
    release prim_esc_tb.i_esc_receiver.u_prim_count.cnt_q[1];

    $display("[prim_esc_seq] Escalation couter error sequence finished!");

    // 7. Random esc_rx/tx signal without request error sequence.
    main_clk.wait_clks($urandom_range(1, 20));
    // Force esc_tx signals to create a integrity fail error case.
    force esc_rx.resp_p = 1;
    force esc_rx.resp_n = 0;
    `DV_SPINWAIT(wait (integ_fail == 1);, , , "Wait for esc_rx.resp_p/n integ_fail timeout");
    release esc_rx.resp_p;
    release esc_rx.resp_n;
    $display("[prim_esc_seq] Random esc_rx error sequence finished [1/2]!");

    main_clk.wait_clks($urandom_range(1, 20));
    // Force esc_tx signals to create a integrity fail error case.
    force esc_tx.esc_p = 1;
    force esc_tx.esc_n = 0;
    `DV_SPINWAIT(wait (integ_fail == 1);, , , "Wait for esc_rx.resp_p/n integ_fail timeout");
    release esc_tx.esc_p;
    release esc_tx.esc_n;
    $display("[prim_esc_seq] Random esc_tx error sequence finished [1/2]!");
    main_clk.wait_clks(2);

    dv_test_status_pkg::dv_test_status(.passed(!error));
    $finish();
  end

endmodule
