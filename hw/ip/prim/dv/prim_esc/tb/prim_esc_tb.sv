// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for prim_esc_sender and prim_esc_receiver_pair.
//
// This test has four sequnces:
// 1). Escalation request sequence:
//     Drive `esc_req` signal to send an escalation request.
//     Wait random length of cycles and check `esc_en` and `integ_fail` signals.
//     Drive `esc_req` back to zero.
// 2). Esc_tx integrity error sequence:
//     Drive `esc_req` signal to send an escalation request.
//     Force `esc_tx.esc_n` to stay high to create signal integrity errors.
//     Wait for `integ_fail` to fire then release the forced signal.
//     Drive `esc_req` back to zero.
// 3). Escalation reverse ping request timeout sequence:
//     Drive `ping_req` signal to send an escalation ping request.
//     Wait for ping handshake to finish by waiting for `ping_ok` signal to set.
//     Drive `ping_req` signal back to 0 and check `esc_en` and `integ_fail` signals.
//     In the meantime, wait until ping counter timeout for next ping request, and check if
//     `esc_en` is set.
//     Reset DUT to clear `esc_en`.
// 4). Escalation receiver counter fail sequence:
//     Drive `ping_req` signal to send an escalation ping request.
//     Wait until `ping_ok` to ensure the ping counter starts to increment.
//     Force one of the two identical counters to 0 and wait for `esc_en` to set.

module prim_esc_tb;

  //////////////////////////////////////////////////////
  // config
  //////////////////////////////////////////////////////

  localparam time ClkPeriod  = 10000;
  localparam int  PING_CNT_DW = 0;
  localparam int  TIMEOUT_CYCLES = 1 << (PING_CNT_DW + 6);

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

  logic ping_req, ping_ok, integ_fail, esc_req, esc_en;
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
    // Set to 0 to avoid long wait period to check ping request reverse timeout.
    .PING_CNT_DW(PING_CNT_DW)
  ) i_esc_receiver (
    .clk_i(clk),
    .rst_ni(rst_n),
    .esc_en_o(esc_en),
    .esc_rx_o(esc_rx),
    .esc_tx_i(esc_tx)
  );

  //////////////////////////////////////////////////////
  // Helper Functions/Tasks and Variables
  //////////////////////////////////////////////////////

  logic error = 0;

  function automatic void test_error(string msg);
    $error(msg);
    error = 1;
  endfunction

  //////////////////////////////////////////////////////
  // Stimuli Application / Response Checking
  //////////////////////////////////////////////////////

  initial begin: p_stimuli
    ping_req = 0;
    esc_req  = 0;
    main_clk.set_period_ps(ClkPeriod);
    main_clk.set_active();
    main_clk.apply_reset();

    // 1). Escalation request sequence.
    esc_req = 1;
    // Drive random length of esc_req and check `esc_en` and `integ_fail` outputs.
    main_clk.wait_clks($urandom_range(1, 20));
    if (integ_fail == 1) test_error("Esc_req unexpected signal integrity error!");
    if (esc_en == 0)     test_error("Esc_req did not set esc_en!");
    esc_req = 0;

    $display("Escalation request sequence passed!");

    // 2). Esc_tx integrity error sequence.
    main_clk.wait_clks($urandom_range(1, 20));
    esc_req = 1;
    // Force esc_tx signal to create a integrity fail error case.
    force esc_tx.esc_n = 1;
    wait (integ_fail == 1);
    release esc_tx.esc_n;
    if (esc_en == 1) test_error("Signal integrity error should not set esc_en!");
    esc_req = 0;

    $display("Escalation esc_p/n integrity sequence passed!");

    // 3). Escalation reverse ping request timeout sequence.
    main_clk.wait_clks($urandom_range(0, 20));
    ping_req = 1;
    fork
      begin
        // After one ping_req, esc_receiver will start a counter to expect next ping_req. If the
        // counter reaches its max value but no ping_req has been received, design will set
        // `esc_en_o` signal.
        main_clk.wait_clks(TIMEOUT_CYCLES + 1);
        if (esc_en != 1) test_error("Design failed to detect ping request timeout!");
      end
      begin
        // Wait for a ping handshake to complete.
        wait (ping_ok == 1);
        ping_req = 0;
        if (integ_fail == 1) test_error("Ping_req unexpected signal integrity error!");
        if (esc_en == 1)     test_error("Ping request should not set esc_en!");
      end
    join
    main_clk.apply_reset();

    $display("Escalation ping request timeout sequence passed!");

    // 4). Escalation receiver counter fail sequence.
    ping_req = 1;
    // Wait until ping request is acknowledged and counter starts to increment.
    wait (ping_ok == 1);
    ping_req = 0;
    // If cnt_q[0] and cnt_q[1]'s value do not match, deisgn will set `esc_en_o` signal.
    force prim_esc_tb.i_esc_receiver.cnt_q[1] = 0;
    wait (esc_en == 1);
    if (integ_fail == 1) begin
      test_error("Escalation receiver counter unexpected signal integrity error!");
    end

    $display("Escalation couter error sequence passed!");

    dv_test_status_pkg::dv_test_status(.passed(!error));
    $finish();
  end

endmodule
