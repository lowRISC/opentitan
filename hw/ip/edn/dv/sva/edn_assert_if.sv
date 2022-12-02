// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Interface: edn_assert_if
// Description: Asserts interface to turn off assertions that have long paths

`define PATH1 \
    tb.dut.u_edn_core.u_prim_count_max_reqs_cntr
`define PATH2 \
    tb.dut.u_edn_core.u_prim_mubi4_sync_edn_enable
`define PATH3 \
    tb.dut.u_edn_core.u_prim_mubi4_sync_boot_req_mode
`define PATH4 \
    tb.dut.u_edn_core.u_prim_mubi4_sync_auto_req_mode
`define PATH5 \
    tb.dut.u_edn_core.u_prim_mubi4_sync_cmd_fifo_rst
`define PATH6 \
    tb.dut.u_edn_core.u_edn_main_sm
`define PATH7 \
    tb.dut.u_edn_core.gen_ep_blk[0].u_edn_ack_sm_ep

interface edn_assert_if(input clk, input rst_n);

  task automatic assert_off ();
    $assertoff(0, `PATH1.CntErrBackward_A);
    $assertoff(0, `PATH6.u_state_regs_A);
    $assertoff(0, `PATH7.u_state_regs_A);
  endtask // assert_off

  task automatic assert_on ();
    $asserton(0, `PATH1.CntErrBackward_A);
    $asserton(0, `PATH6.u_state_regs_A);
    $asserton(0, `PATH7.u_state_regs_A);
  endtask // assert_on

  task automatic assert_off_alert ();

  endtask // assert_off_alert

  task automatic assert_on_alert ();

  endtask // assert_on_alert

endinterface
