// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Tests the software reset functionality: using `sw_rst_regen` and `sw_rst_ctrl_n` CSRs it causes
// resets for each of the bits randomly. It also triggers lc or sys resets to verify the reset
// transitions that cause rising upper resets but non-rising leafs.
//
// Then it clears specific `sw_rst_regen` bits and attempts to cause resets to determine
// the bits with `sw_rst_regen` cleared cannot cause a reset.
class rstmgr_sw_rst_vseq extends rstmgr_base_vseq;
  `uvm_object_utils(rstmgr_sw_rst_vseq)

  `uvm_object_new

  rand bit [NumSwResets-1:0] sw_rst_ctrl_n;

  task body();
    bit [NumSwResets-1:0] exp_ctrl_n;
    bit [NumSwResets-1:0] sw_rst_regen = '1;
    set_alert_and_cpu_info_for_capture(.alert_dump('1), .cpu_dump('1));
    for (int i = 0; i < num_trans; ++i) begin
      `DV_CHECK_RANDOMIZE_FATAL(this)
      check_sw_rst_ctrl_n(sw_rst_ctrl_n, sw_rst_regen, i % 2);
    end
    // In preparation for the per-bit enable test, set sw_rst_ctrl_n to all 1.
    csr_wr(.ptr(ral.sw_rst_ctrl_n[0]), .value('1));
    for (int i = 0; i < NumSwResets; ++i) begin
      bit [NumSwResets-1:0] val_regen;
      bit [NumSwResets-1:0] exp_regen;
      val_regen = ~(1 << i);
      `uvm_info(`gfn, $sformatf("updating sw_rst_regen with %b", val_regen), UVM_LOW)
      csr_wr(.ptr(ral.sw_rst_regen[0]), .value(val_regen));
      exp_regen = (~0) << (i + 1);
      `uvm_info(`gfn, $sformatf("compare sw_rst_regen against %b", exp_regen), UVM_LOW)
      csr_rd_check(.ptr(ral.sw_rst_regen[0]), .compare_value(exp_regen),
                   .err_msg($sformatf("The expected value is %b", exp_regen)));
      check_sw_rst_ctrl_n(.sw_rst_ctrl_n('0), .sw_rst_regen(exp_regen), .erase_ctrl_n(1'b1));
    end
    check_alert_and_cpu_info_after_reset(.alert_dump('0), .cpu_dump('0), .enable(1'b1));
  endtask
endclass
