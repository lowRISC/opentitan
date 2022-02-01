// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Tests the software reset functionality: using `sw_rst_regen` and `sw_rst_ctrl_n` CSRs it causes
// resets for each of the bits randomly. It also triggers lc or sys resets to verify the reset
// transitions that cause rising upper resets but non-rising leafs.
//
// Then it clears specific `sw_rst_regen` bits and attempts to cause resets to determine
// the bits with `sw_rst_regwen` cleared cannot cause a reset.
class rstmgr_sw_rst_vseq extends rstmgr_base_vseq;
  `uvm_object_utils(rstmgr_sw_rst_vseq)

  `uvm_object_new

  task body();
    bit [NumSwResets-1:0] exp_ctrl_n;
    bit [NumSwResets-1:0] sw_rst_regwen = '1;
    alert_pkg::alert_crashdump_t bogus_alert_dump = '1;
    ibex_pkg::crash_dump_t bogus_cpu_dump = '1;
    set_alert_and_cpu_info_for_capture(bogus_alert_dump, bogus_cpu_dump);

    for (int i = 0; i < num_trans; ++i) begin
      `DV_CHECK_RANDOMIZE_FATAL(this)
      check_sw_rst_ctrl_n(sw_rst_ctrl_n, sw_rst_regwen, i % 2);
    end
    // Only run this part of the test if running standalone. Doing this in a stress test
    // messes things up since setting the sw_rst_regwen CSR is irreversible.
    if (is_running_sequence("rstmgr_sw_rst_vseq")) begin
      // In preparation for the per-bit enable test, set sw_rst_ctrl_n to all 1.
      csr_wr(.ptr(ral.sw_rst_ctrl_n[0]), .value('1));
      for (int i = 0; i < NumSwResets; ++i) begin
        bit [NumSwResets-1:0] val_regwen;
        bit [NumSwResets-1:0] exp_regwen;
        val_regwen = ~(1 << i);
        `uvm_info(`gfn, $sformatf("updating sw_rst_regwen with %b", val_regwen), UVM_LOW)
        csr_wr(.ptr(ral.sw_rst_regwen[0]), .value(val_regwen));
        exp_regwen = (~0) << (i + 1);
        `uvm_info(`gfn, $sformatf("compare sw_rst_regwen against %b", exp_regwen), UVM_LOW)
        csr_rd_check(.ptr(ral.sw_rst_regwen[0]), .compare_value(exp_regwen),
                     .err_msg($sformatf("The expected value is %b", exp_regwen)));
        check_sw_rst_ctrl_n(.sw_rst_ctrl_n('0), .sw_rst_regen(exp_regwen), .erase_ctrl_n(1'b1));
      end
      check_alert_and_cpu_info_after_reset(.alert_dump('0), .cpu_dump('0), .enable(1'b1));
    end
  endtask
endclass
