// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Tests the software reset functionality: using `sw_rst_regen` and `sw_rst_ctrl_n` CSRs it causes
// resets for each of the bits randomly. It also triggers lc or sys resets to verify the reset
// transitions that cause rising upper resets but non-rising leafs.
//
// Then it clears each `sw_rst_regwen` bits and attempts to cause resets to determine
// the bits with `sw_rst_regwen` cleared cannot cause a reset.
class rstmgr_sw_rst_vseq extends rstmgr_base_vseq;
  `uvm_object_utils(rstmgr_sw_rst_vseq)

  `uvm_object_new

  task body();
    bit [NumSwResets-1:0] exp_ctrl_n;
    bit [NumSwResets-1:0] sw_rst_regwen = '1;
    alert_crashdump_t bogus_alert_dump = '1;
    cpu_crash_dump_t bogus_cpu_dump = '1;
    set_alert_and_cpu_info_for_capture(bogus_alert_dump, bogus_cpu_dump);

    for (int i = 0; i < num_trans; ++i) begin
      `DV_CHECK_RANDOMIZE_FATAL(this)
      check_sw_rst_ctrl_n(sw_rst_ctrl_n, sw_rst_regwen, i % 2);
    end
    // Only run this part of the test if running standalone. Doing this in a stress test
    // messes things up since setting the sw_rst_regwen CSR is irreversible.
    if (is_running_sequence("rstmgr_sw_rst_vseq")) begin
      // In preparation for the per-bit enable test, set sw_rst_ctrl_n to all 1.
      rstmgr_csr_wr_unpack(.ptr(ral.sw_rst_ctrl_n), .value({NumSwResets{1'b1}}));
      for (int i = 0; i < NumSwResets; ++i) begin
        // Clear the regwen.
        bit [NumSwResets-1:0] val_regwen = ~(1 << i);
        bit [NumSwResets-1:0] exp_regwen = (~0) << (i + 1);
        `uvm_info(`gfn, $sformatf("clearing sw_rst_regwen[%0d]", i), UVM_LOW)
        csr_wr(.ptr(ral.sw_rst_regwen[i]), .value(val_regwen[i]));
        check_sw_rst_regwen(exp_regwen);
        check_sw_rst_ctrl_n(.sw_rst_ctrl_n('0), .sw_rst_regwen(exp_regwen), .erase_ctrl_n(1'b1));
        check_sw_rst_ctrl_n(.sw_rst_ctrl_n('1), .sw_rst_regwen(exp_regwen), .erase_ctrl_n(1'b1));
        // Check we cannot set it back.
        csr_wr(.ptr(ral.sw_rst_regwen[i]), .value(1));
        csr_rd_check(.ptr(ral.sw_rst_regwen[i]), .compare_value(0),
                     .err_msg($sformatf("sw_rst_regwen[%0d] cannot be set back to 1", i)));
      end
      check_alert_and_cpu_info_after_reset(.alert_dump('0), .cpu_dump('0), .enable(1'b1));
    end
  endtask
endclass
