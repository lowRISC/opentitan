// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otp_ctrl_common_vseq extends otp_ctrl_base_vseq;
  `uvm_object_utils(otp_ctrl_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    // drive dft_en pins to access the test_access memory
    cfg.otp_ctrl_vif.drive_lc_dft_en(lc_ctrl_pkg::On);
    // once turn on lc_dft_en regiser, will need some time to update the state register
    // two clock cycles for lc_async mode, one clock cycle for driving dft_en
    cfg.clk_rst_vif.wait_clks(3);
  endtask

  virtual task post_start();
    // Random CSR rw might trigger alert. Some alerts will conintuously be triggered until reset
    // applied, which will cause alert_monitor phase_ready_to_end timeout.
    if (do_apply_reset) begin
      dut_init();
    end else wait(0); // wait until upper seq resets and kills this seq

    // delay to avoid race condition when sending item and checking no item after reset occur
    // at the same time
    #1ps;
    super.post_start();
  endtask

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

endclass
