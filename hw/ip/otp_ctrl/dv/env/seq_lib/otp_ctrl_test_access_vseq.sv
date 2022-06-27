// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TODO: add support to randomly turn on and off lc_dft_en to fully verify the `prim_lc_gate`
// module.
class otp_ctrl_test_access_vseq extends otp_ctrl_dai_lock_vseq;
  `uvm_object_utils(otp_ctrl_test_access_vseq)

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);

    // Drive dft_en pins to access the test_access memory.
    cfg.otp_ctrl_vif.drive_lc_dft_en(lc_ctrl_pkg::On);

    // Once turn on lc_dft_en regiser, will need some time to update the state register
    // two clock cycles for lc_async mode, one clock cycle for driving dft_en.
    cfg.clk_rst_vif.wait_clks(3);
  endtask

endclass
