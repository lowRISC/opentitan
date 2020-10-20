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
    // drive pwr_otp_req pin
    cfg.pwr_otp_vif.drive_pin(0, 1);
    // drive dft_en pins to access the test_access memory
    cfg.lc_dft_en_vif.drive(lc_ctrl_pkg::On);
    wait(cfg.pwr_otp_vif.pins[2] == 1);
  endtask

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

endclass
