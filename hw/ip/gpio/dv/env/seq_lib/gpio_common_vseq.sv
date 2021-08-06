// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class gpio_common_vseq extends gpio_base_vseq;
  `uvm_object_utils(gpio_common_vseq)
  `uvm_object_new

  constraint num_trans_c {
    num_trans inside {[1:3]};
  }

  virtual task pre_start();
    super.pre_start();
    // GPIO scoreboard is cycle accurate and will only update `intr_state` mirrored value only at
    // the address phase of the next read operation. This is too late for intr_test. So we turn on
    // `predict` switch in `csr_wr` task to avoid this issue.
    if (common_seq_type == "intr_test")  do_predict_csr_wr = 1;
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    // Implement gpio pulldown for csr tests for avoiding comparison
    // mismatch for DATA_IN register checks
    set_gpio_pulls(.pu(1'b0), .pd(1'b1));
    super.dut_init(reset_kind);
  endtask: dut_init

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

endclass
