// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class uart_intr_testmode_vseq extends uart_base_vseq;
  `uvm_object_utils(uart_intr_testmode_vseq)

  constraint num_trans_c {
    num_trans inside {[1:5]};
  }

  `uvm_object_new

  task body();
    bit [TL_DW-1:0] dut_intr_state;
    bit [7:0]       exp_intr_state;
    bit [7:0]       exp_intr_pin;

    for (int i = 1; i <= num_trans; i++) begin
      `DV_CHECK_RANDOMIZE_FATAL(this)
      uart_init();

      `DV_CHECK_STD_RANDOMIZE_FATAL(exp_intr_state)
      csr_wr(.csr(ral.intr_test),  .value(exp_intr_state));
      csr_rd(.ptr(ral.intr_state), .value(dut_intr_state));

      exp_intr_pin   = exp_intr_state & en_intr;
      `DV_CHECK_EQ(dut_intr_state, exp_intr_state)
      `DV_CHECK_CASE_EQ(cfg.intr_vif.pins[7:0], exp_intr_pin, $sformatf(
          "exp_intr_state: %0h, en_intr: %0h", exp_intr_state, en_intr))

      csr_wr(.csr(ral.intr_state), .value('hff));
      `uvm_info(`gfn, $sformatf("finished run %0d/%0d", i, num_trans), UVM_LOW)
    end
  endtask : body

endclass : uart_intr_testmode_vseq
