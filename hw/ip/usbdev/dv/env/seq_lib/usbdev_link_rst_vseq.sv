// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// usbdev_link_rst test vseq

class usbdev_link_rst_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_link_rst_vseq)

  `uvm_object_new

  uint   link_rst_timeout_ns = 144; // 3.0us

  task body();
    uvm_reg_data_t read_intr;
    uvm_reg_data_t read_usbstat;
    bit     [31:0] intr_exp;
    bit     [31:0] mask_out;

    super.dut_init("HARD");
    // Clear all interrupts
    csr_wr(.ptr(ral.intr_state), .value(32'h003_ffff));
    // Enable link reset interrupt
    csr_wr(.ptr(ral.intr_enable), .value(32'h0000_0010));
    // Wait for 3us
    cfg.clk_rst_vif.wait_clks(link_rst_timeout_ns);
    // Read USB interrupt register to check link reset interrupt is set
    // Mask out all other interrupts
    intr_exp = 32'h0000_0010;
    mask_out = 32'h0000_0010;
    csr_rd(.ptr(ral.intr_state), .value(read_intr));
    `uvm_info(`gfn, $sformatf("read_intr = %h\n",read_intr), UVM_DEBUG)
    `DV_CHECK_EQ(intr_exp, (read_intr & mask_out));
    // Clear all interrupts
    csr_wr(.ptr(ral.intr_state), .value(32'h003_ffff));
  endtask
endclass : usbdev_link_rst_vseq
