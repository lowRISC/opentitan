// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// usbdev_link_suspend test vseq

class usbdev_link_suspend_vseq extends usbdev_pkt_sent_vseq;
  `uvm_object_utils(usbdev_link_suspend_vseq)

  `uvm_object_new

  uint           link_rst_suspend_ns = 148_800; // 3.1ms

  task body();
    uvm_reg_data_t read_intr;
    uvm_reg_data_t read_usbstat;
    bit     [31:0] mask_reg;
    bit     [31:0] expect_val;

    // Send transaction to make link active
    super.body();
    // Clear all interrupts
    csr_wr(.ptr(ral.intr_state), .value(32'h0003_ffff));
    // Read USB status to check link is active
    // Mask out everything and compare only link_state field
    // Link state should be active no SOF
    mask_reg = 32'h0000_7000;
    expect_val = 32'h0000_5000;
    csr_rd(.ptr(ral.usbstat), .value(read_usbstat));
    `DV_CHECK_EQ(expect_val, (read_usbstat & mask_reg));
    // Enable link Supended interrupt
    csr_wr(.ptr(ral.intr_enable), .value(32'h0000_0020));
    // Wait for longer than 3ms
    cfg.clk_rst_vif.wait_clks(link_rst_suspend_ns);
    // Read USB status register to check link state field
    // Mask out everything and compare only link_state field
    // Link state should be suspended
    mask_reg = 32'h0000_7000;
    expect_val = 32'h0000_4000;
    csr_rd(.ptr(ral.usbstat), .value(read_usbstat));
    `DV_CHECK_EQ(expect_val, (read_usbstat & mask_reg));
    `uvm_info(`gfn, $sformatf("read_usbstat = %h\n",read_usbstat), UVM_DEBUG)
    // Read USB interrupt register to check link suspend interrupt is set
    // Link Supended Interrupt
    mask_reg = 32'h0000_0020;
    expect_val = 32'h0000_0020;
    csr_rd(.ptr(ral.intr_state), .value(read_intr));
    `DV_CHECK_EQ(expect_val, (read_intr & mask_reg));
    // Clear all interrupts
    csr_wr(.ptr(ral.intr_state), .value(32'h0003_ffff));
  endtask
endclass : usbdev_link_suspend_vseq
