// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// usbdev_link_suspend test vseq
class usbdev_link_suspend_vseq extends usbdev_pkt_sent_vseq;
  `uvm_object_utils(usbdev_link_suspend_vseq)

  `uvm_object_new

  // Section 7.1.7.6 of the USB 2.0 Protocol Specification
  // - more than 3.0ms of constant Idle signaling shall put the device in
  //   Suspend state.
  uint link_rst_suspend_ns = 3_100 * 48; // 3.1ms in 48MHz clock cycles.

  task body();
    uvm_reg_data_t link_suspend;
    uvm_reg_data_t link_state;

    // Send transaction to make link active
    super.body();

    // Read USB status to check link is active
    // Link state should be active no SOF
    csr_rd(.ptr(ral.usbstat.link_state), .value(link_state));
    `DV_CHECK_EQ(usbdev_link_state_e'(link_state), LinkActiveNoSOF)

    // Ensure the interrupt is not presently asserted.
    csr_wr(.ptr(ral.intr_state), .value(1 << IntrLinkSuspend));

    // Wait for longer than 3ms, generating no activity; bus remains Idle.
    cfg.clk_rst_vif.wait_clks(link_rst_suspend_ns);

    // Read USB status register to check link state field
    // Link state should be suspended
    csr_rd(.ptr(ral.usbstat.link_state), .value(link_state));
    `DV_CHECK_EQ(usbdev_link_state_e'(link_state), LinkSuspended)

    // Check that the link suspend interrupt has been asserted.
    wait_for_interrupt(1 << IntrLinkSuspend, .timeout_clks(1), .clear(1), .enforce(1));
    // Disable the interrupt before completing.
    csr_wr(.ptr(ral.intr_enable), .value(0));
  endtask
endclass : usbdev_link_suspend_vseq
