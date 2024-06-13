// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence tests that the Link Reset interrupt is raised
class usbdev_link_reset_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_link_reset_vseq)

  `uvm_object_new

  virtual task body();
    // Ensure the interrupt is not already asserted.
    csr_wr(.ptr(ral.intr_state), .value(1 << IntrLinkReset));
    // Enable the interrupt to make it visible at the pin too.
    csr_wr(.ptr(ral.intr_enable), .value(1 << IntrLinkReset));

    // Leave the link in an Idle state for a while, to make the signaling changes clearer.
    cfg.clk_rst_vif.wait_clks(1000);

    // Perform a Bus Reset that lasts just 10 microseconds; the specification requires at least
    // 10ms of reset signaling, but the device is permitted to respond after just 2.5 microseconds.
    // USBDEV is expected to respond within 4 microseconds.
    fork
      send_bus_reset(10);
      wait_for_interrupt(1 << IntrLinkReset, .timeout_clks(10 * 48), .clear(0), .enforce(1));
    join
    // Check that the interrupt line is asserted.
    `DV_CHECK_EQ(cfg.intr_vif.pins[IntrLinkReset], 1'b1, "Interrupt signal not asserted")
    // Disable the interrupt before completing.
    csr_wr(.ptr(ral.intr_enable), .value(0));
    clear_all_interrupts();
  endtask

endclass : usbdev_link_reset_vseq
