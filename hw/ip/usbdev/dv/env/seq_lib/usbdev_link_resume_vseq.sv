// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// usbdev_link_resume test vseq
class usbdev_link_resume_vseq extends usbdev_link_suspend_vseq;
  `uvm_object_utils(usbdev_link_resume_vseq)

  `uvm_object_new

  task body();
    uvm_reg_data_t link_state;

    // Send transaction to make link active
    super.body();

    // Check that the DUT is presently Suspended.
    csr_rd(.ptr(ral.usbstat.link_state), .value(link_state));
    `DV_CHECK_EQ(usbdev_link_state_e'(link_state), LinkSuspended)

    // Ensure the interrupt is not presently asserted.
    csr_wr(.ptr(ral.intr_state), .value(1 << IntrLinkResume));

    // Ask the driver to Resume the DUT; Resume Signaling should be >= 20ms, which the usb20_driver
    // will normally use by default, so we don't replicate the time delay here.
    send_resume_signaling();

    // The LinkResume interrupt should be raised at the end of the Resume Signaling, and thus be set
    // almost immediately if not already.
    wait_for_interrupt(1 << IntrLinkResume, .timeout_clks(8), .clear(0), .enforce(1));

    // The USB should also be back in the Idle state, with no SOF having yet been transmitted.
    csr_rd(.ptr(ral.usbstat.link_state), .value(link_state));
    `DV_CHECK_EQ(usbdev_link_state_e'(link_state), LinkActiveNoSOF)
    // Disable the interrupt before completing.
    csr_wr(.ptr(ral.intr_enable), .value(0));
  endtask
endclass : usbdev_link_resume_vseq
