// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_link_resume_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_link_resume_vseq)

  `uvm_object_new

  // 20ms in terms of 48MHZ clock
  uint twentry_ms_ns = 960_000;

  task body();
    // Enable link resume interrupt.
    csr_wr(.ptr(ral.intr_enable.link_resume), .value(1'b1));

    // Wait for 20ms to allow the USB link to enter in suspended state.
    cfg.clk_rst_vif.wait_clks(twentry_ms_ns);

    // Call Start of Frame Sequence to bring USB from suspend to resume state.
    call_sof_seq(PidTypeSofToken);

    // Set wake_control.wake_ack bit.
    csr_wr(.ptr(ral.wake_control.wake_ack), .value(1'b1));

    // Check whether the link resume interrupt is asserted or not.
    `DV_CHECK_EQ(cfg.intr_vif.sample_pin(IntrLinkResume), 1);
  endtask

endclass
