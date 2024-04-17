// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_link_rst_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_link_rst_vseq)

  `uvm_object_new

  uint link_rst_timeout_ns = 144; // 3.0us

  task body();

    // Enable link reset interrupt
    csr_wr(.ptr(ral.intr_enable.link_reset), .value(1'b1));
    // USB env drives dp and dn in SE0 state greater than 10us after reset.
    // Wait for 3us.
    cfg.clk_rst_vif.wait_clks(link_rst_timeout_ns);
    // Wait for link_reset interrupt
    wait(cfg.intr_vif.sample_pin(IntrLinkReset));
    // Check USB host_lost interrupt that it is asserted.
    `DV_CHECK_EQ(cfg.intr_vif.sample_pin(IntrLinkReset), 1);
  endtask

endclass
