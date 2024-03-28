// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_resume_link_active_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_resume_link_active_vseq)

  `uvm_object_new

  task body();
    bit [2:0] powered_link_state;
    bit       resume;

    super.dut_init("HARD");
    // Perform no operation for more than 3ms (3ms = 144,000 clk cycle at 48MHz)
    cfg.clk_rst_vif.wait_clks(154000);
    // Read link_state it should be in link powered state
    csr_rd(.ptr(ral.usbstat.link_state), .value(powered_link_state));
    `DV_CHECK_EQ(powered_link_state, 1);

    // Set resume link state in usbctrl register
    csr_wr(.ptr(ral.usbctrl.resume_link_active), .value(1'b1));
    cfg.clk_rst_vif.wait_clks(5);

    // Read link_resume interrupt
    csr_rd(.ptr(ral.intr_state.link_resume), .value(resume));
    // DV_CHECK on link_resume interrupt
    `DV_CHECK_EQ(resume, 1);
  endtask

endclass
