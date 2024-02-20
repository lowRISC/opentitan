// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// usbdev_resume_link_active_vseq test vseq
class usbdev_resume_link_active_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_resume_link_active_vseq)

  `uvm_object_new

  task body();
    bit [2:0] powered_link_state;
    bit       resume;

    super.dut_init("HARD");
    clear_all_interrupts();

    // Perform no operation for more than 3ms (3ms = 144,000 clk cycle)
    cfg.clk_rst_vif.wait_clks(154000);
    // Read link_state it should be in link powered state
    csr_rd(.ptr(ral.usbstat.link_state), .value(powered_link_state));
    `DV_CHECK_EQ(powered_link_state, 1);

    // Set resume link state in usbctrl register
    ral.usbctrl.resume_link_active.set(1'b1);
    csr_update(ral.usbctrl);
    cfg.clk_rst_vif.wait_clks(20);
    // Read link_resume interrupt
    csr_rd(.ptr(ral.intr_state.link_resume), .value(resume));
    // DV_CHECK on link_resume interrupt
    `DV_CHECK_EQ(resume, 1);

    // AV FIFO must be provided a free buffer before the interrupt is cleared
    // otherwise interrupt can re-assert
    ral.avoutbuffer.buffer.set(out_buffer_id);
    csr_update(ral.avoutbuffer);
    // Clear interrupts
    csr_wr(.ptr(ral.intr_state), .value(32'h0001_ffff));
  endtask

endclass
