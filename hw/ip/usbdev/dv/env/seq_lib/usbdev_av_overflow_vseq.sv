// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_av_overflow_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_av_overflow_vseq)

  `uvm_object_new

  // Choose the Available SETUP Buffer FIFO rather than the Available OUT Buffer FIFO.
  rand bit setup;

  // Supply a buffer to the selected FIFO.
  task supply_buffer(int unsigned b);
    if (setup) csr_wr(.ptr(ral.avsetupbuffer), .value(b));
    else csr_wr(.ptr(ral.avoutbuffer), .value(b));
  endtask

  virtual task body();
    int unsigned depth = setup ? AvSetupFIFODepth : AvOutFIFODepth;
    uvm_reg_data_t av_overflow;

    clear_all_interrupts();
    // Enable the Av Overflow interrupt.
    csr_wr(.ptr(ral.intr_enable), .value(1 << IntrAvOverflow));

    // Add buffers into the FIFO; fully populate the FIFO without yet overflowing it.
    // The buffer numbers do not matter.
    for (int unsigned b = 0; b < depth; b++) supply_buffer(b);

    // There should be no interrupt at present.
    csr_rd(.ptr(ral.intr_state.av_overflow), .value(av_overflow));
    `DV_CHECK_EQ(av_overflow, 0, "Av Overlow interrupt unexpectedly asserted")

    // Attempt to add another buffer.
    supply_buffer(depth);

    csr_rd(.ptr(ral.intr_state.av_overflow), .value(av_overflow));
    `DV_CHECK_EQ(av_overflow, 1, "Av Overlow interrupt not asserted when expected")

    // Check that the interrupt line is asserted.
    `DV_CHECK_EQ(cfg.intr_vif.pins[IntrAvOverflow], 1'b1, "Interrupt signal not asserted")
    clear_all_interrupts();
  endtask

endclass : usbdev_av_overflow_vseq
