// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_rx_full_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_rx_full_vseq)

  `uvm_object_new

  // Supply a buffer to the selected FIFO.
  task supply_buffer(int unsigned b);
    csr_wr(.ptr(ral.avsetupbuffer), .value(b));
  endtask

  virtual task body();
    uvm_reg_data_t rx_full;

    clear_all_interrupts();
    // Enable the Rx Full interrupt.
    csr_wr(.ptr(ral.intr_enable), .value(1 << IntrRxFull));

    // Make all endpoints accept SETUP packets; `ep_default` is randomized.
    configure_setup_all();

    // Keep sending packets until we expect to see the Rx Full interrupt.
    for (int unsigned b = 0; b < RxFIFODepth; b++) begin
      // Make a single buffer available; the buffer number does not matter.
      supply_buffer(b);

      // There should be no interrupt at present.
      csr_rd(.ptr(ral.intr_state.rx_full), .value(rx_full));
      `DV_CHECK_EQ(rx_full, 0, "RX Full interrupt unexpectedly asserted")

      send_prnd_setup_packet(ep_default);
    end

    csr_rd(.ptr(ral.intr_state.rx_full), .value(rx_full));
    `DV_CHECK_EQ(rx_full, 1, "RX Full interrupt not asserted when expected")

    // Check that the interrupt line is asserted.
    `DV_CHECK_EQ(cfg.intr_vif.pins[IntrRxFull], 1'b1, "Interrupt signal not asserted")

    // Remove the packets to remove the interrupt.
    for (int unsigned b = 0; b < RxFIFODepth; b++) begin
      uvm_reg_data_t rx_fifo_read;
      csr_rd(.ptr(ral.rxfifo), .value(rx_fifo_read));
      // Just check the buffer numbers as we do so.
      `DV_CHECK_EQ(get_field_val(ral.rxfifo.buffer, rx_fifo_read), b)
    end
    clear_all_interrupts();
  endtask

endclass : usbdev_rx_full_vseq
