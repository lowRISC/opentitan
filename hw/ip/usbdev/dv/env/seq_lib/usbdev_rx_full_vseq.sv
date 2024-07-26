// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_rx_full_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_rx_full_vseq)

  `uvm_object_new

  // Use SETUP packets rather than OUT?
  rand bit use_setup;

  // Supply a buffer to the selected FIFO.
  task supply_buffer(int unsigned b);
    if (use_setup) csr_wr(.ptr(ral.avsetupbuffer), .value(b));
    else csr_wr(.ptr(ral.avoutbuffer), .value(b));
  endtask

  virtual task body();
    int unsigned max_av_level = use_setup ? AvSetupFIFODepth : AvOutFIFODepth;
    int unsigned exp_av_level = 0;
    int unsigned buffer_id = 0;
    int unsigned exp_rx_level;
    uvm_reg_data_t rx_level;
    uvm_reg_data_t rx_full;

    clear_all_interrupts();
    // Enable the Rx Full interrupt.
    csr_wr(.ptr(ral.intr_enable), .value(1 << IntrRxFull));

    `uvm_info(`gfn, $sformatf("Using SETUP packets %0d", use_setup), UVM_LOW)

    // Make all endpoints accept SETUP packets; `ep_default` is randomized.
    if (use_setup) configure_setup_all();
    else configure_out_all();

    // Keep sending packets until we expect to see the Rx Full interrupt.
    exp_rx_level = RxFIFODepth - !use_setup;
    for (int unsigned b = 0; b < exp_rx_level; b++) begin
      // Ensure one or more buffers if available.
      int unsigned desired_av_level = $urandom_range(1, max_av_level);
      while (exp_av_level < desired_av_level) begin
        // Buffer numbers increase monotonically so that we can check them below.
        supply_buffer(buffer_id);
        buffer_id++;
        exp_av_level++;
      end
      // There should be no interrupt at present.
      csr_rd(.ptr(ral.intr_state.rx_full), .value(rx_full));
      `DV_CHECK_EQ(rx_full, 0, "RX Full interrupt unexpectedly asserted")

      if (use_setup) send_prnd_setup_packet(ep_default);
      else send_prnd_out_packet(ep_default, b[0] ? PidTypeData1 : PidTypeData0);
      exp_av_level--;
    end

    csr_rd(.ptr(ral.intr_state.rx_full), .value(rx_full));
    `DV_CHECK_EQ(rx_full, use_setup, "RX Full interrupt not as expected")
    csr_rd(.ptr(ral.usbstat.rx_depth), .value(rx_level));
    `DV_CHECK_EQ(rx_level, exp_rx_level, "RX FIFO level not as expected")

    // Check that the interrupt line has the expected state.
    `DV_CHECK_EQ(cfg.intr_vif.pins[IntrRxFull], use_setup, "Interrupt signal not asserted")

    // Remove the packets to remove the interrupt.
    for (int unsigned b = 0; b < exp_rx_level; b++) begin
      uvm_reg_data_t rx_fifo_read;
      csr_rd(.ptr(ral.rxfifo), .value(rx_fifo_read));
      // Just check the buffer numbers as we do so.
      `DV_CHECK_EQ(get_field_val(ral.rxfifo.buffer, rx_fifo_read), b)
      // Check the updated FIFO level.
      csr_rd(.ptr(ral.usbstat.rx_depth), .value(rx_level));
      `DV_CHECK_EQ(rx_level, exp_rx_level - 1 - b)
    end

    // Check that the `rx_full` Status interrupt has become deasserted.
    csr_rd(.ptr(ral.intr_state.rx_full), .value(rx_full));
    `DV_CHECK_EQ(rx_full, 1'b0, "RX Full interrupt not deasserted when expected")
    `DV_CHECK_EQ(cfg.intr_vif.pins[IntrRxFull], 1'b0, "Interrupt signal not deasserted")
  endtask

endclass : usbdev_rx_full_vseq
