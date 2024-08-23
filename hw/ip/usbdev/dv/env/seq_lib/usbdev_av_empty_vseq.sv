// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_av_empty_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_av_empty_vseq)

  `uvm_object_new

  // Choose the Available SETUP Buffer FIFO rather than the Available OUT Buffer FIFO.
  rand bit setup;

  // Supply a buffer to the selected FIFO.
  task supply_buffer(int unsigned b);
    if (setup) csr_wr(.ptr(ral.avsetupbuffer), .value(b));
    else csr_wr(.ptr(ral.avoutbuffer), .value(b));
  endtask

  task check_level(int unsigned exp_level);
    uvm_reg_data_t level;
    if (setup) csr_rd(.ptr(ral.usbstat.av_setup_depth), .value(level));
    else csr_rd(.ptr(ral.usbstat.av_out_depth), .value(level));
    `DV_CHECK_EQ(level, exp_level, "Unexpected FIFO level")
  endtask

  task check_interrupt_state(bit exp, string msg);
    uvm_reg_data_t av_empty;
    if (setup) csr_rd(.ptr(ral.intr_state.av_setup_empty), .value(av_empty));
    else csr_rd(.ptr(ral.intr_state.av_out_empty), .value(av_empty));
    `DV_CHECK_EQ(av_empty, exp, msg);
  endtask

  virtual task body();
    uvm_reg_data_t intr_bit = 1 << (setup ? IntrAvSetupEmpty : IntrAvOutEmpty);
    int unsigned depth = setup ? AvSetupFIFODepth : AvOutFIFODepth;

    `uvm_info(`gfn, $sformatf("Testing AVSetup %0d", setup), UVM_LOW)

    clear_all_interrupts();
    // Enable the appropriate Av Empty interrupt.
    csr_wr(.ptr(ral.intr_enable), .value(intr_bit));
    check_level(0);

    // Add a single buffer into the FIFO.
    supply_buffer(0);
    check_level(1);

    // There should be no interrupt at present.
    check_interrupt_state(0, "Av Empty interrupt unexpectedly asserted");

    // Send a single SETUP/OUT packet to cause the buffer to be consumed, and the FIFO to empty.
    if (setup) begin
      configure_setup_all();
      send_prnd_setup_packet(ep_default);
    end else begin
      configure_out_all();
      send_prnd_out_packet(ep_default, PidTypeData0);
    end
    check_response_matches(PidTypeAck);

    // Check the new FIFO level; the FIFO should be empty.
    check_level(0);
    // The AV Empty interrupt should be asserted too.
    check_interrupt_state(1, "Av Empty interrupt not asserted when expected");

    // Check that the interrupt line is asserted.
    `DV_CHECK_EQ(cfg.intr_vif.pins[setup ? IntrAvSetupEmpty : IntrAvOutEmpty], 1'b1,
                 "Interrupt signal not asserted")

    // Provide another buffer and check that this Status type interrupt is deasserted.
    supply_buffer(1);
    check_level(1);
    check_interrupt_state(0, "Av Empty interrupt unexpectedly remained asserted");
    `DV_CHECK_EQ(cfg.intr_vif.pins[setup ? IntrAvSetupEmpty : IntrAvOutEmpty], 1'b0)

    // Disable the interrupt so that it does not remain asserted when the FIFOs are emptied.
    csr_wr(.ptr(ral.intr_enable), .value(0));
  endtask

endclass : usbdev_av_empty_vseq
