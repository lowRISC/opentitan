// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Av out empty vseq
class usbdev_av_out_empty_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_av_out_empty_vseq)

  `uvm_object_new

  task body();
    uvm_reg_data_t read_rxfifo;
    super.dut_init("HARD");
    clear_all_interrupts();  // clear interrupts
    // Configure out transaction
    configure_out_trans();
    // Enable av_empty interrupt
    ral.intr_enable.av_out_empty.set(1'b1);
    csr_update(ral.intr_enable);
    // Out token packet followed by a data packet
    call_token_seq(PktTypeToken, PidTypeOutToken, endp);
    cfg.clk_rst_vif.wait_clks(20);
    call_data_seq(PktTypeData, PidTypeData0, rand_or_not, num_of_bytes);
    cfg.clk_rst_vif.wait_clks(20);
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_out_response_from_device(m_usb20_item, PidTypeAck);
    // Verifies that the av empty signal
    check_trans_accuracy();
    // Make sure buffer is availabe for next trans
    ral.avoutbuffer.buffer.set(out_buffer_id + 1);
    csr_update(ral.avoutbuffer);
    // Read rxfifo reg
    csr_rd(.ptr(ral.rxfifo), .value(read_rxfifo));
    // clear interrupts
    clear_all_interrupts();
  endtask

  task check_trans_accuracy();
    bit av_out_empty;
    // Read av empty interrupt state
    csr_rd(.ptr(ral.intr_state.av_out_empty), .value(av_out_empty));
    // DV_CHECK on av empty interrupt
    `DV_CHECK_EQ(av_out_empty, 1);
  endtask
endclass
