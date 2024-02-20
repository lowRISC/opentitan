// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Stall_priority_over_nak vseq
class usbdev_stall_priority_over_nak_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_stall_priority_over_nak_vseq)

  `uvm_object_new

  task body();
    super.dut_init("HARD");
    clear_all_interrupts();  // clear interrupts
    // Configure out transaction
    configure_out_trans();
    // Set nak_out endpoint
    ral.set_nak_out[0].enable[endp].set(1'b1);
    csr_update(ral.set_nak_out[0]);
    // Set out_stall endpoint
    ral.out_stall[0].endpoint[endp].set(1'b1);
    csr_update(ral.out_stall[0]);
    // Out token packet followed by a data packet
    call_token_seq(PktTypeToken, PidTypeOutToken, endp);
    cfg.clk_rst_vif.wait_clks(20);
    call_data_seq(PktTypeData, PidTypeData0, rand_or_not, num_of_bytes);
    cfg.clk_rst_vif.wait_clks(20);
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_out_response_from_device(m_usb20_item, PidTypeStall);
    // change available buffer id
    ral.avoutbuffer.buffer.set(out_buffer_id + 1);
    csr_update(ral.avoutbuffer);
  endtask
endclass
