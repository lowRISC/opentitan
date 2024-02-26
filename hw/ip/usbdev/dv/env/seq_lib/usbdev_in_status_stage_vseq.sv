// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// In status stage vseq
class usbdev_in_status_stage_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_in_status_stage_vseq)

  `uvm_object_new

  task body();
    num_of_bytes = 0;
    rand_or_not = 0;

    super.dut_init("HARD");
    clear_all_interrupts();  // clear interrupts
    // Configure out transaction
    configure_out_trans();
    // Out token packet followed by a zero length data packet
    call_token_seq(PktTypeToken, PidTypeOutToken, endp);
    cfg.clk_rst_vif.wait_clks(20);
    call_data_seq(PktTypeData, PidTypeData0, rand_or_not, num_of_bytes);
    // Get response from DUT
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_out_response_from_device(m_usb20_item, PidTypeAck);
    cfg.clk_rst_vif.wait_clks(20);
    check_out_trans_accuracy();
    // Make sure buffer is availabe for next trans
    ral.avoutbuffer.buffer.set(out_buffer_id + 1);
    csr_update(ral.avoutbuffer);
  endtask

  task check_out_trans_accuracy();
    bit read_rxfifo_size;
    // Get rx fifo size status
    csr_rd(.ptr(ral.rxfifo.size), .value(read_rxfifo_size));
    // DV_CHECK on data size
    `DV_CHECK_EQ(read_rxfifo_size, 0);
  endtask
endclass
