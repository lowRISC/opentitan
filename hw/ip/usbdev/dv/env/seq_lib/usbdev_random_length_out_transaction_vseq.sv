// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Random length out transaction vseq
class usbdev_random_length_out_transaction_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_random_length_out_transaction_vseq)

  `uvm_object_new

  task body();
    // Configure out transaction
    configure_out_trans();
    // Out token packet followed by a data packet of random bytes
    call_token_seq(PktTypeToken, PidTypeOutToken);
    cfg.clk_rst_vif.wait_clks(20);
    call_data_seq(PktTypeData, PidTypeData0, rand_or_not, num_of_bytes);
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_out_response_from_device(m_usb20_item, PidTypeAck);
    cfg.clk_rst_vif.wait_clks(20);
    // Verifies the data size is of random length
    check_trans_accuracy();
  endtask

  task check_trans_accuracy();
    bit      [6:0] data_size;
    bit      [6:0] rx_fifo_data_size;

     // Checking that data is of random length (0-64 bytes)
    csr_rd(.ptr(ral.rxfifo.size), .value(rx_fifo_data_size));
    `uvm_info(`gfn, $sformatf("RX fifo size =  %d", rx_fifo_data_size), UVM_DEBUG)
    `uvm_info(`gfn, $sformatf("Data size =  %d", m_data_pkt.data.size()), UVM_DEBUG)
    `DV_CHECK_EQ(rx_fifo_data_size, m_data_pkt.data.size());
  endtask
endclass
