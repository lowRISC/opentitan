// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// In status stage vseq
class usbdev_in_status_stage_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_in_status_stage_vseq)

  `uvm_object_new

  task body();
    // Configure out transaction
    configure_out_trans();
    // Out token packet followed by a zero length data packet
    call_token_seq(PidTypeOutToken);
    inter_packet_delay();
    call_data_seq(PidTypeData0, .randomize_length(1'b0), .num_of_bytes(1'b0));
    inter_packet_delay();
    // Get response from DUT
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_out_response_from_device(m_usb20_item, PidTypeAck);
    // The sequence verifies that the data size is zero, as this test validates the functionality
    // of sending data with a zero length, followed by acknowledging the data through ACK pid.
    // And we are verifying this by reading the data size from rxfifo.
    check_rxfifo_empty();
  endtask

  task check_rxfifo_empty();
    bit read_rxfifo_size;
    // Get rx fifo size status
    csr_rd(.ptr(ral.rxfifo.size), .value(read_rxfifo_size));
    // DV_CHECK on data size
    `DV_CHECK_EQ(read_rxfifo_size, 0);
  endtask
endclass
