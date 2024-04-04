// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_link_in_err_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_link_in_err_vseq)

  `uvm_object_new

  virtual task body();
    bit link_error;
    configure_out_trans();
    call_token_seq(PidTypeOutToken);
    inter_packet_delay();
    call_data_seq(PidTypeData0, .randomize_length(1'b1), .num_of_bytes(0));
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_data_pid_from_device(m_usb20_item, PidTypeAck);
    inter_packet_delay();
    // Check that link_in_err interrupt is zero.
    csr_rd(.ptr(ral.intr_state.link_in_err), .value(link_error));
    `DV_CHECK_EQ(0, link_error);
    configure_in_trans(out_buffer_id, m_data_pkt.data.size());
    call_token_seq(PidTypeInToken);
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_data_pid_from_device(m_usb20_item, PidTypeData0);
    inter_packet_delay();
    // Send unexpected PID to USB device and device will assert link_in_err interrupt.
    // Expected pkt is ACK but send NYET packet.
    call_handshake_sequence(PktTypeHandshake, PidTypeNyet);
    csr_rd(.ptr(ral.intr_state.link_in_err), .value(link_error));
    // Check link_in_err is asserted.
    `DV_CHECK_EQ(1, link_error);
  endtask
endclass
