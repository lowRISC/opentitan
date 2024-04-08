// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_in_rand_trans_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_in_rand_trans_vseq)

  `uvm_object_new

  task body();
    bit [6:0] num_of_bytes;
    bit pkt_sent;

    // Take the size of the packet from a plusarg if specified. If not, pick a random size.
    if (!$value$plusargs("num_of_bytes=%0d", num_of_bytes)) begin
      num_of_bytes = $urandom_range(0, 64);
    end
    `uvm_info(`gfn, $sformatf("Sending OUT then IN packet, with length %0d", num_of_bytes),
              UVM_MEDIUM)

    // For IN transaction need to do first OUT transaction
    // to store data in buffer memory for read through IN.
    configure_out_trans(); // register configurations for OUT Trans.
    // Out token packet followed by a data packet
    call_token_seq(PidTypeOutToken);
    inter_packet_delay();
    call_data_seq(PidTypeData0, 1'b0, num_of_bytes);
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    m_usb20_item.check_pid_type(PidTypeAck);
    inter_packet_delay();
    // IN Trans configurations
    configure_in_trans(out_buffer_id, m_data_pkt.data.size());
    // Token pkt followed by handshake pkt
    call_token_seq(PidTypeInToken);
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_data_pid_from_device(m_usb20_item, PidTypeData0);
    inter_packet_delay();
    call_handshake_sequence(PktTypeHandshake, PidTypeAck);
    for (int i = 0; i < 10; i++) begin
      csr_rd(ral.intr_state.pkt_sent, .value(pkt_sent));
      if (pkt_sent) break;
    end
    if (!pkt_sent) begin
      `uvm_error(`gfn, "usbdev IN transaction not completed")
    end
  endtask
endclass
