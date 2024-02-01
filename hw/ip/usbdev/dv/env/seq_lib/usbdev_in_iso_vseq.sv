// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_in_iso_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_in_iso_vseq)

  `uvm_object_new

  task body();
    configure_out_trans();
    call_token_seq(PidTypeOutToken);
    inter_packet_delay();
    call_data_seq(PidTypeData0, .randomize_length(1'b1), .num_of_bytes(0));
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    // check OUT response
    get_out_response_from_device(m_usb20_item, PidTypeAck);
    inter_packet_delay();
    // register configurations for IN Trans.
    configure_in_trans(out_buffer_id, m_data_pkt.data.size());
    // ISO EP1 OUT
    csr_wr(.ptr(ral.in_iso[0].iso[endp]), .value(1'b1));
    // Token pkt followed by handshake pkt
    call_token_seq(PidTypeInToken);
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_data_pid_from_device(m_usb20_item, PidTypeData0);
    // For completion of IN transaction and assertion of in_sent interrupt
    // after succesful IN. ACK from Host is not required because the endpoint
    // hase been configured for isochronous traffic.
    // Verify Transaction reads register status and verifis that IN trans is successfull.
    check_in_sent(); // verify that IN transaction is successfull.
  endtask
endclass
