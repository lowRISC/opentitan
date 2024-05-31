// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_in_iso_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_in_iso_vseq)

  `uvm_object_new

  task body();
    configure_out_trans(ep_default);
    send_prnd_out_packet(ep_default, PidTypeData0, .randomize_length(1'b1), .num_of_bytes(0));
    // check OUT response
    check_response_matches(PidTypeAck);
    // register configurations for IN Trans.
    configure_in_trans(ep_default, out_buffer_id, m_data_pkt.data.size());
    // ISO EP1 OUT
    csr_wr(.ptr(ral.in_iso[0].iso[ep_default]), .value(1'b1));
    // Token pkt followed by handshake pkt
    send_token_packet(ep_default, PidTypeInToken);
    check_response_matches(PidTypeData0);
    // For completion of IN transaction and assertion of in_sent interrupt
    // after succesful IN. ACK from Host is not required because the endpoint
    // hase been configured for isochronous traffic.
    // Verify Transaction reads register status and verifis that IN trans is successfull.
    check_in_sent(ep_default); // verify that IN transaction is successfull.
  endtask
endclass
