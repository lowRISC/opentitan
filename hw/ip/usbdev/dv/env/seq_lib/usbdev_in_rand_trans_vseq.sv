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
    configure_out_trans(ep_default); // register configurations for OUT Trans.
    // Out token packet followed by a data packet
    send_prnd_out_packet(ep_default, PidTypeData0, .randomize_length(1'b0),
                         .num_of_bytes(num_of_bytes));
    check_response_matches(PidTypeAck);
    // IN Trans configurations
    configure_in_trans(ep_default, out_buffer_id, m_data_pkt.data.size());
    // Token pkt followed by handshake pkt
    send_token_packet(ep_default, PidTypeInToken);
    check_response_matches(PidTypeData0);
    send_handshake(PidTypeAck);

    for (int i = 0; i < 10; i++) begin
      csr_rd(ral.intr_state.pkt_sent, .value(pkt_sent));
      if (pkt_sent) break;
    end
    if (!pkt_sent) begin
      `uvm_error(`gfn, "usbdev IN transaction not completed")
    end
  endtask
endclass
