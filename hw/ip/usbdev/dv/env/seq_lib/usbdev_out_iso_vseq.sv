// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Isochronous OUT transaction.

class usbdev_out_iso_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_out_iso_vseq)

  `uvm_object_new

  task body();
    // Expected data content of packet
    byte unsigned exp_data[];
    bit pkt_received;

    configure_out_trans(ep_default);
    // ISO EP OUT
    csr_wr(.ptr(ral.out_iso[0].iso[ep_default]), .value(1'b1));
    // write to clear pkt_received interrupt; we want to verify this becomes asserted in
    // response to the transaction.
    csr_wr(.ptr(ral.intr_state.pkt_received), .value(1'b1));
    send_prnd_out_packet(ep_default, PidTypeData0, .randomize_length(1'b1), .num_of_bytes(0));
    // The device should not send an ACK in this case because the traffic is isochronous.
    check_no_response();

    // Wait until usbdev generates an interrupt to show the packet has been received, and then
    // validate the received packet.
    for (int i = 0; i < 10; i++) begin
      csr_rd(.ptr(ral.intr_state.pkt_received), .value(pkt_received));
      if (pkt_received) break;
    end
    if (!pkt_received) begin
      `uvm_error(`gfn, "usbdev didn't generate expected pkt_received interrupt")
    end
    check_rx_packet(ep_default, 1'b0, out_buffer_id, m_data_pkt.data);
  endtask
endclass
