// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Random length out transaction vseq
class usbdev_random_length_out_transaction_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_random_length_out_transaction_vseq)

  `uvm_object_new

  // Subclasses with a fixed length transaction should set this to zero and should set num_of_bytes
  // to the length that they want. The default is to set randomize_length to 1. num_of_bytes will
  // then be ignored.
  bit       randomize_length = 1'b1;
  bit [6:0] num_of_bytes = 0;

  task body();
    // Configure out transaction
    configure_out_trans(ep_default);

    // Out token packet followed by a data packet of random bytes
    send_prnd_out_packet(ep_default, PidTypeData0, .randomize_length(randomize_length),
                         .num_of_bytes(num_of_bytes));
    check_response_matches(PidTypeAck);

    // Check that the USB device received a packet with the expected properties.
    check_pkt_received(ep_default, 0, out_buffer_id, m_data_pkt.data);
  endtask

endclass
