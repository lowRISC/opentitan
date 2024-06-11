// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// usbdev_av_buffer test vseq
class usbdev_av_buffer_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_av_buffer_vseq)

  `uvm_object_new

  // Shall we exercise the SETUP FIFO rather than the OUT FIFO?
  rand bit setup;
  // Buffer to be used.
  rand bit [4:0] buf_num;

  task body();
    if (setup) begin
      // Choose a buffer to receive our packet.
      setup_buffer_id = buf_num;
      // Configure support for SETUP transactions.
      configure_setup_trans(ep_default);
      // Send SETUP packet.
      send_prnd_setup_packet(ep_default);
    end else begin
      // Choose a buffer to receive our packet.
      out_buffer_id = buf_num;
      // Configure support for OUT transactions.
      configure_out_trans(ep_default);
      // Send OUT packet.
      send_prnd_out_packet(ep_default, PidTypeData0, .randomize_length(1'b1), .num_of_bytes(0));
    end

    // Check that the USB device received a packet with the expected properties.
    check_pkt_received(ep_default, setup, buf_num, m_data_pkt.data);
  endtask
endclass : usbdev_av_buffer_vseq
