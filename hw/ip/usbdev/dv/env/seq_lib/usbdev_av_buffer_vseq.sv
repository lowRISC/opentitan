// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// usbdev_av_buffer test vseq
class usbdev_av_buffer_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_av_buffer_vseq)

  `uvm_object_new

  usb20_item      item;
  RSP             rsp_item;

  task body();
    // Configure support for OUT transaction
    configure_out_trans(ep_default);
    // Out token packet followed by a data packet of 8 bytes
    send_prnd_out_packet(ep_default, PidTypeData0, .randomize_length(1'b0), .num_of_bytes(8));
    get_response(rsp_item);
    $cast(item, rsp_item);
    item.check_pid_type(PidTypeAck);

    // Check that the USB device received a packet with the expected properties.
    check_pkt_received(ep_default, 0, out_buffer_id, m_data_pkt.data);
  endtask

endclass
