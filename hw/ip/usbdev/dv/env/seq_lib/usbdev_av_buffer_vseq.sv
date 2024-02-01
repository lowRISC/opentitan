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
    // Configure transaction
    configure_trans();
    // Out token packet followed by a data packet of 8 bytes
    call_token_seq(PidTypeOutToken);
    cfg.clk_rst_vif.wait_clks(20);
    call_data_seq(PidTypeData0, .randomize_length(1'b0), .num_of_bytes(8));
    get_response(rsp_item);
    $cast(item, rsp_item);
    get_out_response_from_device(item, PidTypeAck);
    cfg.clk_rst_vif.wait_clks(20);

    // Check that the USB device received a packet with the expected properties.
    check_pkt_received(endp, 0, out_buffer_id, m_data_pkt.data);
  endtask

  task configure_trans();
    // Enable EP0 Out
    csr_wr(.ptr(ral.ep_out_enable[0].enable[endp]), .value(1'b1));
    csr_update(ral.ep_out_enable[0]);
    // Enable rx out
    ral.rxenable_out[0].out[endp].set(1'b1);
    csr_update(ral.rxenable_out[0]);
    // Set buffer
    csr_wr(.ptr(ral.avoutbuffer.buffer), .value(out_buffer_id));
  endtask

endclass
