// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// usbdev_pkt_received test vseq
class usbdev_pkt_received_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_pkt_received_vseq)

  `uvm_object_new

  task body();
    // Expected data content of packet
    byte unsigned exp_data[];

    // Configure transaction
    configure_out_trans();
    // Enable pkt_received interrupt
    ral.intr_enable.pkt_received.set(1'b1);
    csr_update(ral.intr_enable);

    // Out token packet followed by a data packet
    call_token_seq(PidTypeOutToken);
    cfg.clk_rst_vif.wait_clks(10);
    call_data_seq(PidTypeData0, .randomize_length(1'b1), .num_of_bytes(0));
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_out_response_from_device(m_usb20_item, PidTypeAck);

    recover_orig_data(m_data_pkt.data, exp_data);
    // Check that the USB device received a packet with the expected properties.
    check_pkt_received(endp, 0, out_buffer_id, exp_data);
  endtask

  // TODO: Presently the act of sending a data packet, destructively modifies it!
  // Restore the data packet to its original state. This just bit-reverses each byte
  // within the input array.
  function void recover_orig_data(input byte unsigned in[], output byte unsigned out[]);
    out = {<<8{in}};  // Reverse the order of the bytes
    out = {<<{out}};  // Bit-reverse everything
  endfunction

endclass
