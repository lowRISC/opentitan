// Copyright lowRISC contributors.
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
    // Expected data content of packet
    byte unsigned exp_data[];

    // Configure out transaction
    configure_out_trans();
    // Out token packet followed by a data packet of random bytes
    call_token_seq(PidTypeOutToken);
    cfg.clk_rst_vif.wait_clks(20);
    call_data_seq(PidTypeData0, .randomize_length(randomize_length), .num_of_bytes(num_of_bytes));
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    get_out_response_from_device(m_usb20_item, PidTypeAck);
    cfg.clk_rst_vif.wait_clks(20);

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
