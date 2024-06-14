// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_setup_priority_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_setup_priority_vseq)

  `uvm_object_new

  // Properties of a received packet.
  typedef struct {
    bit [3:0] ep;
    bit       setup;
    byte unsigned data[];
  } rx_packet_t;

  // Queue of expected received packets, for subsequent checking.
  rx_packet_t exp_rx[$];

  // Check that the RX FIFO contains the expected number of packet descriptions.
  task check_rx_level(int unsigned exp_level);
    uvm_reg_data_t act_level;
    csr_rd(.ptr(ral.usbstat.rx_depth), .value(act_level));
    `DV_CHECK_EQ(act_level, exp_level, "RX FIFO does not have expected level")
  endtask

  // Retain the packet properties for subsequent checking.
  function retain_packet(bit [3:0] ep, bit setup, ref byte unsigned data[]);
    rx_packet_t rx;
    // The randomized packet data that was transmitted to the DUT.
    rx.ep = ep;
    rx.setup = setup;
    rx.data = data;
    `uvm_info(`gfn, $sformatf("Retaining packet ep %d setup %d data %p", rx.ep, rx.setup, rx.data),
              UVM_MEDIUM)
    exp_rx.push_back(rx);
  endfunction

  task body();
    int unsigned depth = RxFIFODepth;
    bit data_toggle = 0;
    uvm_reg_data_t level;

    // Initialize the buffer tracking.
    buf_init();

    // Configure the USB device to receive SETUP packets on Endpoint Zero.
    // Place 1 buffer in the Available SETUP Buffer FIFO.
    configure_setup_trans(0);
    // Configure endpoint 1 to receive OUT DATA packets.
    configure_out_trans(1);
    // Place a further 7 data buffers in the Available OUT Buffer FIFO.
    for (int unsigned i = 0; i < depth - 1; i++) begin
      int buf_num = buf_alloc();
      `DV_CHECK_GE(buf_num, 0)
      csr_wr(.ptr(ral.avoutbuffer), .value(buf_num));
    end
    // Transmit 7 OUT DATA packets to endpoint 1, checking that each packet is
    // ACKed, but do not read from Rx FIFO.
    for (int unsigned i = 0; i < depth - 1; i++) begin
      // Observe correct data toggling.
      send_prnd_out_packet(1, data_toggle ? PidTypeData1 : PidTypeData0);
      check_response_matches(PidTypeAck);
      data_toggle = !data_toggle;
      retain_packet(.ep(1), .setup(0), .data(m_data_pkt.data));
    end
    // Check that the Rx FIFO contains 7 buffers.
    check_rx_level(depth - 1);
    // Transmit 1 OUT DATA packet to endpoint 1.
    send_prnd_out_packet(1, data_toggle ? PidTypeData1 : PidTypeData0);
    // Verify that the OUT DATA packet is NAKed as expected; we don't retain this one because
    // the DUT should not have stored it.
    check_response_matches(PidTypeNak);
    // Check that the Rx FIFO depth is still 7.
    check_rx_level(depth - 1);
    // Transmit a SETUP DATA packet to Endpoint Zero, checking that the packet is ACKed.
    send_prnd_setup_packet(0);
    retain_packet(.ep(0), .setup(1), .data(m_data_pkt.data));
    check_response_matches(PidTypeAck);
    // Check that the Rx FIFO depth is now 8.
    check_rx_level(depth);
    // Read the packets from the Rx FIFO, checking the properties of each of the 7 OUT
    // DATA packets and the final 1 SETUP DATA packet in turn.
    for (int unsigned i = 0; i < depth; i++) begin
      // Collect the expected packet properties.
      rx_packet_t rx = exp_rx.pop_front();
      check_rx_packet(rx.ep, rx.setup, .exp_buffer_id(0), .exp_byte_data(rx.data),
                      .buffer_known(0));
    end
  endtask
endclass : usbdev_setup_priority_vseq
