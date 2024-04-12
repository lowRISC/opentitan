// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Transmit a stream of maximum length packets to the DUT, aiming to achieve maximal 'Bit Stuffing'
// throughout at least some of those OUT packets. This is difficult to guarantee because of the
// interaction between the data bytes and the CRC16 that checksums those bits.
//
// This may be used as the basis for testing the rx sampling under conditions of worst case phase
// and maximal frequency delta.
class usbdev_stream_len_max_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_stream_len_max_vseq)

  `uvm_object_new

  // Remember the current state of the Data Toggle bit for the selected OUT endpoint.
  bit data_tog = 0;

  virtual task transmit_out_packets(int unsigned num_packets);
    byte unsigned data[$];
    `uvm_info(`gfn, $sformatf("Transmitting %d max length OUT packets", num_packets), UVM_MEDIUM)
    // To achieve the maximum length of OUT packet we just emit a lot of '1' bits to ensure that
    // maximal bit stuffing occurs. Although bit stuffing is active throughout the DATA0 PID
    // and the CRC16 too, it seems as though the maximum packet length is 614 bits and this is
    // achieved with a simple sequence of 0xff bytes, yielding a CRC16 of 0x40fe.
    for (int unsigned idx = 0; idx < MaxPktSizeByte; idx++) begin
      data.push_back(8'hFF);
    end
    for (int unsigned txn = 0; txn < num_packets; txn++) begin
      // TODO: perhaps we want to collect and check the packets in another process?
      // This would stop the CSR/buffer accesses from affecting the USB traffic timing, which
      // could be important in exercising all freq/phase extremes.
      send_out_packet(ep_default, data_tog ? PidTypeData1 : PidTypeData0, data);
      check_response_matches(PidTypeAck);
      inter_packet_delay();
      data_tog ^= 1;

      // Check that the USB device received a packet with the expected properties.
      check_pkt_received(ep_default, 0, out_buffer_id, m_data_pkt.data);
      // Return the OUT buffer for reuse.
      csr_wr(.ptr(ral.avoutbuffer.buffer), .value(out_buffer_id));
    end
  endtask

  virtual task body();
    // Set up an endpoint to receive OUT packets.
    configure_out_trans(ep_default);

    transmit_out_packets(num_trans);
  endtask

endclass : usbdev_stream_len_max_vseq
