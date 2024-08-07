// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_iso_retraction_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_iso_retraction_vseq)

  `uvm_object_new

  constraint num_trans_c {
    num_trans inside {[64:256]};
  }

  // Packets retrieved, from the perspective of the host side.
  bit pkts_rcvd[];
  // Packets sent, from the perspective of the device side.
  bit pkts_sent[];

  // Indication that the device side has completed.
  bit complete = 1'b0;

  // Choose min/max delays to try to ensure a good probability of collisions between host-side
  // collection attempts and device-side retractions.
  // We used max length packets, which take ca. 4 x 550-700 clock ticks to transmit.
  int unsigned min_delay = 320;
  int unsigned max_delay = 3200;

  // Host side collected IN packets until instructed to stop.
  task host_side();
    int prev_seq = -1;
    do begin
      // TODO: experiment/justify. See #23932.
      int unsigned delay = $urandom_range(1, max_delay - min_delay);
      usb20_item reply;
      // Randomized delay, to ensure that we miss some of the packets.
      // TODO: we should really be using the host clock here; see #23932.
      cfg.clk_rst_vif.wait_clks(delay);
      // Isochronous packets are not ACKnowledged.
      retrieve_in_packet(ep_default, reply, .ack(1'b0));
      `DV_CHECK_EQ(reply.m_ev_type, EvPacket)
      case (reply.m_pid_type)
        PidTypeData0, PidTypeData1: begin
          // Packets shall arrive in order, because it's a single endpoint.
          data_pkt data;
          $cast(data, reply);
          // Isochronous endpoints without pending data shall return a Zero Length Packet, because
          // there is no handshake mechanism and a response must be returned to the USB host.
          if (data.data.size() > 0) begin
            bit [31:0] seq;
            `DV_CHECK_EQ(data.data.size, MaxPktSizeByte)
            seq = {data.data[3], data.data[2], data.data[1], data.data[0]};
            `uvm_info(`gfn, $sformatf("Retrieved IN packet (seq %0d)", seq), UVM_MEDIUM)
            `DV_CHECK_GT(int'(seq), prev_seq)
            `DV_CHECK_LT(seq, num_trans)
            pkts_rcvd[seq] = 1'b1;
            prev_seq = seq;
          end
        end
        // Since we deal only with Isochronous endpoints presently, we should always get a DATA
        // packet in response.
        default: `uvm_fatal(`gfn, "Unexpected response")
      endcase
    end while (!complete);
  endtask

  // Introduce a random delay on the device side before attempting to present a new packet
  // (and thus possibly retracting its predecessor).
  task device_rand_delay();
    int unsigned delay = $urandom_range(min_delay, max_delay);
    cfg.clk_rst_vif.wait_clks(delay);
  endtask

  // Record a verdict on whether the previous packet was successfully sent (ie. not retracted),
  // and release its associated buffer for reuse.
  function void device_pkt_verdict(int prev_seq, int prev_buf, bit retracted,
                                   int unsigned retracted_buf);
    // Was a packet retracted?
    if (retracted) begin
      // Just check that it was the buffer we last supplied.
      `DV_CHECK_EQ(retracted_buf, prev_buf)
      `uvm_info(`gfn, $sformatf(" - seq %0d retracted", prev_seq), UVM_MEDIUM)
    end else if (prev_seq >= 0) begin
      `uvm_info(`gfn, $sformatf(" - seq %0d sent", prev_seq), UVM_MEDIUM)
      pkts_sent[prev_seq] = 1'b1;
    end
    // Release the buffer holding the previous packet, so that we don't run out of available
    // buffers.
    if (prev_buf >= 0) begin
      `uvm_info(`gfn, $sformatf(" - releasing buffer %0d", prev_buf), UVM_MEDIUM)
      buf_release(prev_buf);
    end
  endfunction

  // Device side presents IN packets for collection; if a packet has not been collected then it
  // will be retracted when the next is presented.
  task device_side();
    int unsigned retracted_buf;
    uvm_reg_data_t configin;
    int prev_seq = -1;
    int prev_buf = -1;
    bit retracted;
    int seq = 0;

    repeat (num_trans) begin
      byte unsigned pkt_data[$];
      int unsigned nwords;
      int buf_num;

      // Collect and populate a buffer; we use the sequence number as the packet content so that
      // the host side can identify which packet it has collected.
      buf_num = buf_alloc();
      `DV_CHECK_GE(buf_num, 0, "No buffer available")

      // Repeat the sequence number throughout the buffer to create a longer packet.
      // TODO: investigate whether there's any benefit to varying this. See #23932.
      nwords = MaxPktSizeByte / 4;
      repeat (nwords) begin
        bit [31:0] pkt_seq = seq;
        repeat (4) begin
          pkt_data.push_back(pkt_seq[7:0]);
          pkt_seq >>= 8;
        end
      end
      write_buffer(buf_num, pkt_data);

      // After a randomized short delay, present the new IN packet for collection; we may or may
      // not thus be required to retract and replace the previous IN packet.
      device_rand_delay();
      `uvm_info(`gfn, $sformatf("Presenting IN packet (seq %0d) via buf %0d", seq, buf_num),
                UVM_MEDIUM)
      present_in_packet(ep_default, buf_num, pkt_data.size(), .may_retract(1'b1),
                        .retracted(retracted), .retracted_buf(retracted_buf));
      device_pkt_verdict(prev_seq, prev_buf, retracted, retracted_buf);

      // Remember properties of this presented IN packet.
      prev_buf = buf_num;
      prev_seq = seq;
      // Next packet.
      seq++;
    end

    // We must reach a verdict on the final packet that we presented.
    device_rand_delay();
    csr_rd(.ptr(ral.configin[ep_default]), .value(configin));
    if (get_field_val(ral.configin[0].rdy, configin)) begin
      bit sent, pend;
      retract_in_packet(ep_default, configin, sent, pend, retracted, retracted_buf);
    end else retracted = 1'b0;
    device_pkt_verdict(prev_seq, prev_buf, retracted, retracted_buf);

    // We have now reached a verdict on all the packets that we have tried to send.
    complete = 1'b1;
  endtask

  virtual task body();
    // Initialize buffer allocation.
    buf_init();

    // Size the packets sent and packets received bitmaps appropriately; all bits are initially
    // reset, indicating that the corresponding packet has neither been sent not received.
    pkts_rcvd = new [num_trans];
    pkts_sent = new [num_trans];

    // Enable endpoint for IN traffic.
    csr_wr(.ptr(ral.ep_in_enable[0].enable[ep_default]),  .value(1'b1));
    csr_wr(.ptr(ral.in_iso[0].iso[ep_default]), .value(1'b1));

    fork
      host_side();
      device_side();
    join

    // Check that the two parties agree on which packets were actually transferred successfully.
    `uvm_info(`gfn, $sformatf("device side sent   %p", pkts_sent), UVM_LOW)
    `uvm_info(`gfn, $sformatf("host side received %p", pkts_rcvd), UVM_LOW)
    for (int unsigned seq = 0; seq < num_trans; seq++) begin
      if (pkts_sent[seq] != pkts_rcvd[seq]) begin
        `uvm_info(`gfn, $sformatf("mismatched seq %0d - sent %0d rcvd %0d", seq,
                                  pkts_sent[seq], pkts_rcvd[seq]), UVM_MEDIUM)
      end
    end
    if (pkts_rcvd != pkts_sent) `uvm_fatal(`gfn, "Device- and host-side do not agree")

    // Deactivate the DUT.
    usbdev_disconnect();
    csr_wr(.ptr(ral.in_iso[0].iso[ep_default]), .value(1'b0));
    csr_wr(.ptr(ral.ep_in_enable[0].enable[ep_default]), .value(1'b0));
  endtask
endclass : usbdev_iso_retraction_vseq
