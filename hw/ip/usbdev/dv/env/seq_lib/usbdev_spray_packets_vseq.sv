// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Spray IN/OUT/SETUP packets at a selection of device addresses and endpoints, and check that only
// the expected packets are received, with all other packets being ignored. Reasons for packets
// being ignored are:
//
// - device address does not match.
// - endpoint number is invalid.
// - endpoint is not enabled for this type of traffic.
// - endpoint is stalled.
//
// That certain packets are ignored is checked simply by collecting the packets that we expect to be
// received and comparing them exactly and in-order against those that the DUT actually collects.
//
// From this sequence may be derived other simple sequences that contrain the endpoint configuration
// and/or target properties (eg. device address, endpoint number).

class usbdev_spray_packets_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_spray_packets_vseq)

  `uvm_object_new

  // Types of transaction that we may perform.
  typedef enum bit [1:0] {
    TxnType_SETUP,
    TxnType_IN,
    TxnType_OUT
  } txn_type_e;

  // Chosen configuration of DUT.
  rand bit [NEndpoints-1:0] ep_out_enable;
  rand bit [NEndpoints-1:0] ep_in_enable;
  rand bit [NEndpoints-1:0] out_stall;
  rand bit [NEndpoints-1:0] in_stall;
  rand bit [NEndpoints-1:0] rxenable_setup;
  rand bit [NEndpoints-1:0] rxenable_out;

  // Does the specified endpoint accept the given type of transaction?
  virtual function bit endpoint_accepts(bit [3:0] ep, txn_type_e txn_type);
    // Non-extant endpoints shall simply ignore all traffic.
    if (ep >= NEndpoints) return 0;
    case (txn_type)
      // SETUP transactions shall never return STALL, so we ignore 'out_stall' here.
      TxnType_SETUP: return (ep_out_enable[ep] & rxenable_setup[ep]);
      TxnType_IN:    return (ep_in_enable[ep]  & !in_stall[ep]);
      // We're slightly biased in favor of OUT packets, but that's a good choice really.
      default:       return (ep_out_enable[ep] & !out_stall[ep] & rxenable_out[ep]);
    endcase
  endfunction

  // Is the specified endpoint stalled for the given type of transaction?
  virtual function bit endpoint_stalled(bit [3:0] ep, txn_type_e txn_type);
    // Non-extant endpoints shall simply ignore all traffic, not return STALL handshakes.
    if (ep >= NEndpoints) return 0;
    case (txn_type)
      // SETUP transactions shall never return STALL as a response.
      TxnType_SETUP: return 1'b0;
      TxnType_IN:    return (ep_in_enable[ep]  &  in_stall[ep]);
      // We're slightly biased in favor of OUT packets, but that's a good choice really.
      default:       return (ep_out_enable[ep] & out_stall[ep]);
    endcase
  endfunction

  // To be overridden by any child sequence that wishes to constrain the configuration.
  virtual function void choose_config();
    // Use randomized configuration without further constraints.
  endfunction

  rand bit [6:0] target_addr;
  rand bit [3:0] target_ep;
  rand bit [1:0] txn_type;

  // Expectation of Data Toggle bits; required to guarantee delivery as expected.
  bit [NEndpoints-1:0] exp_out_toggles;
  bit [NEndpoints-1:0] exp_in_toggles;

  // Decide upon the target device address and endpoint for this transaction, and the type of
  // transaction.
  // To be overridden by any child sequence that wishes to constrain the choice of target, endpoint
  // and/or transaction type, and/or constraints may be added to their randomization.
  virtual function void choose_target();
    `DV_CHECK_STD_RANDOMIZE_FATAL(target_addr)
    `DV_CHECK_STD_RANDOMIZE_FATAL(target_ep)
    `DV_CHECK_STD_RANDOMIZE_FATAL(txn_type)
  endfunction

  // Keep a single buffer for use with IN transactions.
  rand bit [4:0] in_buf;

  // Ensure that there is at least one buffer in the specified 'Available Buffer' FIFO so that
  // packet reception may occur.
  task ensure_buffer_avail(bit [3:0] ep, txn_type_e txn_type);
    uvm_reg_data_t level;
    case (txn_type)
      TxnType_IN: begin
        // Nothing to do here for IN transactions.
      end
      TxnType_SETUP: begin
        // Do we need to supply a buffer?
        csr_rd(.ptr(ral.usbstat.av_setup_depth), .value(level));
        if (!level) begin
          int buf_num = buf_alloc();
          `DV_CHECK_GE(buf_num, 0, "Buffers exhausted")
          csr_wr(.ptr(ral.avsetupbuffer), .value(buf_num));
        end
      end
      // We're slightly biased in favor of OUT packets, but that's a good choice really;
      default: begin
        // Do we need to supply a buffer?
        csr_rd(.ptr(ral.usbstat.av_out_depth), .value(level));
        if (!level) begin
          int buf_num = buf_alloc();
          `DV_CHECK_GE(buf_num, 0, "Buffers exhausted")
          csr_wr(.ptr(ral.avoutbuffer), .value(buf_num));
        end
      end
    endcase
  endtask

  task transaction_in(bit acceptable, bit stall_expected, ref byte unsigned data[$],
                      output bit rx_expected);
    usb20_item response;
    if (target_ep < NEndpoints) begin
      // configin[x] register has already been programmed with the buffer, so we use it here
      // and complete the packet description...
      uvm_reg_data_t configin;
      csr_rd(.ptr(ral.configin[target_ep]), .value(configin));
      // ...now populate the buffer itself and then present the packet for collection.
      write_buffer(in_buf, data);
      ral.configin[target_ep].buffer.set(in_buf);
      ral.configin[target_ep].size.set(data.size());
      ral.configin[target_ep].rdy.set(1'b1);
      csr_update(ral.configin[target_ep]);
    end
    // An IN transaction shall be tested immediately, and we shall ACKnowledge any DATA packet
    // that is received.
    send_token_packet(target_ep, PidTypeInToken, target_addr);
    if (acceptable) begin
      check_in_packet(exp_in_toggles[target_ep] ? PidTypeData1 : PidTypeData0, data);
      send_handshake(PidTypeAck);
      // Advance our DATA toggle.
      exp_in_toggles[target_ep] ^= 1'b1;
    end else if (stall_expected) check_response_matches(PidTypeStall);
    else check_no_response();
    rx_expected = 0;
  endtask

  task transaction_setup(bit acceptable, bit stall_expected, ref byte unsigned data[$],
                         output bit rx_expected);
    // This sequence is constructed such that any acceptable packet shall be received; we've
    // ensured the availability of a suitable buffer.
    rx_expected = acceptable;
    send_setup_packet(target_ep, data, target_addr);
    // DATA toggles are reset upon receipt of the SETUP token, whether or not the DATA packet
    // is received.
    if (target_addr == dev_addr && target_ep < NEndpoints) begin
      // SETUP packet carries DATA0 and the IN side is updated too.
      // Note: the IN Data Toggle is set in anticipation of successful receipt.
      if (ep_out_enable[target_ep]) exp_out_toggles[target_ep] = 1'b0;
      if (ep_in_enable[target_ep])  exp_in_toggles[target_ep]  = 1'b1;
    end
    // An unacceptable SETUP transaction should yield either a STALL or no response.
    if (rx_expected) begin
      // Acceptable SETUP packets shall aways be received, never ignored.
      check_response_matches(PidTypeAck);
      // A SETUP packet successfully received clears the stall conditions.
      out_stall[target_ep] = 1'b0;
      in_stall[target_ep]  = 1'b0;
      exp_out_toggles[target_ep] ^= 1'b1;
    end else if (stall_expected) check_response_matches(PidTypeStall);
    else check_no_response();
  endtask

  task transaction_out(bit acceptable, bit stall_expected, ref byte unsigned data[$],
                       output bit rx_expected);
    pid_type_e pid = exp_out_toggles[target_ep] ? PidTypeData1 : PidTypeData0;
    // This sequence is constructed such that any acceptable packet shall be received; we've
    // ensured the availability of a suitable buffer.
    rx_expected = acceptable;
    send_out_packet(target_ep, pid, data, 1'b0, target_addr);
    // An unacceptable OUT response may yield a NAK (rxenable_out not set), STALL or simply
    // no response.
    if (rx_expected) begin
      // If we're expecting the packet to be received it shall always be accepted immediately
      // in this sequence; a NAK through lack of resources would break the logic.
      check_response_matches(PidTypeAck);
      exp_out_toggles[target_ep] ^= 1'b1;
    end else if (stall_expected) check_response_matches(PidTypeStall);
    else begin
      if (target_addr == dev_addr && target_ep < NEndpoints && ep_out_enable[target_ep]) begin
        // Configuration (rxenable_out) prevents the packet being received.
        check_response_matches(PidTypeNak);
      end else check_no_response();
    end
  endtask

  // Description of an expected received packet.
  typedef struct {
    bit [4:0]     ep;
    bit           setup;
    byte unsigned data[];
  } rx_packet_t;

  // The set of packets that we expect to be received.
  rx_packet_t exp_rx[$];

  // Actual number of packets received.
  int unsigned rx_cnt;

  // Collect and check received packets until the RX FIFO level is no more than the specified
  // maximum.
  task collect_rx_packets(int unsigned max_depth, ref int unsigned rx_cnt);
    uvm_reg_data_t rx_depth;
    csr_rd(.ptr(ral.usbstat.rx_depth), .value(rx_depth));
    while (rx_depth > max_depth) begin
      uvm_reg_data_t rx_fifo_read;
      bit [4:0] act_buffer_id;

      `DV_CHECK_GT(exp_rx.size(), 0, "RX FIFO has a packet but none expected")
      // Read RX FIFO entry here because we need to retain the number of the buffer that was used.
      csr_rd(.ptr(ral.rxfifo), .value(rx_fifo_read));
      act_buffer_id = get_field_val(ral.rxfifo.buffer, rx_fifo_read);
      // Check the properties and content of the received packet, observing that we do not know
      // into which buffer the packet will have been received.
      check_rxfifo_packet(exp_rx[0].ep, exp_rx[0].setup, exp_rx[0].data, rx_fifo_read);
      void'(exp_rx.pop_front());
      rx_cnt++;
      // Release the buffer that was used.
      buf_release(act_buffer_id);
      // Read the new level.
      csr_rd(.ptr(ral.usbstat.rx_depth), .value(rx_depth));
    end
  endtask

  virtual task body();
    // Expected count of received packets.
    int unsigned exp_rx_cnt = 0;
    // Count of received packets.
    rx_cnt = 0;

    // Initially mark all buffers as available for use, except the one that we have chosen to use
    // for IN transactions.
    buf_init();
    buf_claim(in_buf);

    // Choose endpoint configuration for this sequence.
    choose_config();

    // Configure the DUT.
    csr_wr(.ptr(ral.ep_out_enable[0]), .value(ep_out_enable));
    csr_wr(.ptr(ral.ep_in_enable[0]), .value(ep_in_enable));
    csr_wr(.ptr(ral.out_stall[0]), .value(out_stall));
    csr_wr(.ptr(ral.in_stall[0]), .value(in_stall));
    csr_wr(.ptr(ral.rxenable_setup[0]), .value(rxenable_setup));
    csr_wr(.ptr(ral.rxenable_out[0]), .value(rxenable_out));

    // Report endpoint configuration for diagnostic purposes.
    `uvm_info(`gfn, $sformatf("ep_out_enable 0x%3x out_stall 0x%3x rxenable_out 0x%3x",
                              ep_out_enable, out_stall, rxenable_out), UVM_MEDIUM)
    `uvm_info(`gfn, $sformatf("ep_in_enable 0x%3x in_stall 0x%3x rxenable_setup 0x%3x",
                              ep_in_enable, in_stall, rxenable_setup), UVM_MEDIUM)

    // Each transaction is a single packet that may or may not be received.
    for (int unsigned txn = 0; txn < num_trans; txn++) begin
      uvm_reg_data_t rx_depth;
      byte unsigned data[$];
      bit stall_expected = 0;
      bit rx_expected = 0;
      bit acceptable = 0;

      // This chooses the target and type of this transaction.
      choose_target();
      `uvm_info(`gfn, $sformatf("Txn %0x: type %x address 0x%x ep 0x%x", txn, txn_type, target_addr,
                                target_ep), UVM_MEDIUM)

      // Make sure there is a buffer available in the appropriate FIFO or available for collection.
      ensure_buffer_avail(target_ep, txn_type_e'(txn_type));

      // Do we expect the DUT to accept this transaction?
      if (target_addr == dev_addr) begin
        // STALL response takes priority over the availability of resources required to accept a
        // packet.
        stall_expected = endpoint_stalled(target_ep, txn_type_e'(txn_type));
        // Check the endpoint configuration to see whether this transaction type shall be ignored.
        if (endpoint_accepts(target_ep, txn_type_e'(txn_type))) begin
          // The endpoint accepts this transaction, so OUT/SETUP should be received.
          acceptable = 1;
        end
      end
      `uvm_info(`gfn, $sformatf("acceptable %d stall_expected %d", acceptable, stall_expected),
                UVM_MEDIUM)

      // The packet contents encode the properties of the transaction, so that we can match up the
      // received packet with the transaction; the contents of the packet are not significant to
      // the test but they are very useful diagnostically.
      data.push_back(txn[7:0]);
      data.push_back(txn[15:8]);
      data.push_back(txn[23:16]);
      data.push_back(txn[31:24]);
      data.push_back(target_addr);
      data.push_back(target_ep);
      data.push_back(txn_type);

      // Perform this transaction.
      case (txn_type)
        TxnType_IN:    transaction_in(acceptable, stall_expected, data, rx_expected);
        TxnType_SETUP: transaction_setup(acceptable, stall_expected, data, rx_expected);
        // We're slightly biased in favor of OUT packets, but that's a good choice really.
        default:       transaction_out(acceptable, stall_expected, data, rx_expected);
      endcase

      // Remember the properties of the packet iff we're expecting it to be received.
      `uvm_info(`gfn, $sformatf("rx_expected = %d", rx_expected), UVM_MEDIUM)
      if (rx_expected) begin
        rx_packet_t rx;
        rx.ep = target_ep;
        rx.setup = (txn_type == TxnType_SETUP);
        rx.data = data;
        // Retain packet properties and content.
        exp_rx.push_back(rx);
        exp_rx_cnt++;
      end

      // We MUST collect at least one packet now if we expect the RX FIFO to have become full,
      // which from the perspective of OUT packets means 'depth - 1' because the final entry is
      // reserved exclusively for SETUP packets.
      collect_rx_packets(RxFIFODepth - 2, rx_cnt);
    end

    // Ensure that all packets have been collected and checked.
    collect_rx_packets(0, rx_cnt);

    buf_release(in_buf);

    // Check that there are no outstanding packets.
    `DV_CHECK_EQ(exp_rx.size(), 0, "Outstanding packets not received as expected")
    `DV_CHECK_EQ(rx_cnt, exp_rx_cnt, "Mismatch in number of received packets")
  endtask
endclass : usbdev_spray_packets_vseq
