// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_bad_traffic_vseq extends usbdev_bus_rand_vseq;
  `uvm_object_utils(usbdev_bad_traffic_vseq)

  `uvm_object_new

  // Number of types of bad traffic events.
  localparam int unsigned NEventTypes = 6;

  // Configuration switches; each controls whether a particular type of bad traffic may be
  // generated within this test.
  //
  // Note: these are typed as 'int unsigned' rather than bit to permit the use of 'randcase' as a
  //       selection without explicit widening, and we can adjust the weightings of the individual
  //       stimuli in the test configuration.
  int unsigned wt_bad_syncs = 0;
  int unsigned wt_bad_pids = 0;
  int unsigned wt_spurious_pids = 0;
  int unsigned wt_bad_crc5 = 0;
  int unsigned wt_bad_crc16 = 0;
  int unsigned wt_bitstuff_errs = 0;

  // Generate invalid SYNC signaling on the token packet and/or the data packet of an OUT
  // transaction to the chosen endpoint.
  virtual task generate_bad_sync(bit [3:0] ep);
    int unsigned corrupt = $urandom_range(1, 3);  // bit 1 = corrupt data, bit 0 = corrupt out.
    `uvm_info(`gfn, "Generating transaction with invalid SYNC", UVM_MEDIUM)
    claim_driver();
    // See explanation in `usb20_agent_cfg.sv` => choose an invalid Endpoint so that we do not
    // interfere with valid traffic.
    if (cfg.m_usb20_agent_cfg.rtl_limited_sync_recovery) begin
      ep = $urandom_range(NEndpoints, 15);
      `uvm_info(`gfn, $sformatf(" => redirecting as valid traffic to invalid endpoint %0d", ep),
                UVM_MEDIUM)
    end
    // Instruct the driver to scramble one or both of the SYNC signals.
    inject_invalid_token_sync = corrupt[0];
    inject_invalid_data_sync  = corrupt[1];
    send_prnd_out_packet(ep, exp_out_toggle[ep] ? PidTypeData1 : PidTypeData0);
    check_no_response();
    // Reinstate normal operation.
    inject_invalid_token_sync = 1'b0;
    inject_invalid_data_sync  = 1'b0;
    release_driver();
  endtask

  typedef enum {
    // Spurious Packet IDentifiers (token packets and handshake packets).
    SpuriousData2, // DATA2 is High-Speed.
    SpuriousMData, // MDATA is High-Speed.
    SpuriousStall, // STALL shall not be received by DUT; ignore.
    SpuriousNyet,  // NYET is High-Speed.
    SpuriousErr, // ERR PID is unused by DUT.
    SpuriousSplit, // SPLIT is a High-Speed Transaction Token.
    SpuriousPing, // The PING protocol is High-Speed.
    // Spurious DATA packets without a preceding OUT/SETUP token packet.
    SpuriousData0,
    SpuriousData1
  } spurious_pid_e;

  // Generate spurious Packet IDenfifiers that the device shall ignore.
  virtual task generate_spurious_pid(bit [3:0] ep);
    // Token packets that the DUT should ignore
    spurious_pid_e pid;
    bit [7:0] bad_pid;
    // TODO: With the usb20_monitor now able to decode valid low speed traffic, it has no reliable
    // way to differentiate between the spurious PRE tokens generated here and the valid, intended
    // use of PRE tokens; the 'hub setup' interval is indistinguishable from some token packets
    // (it depends upon the target address).
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(pid, pid != SpuriousErr;)
    `uvm_info(`gfn, $sformatf("Generating spurious PID type %0d", pid), UVM_MEDIUM)
    claim_driver();
    case (pid)
      // Data packets that should be sent only to High-Speed devices.
      SpuriousData2, SpuriousMData: begin
        pid_type_e bad_pid = (pid == SpuriousMData) ? PidTypeMData : PidTypeData2;
        send_prnd_out_packet(ep, bad_pid);
        check_no_response();
      end
      // Spurious/unused handshake PIDs; usb20_driver does not produce a response to handshake
      // sequence items.
      SpuriousStall: send_handshake(PidTypeStall);
      SpuriousNyet: send_handshake(PidTypeNyet);
      // Spurious token packets.
      SpuriousSplit, SpuriousPing, SpuriousErr: begin
        pid_type_e bad_pid = (pid == SpuriousSplit) ? PidTypeSplit :
                            ((pid == SpuriousPing)  ? PidTypePing  : PidTypePre); // PRE == ERR.
        send_token_packet(ep, pid_type_e'(bad_pid));
        // usb20_driver does not produce a response to token packet sequence items, so don't
        // await a response.
      end
      SpuriousData0, SpuriousData1: begin
        pid_type_e bad_pid = (pid == SpuriousData1) ? PidTypeData1 : PidTypeData0;
        send_prnd_data_packet(pid_type_e'(bad_pid));
        check_no_response();
      end
      default: `uvm_fatal(`gfn, $sformatf("Unexpected/invalid selection %0d", pid))
    endcase
    release_driver();
  endtask

  // Generate a SETUP/OUT transaction to the DUT with invalid Packet IDentifier(s).
  virtual task generate_bad_pid(bit [3:0] ep);
    bit [7:0] setup_out_pid, data_pid;
    bit is_setup;
    build_prnd_bad_pids(is_setup, setup_out_pid, data_pid);
    `uvm_info(`gfn, $sformatf("Generating bad PID(s) %0x,%0x (SETUP-based %0d)", setup_out_pid,
                              data_pid, is_setup), UVM_MEDIUM)
    // Since the SETUP/OUT PID and/or the DATA PID has been corrupted, the entire packet should be
    // ignored.
    claim_driver();
    // If we send a valid SETUP token packet the DUT will reset its Data Toggle bits, so we need to
    // reset our expectations too.
    if (setup_out_pid == PidTypeSetupToken) begin
      // In this case we shall not be sending a valid DATA0 packet, so we expect the OUT endpoint
      // still be awaiting DATA0, but the IN side will have a set toggle bit.
      exp_out_toggle[ep] = 1'b0;
      exp_in_toggle[ep] = 1'b1;
    end
    send_token_packet(ep, pid_type_e'(setup_out_pid));
    inter_packet_delay();
    send_prnd_data_packet(pid_type_e'(data_pid));
    check_no_response();
    release_driver();
    // TODO: Check that a PID error interrupt is raised by the DUT?
  endtask

  // Transmit a SETUP token packet, an IN token packet or an OUT token packet with an invalid CRC5.
  virtual task generate_bad_crc5(bit [3:0] ep);
    int unsigned pkt_type = $urandom_range(0, 2);
    `uvm_info(`gfn, $sformatf("Generating bad CRC5 token packet type %0d", pkt_type), UVM_MEDIUM)
    claim_driver();
    // Ensure that the CRC5 value is incorrect; this should prevent the DUT responding to the
    // (apparent) SETUP token packet.
    inject_bad_token_crc5 = 1'b1;
    case (pkt_type)
      0: begin
        send_prnd_setup_packet(ep);
        check_no_response();
      end
      1: begin
        send_prnd_out_packet(ep, exp_out_toggle[ep] ? PidTypeData1 : PidTypeData0);
        check_no_response();
      end
      default: begin
        usb20_item reply;
        retrieve_in_packet(ep, reply, .ack(0));
        `DV_CHECK_EQ(reply.timed_out, 1, "Response to corrupted IN request was unexpected")
      end
    endcase
    // Restore normal operation.
    inject_bad_token_crc5 = 1'b0;
    release_driver();
  endtask

  // Perform an OUT DATA transaction with an invalid CRC16.
  //
  // Note: If were to use a SETUP DATA transaction with just an invalid CRC16, the DUT would still
  // respond to the SETUP token packet and alter its internal state.
  virtual task generate_bad_crc16(bit [3:0] ep);
    `uvm_info(`gfn, "Generating bad CRC16 data packet", UVM_MEDIUM)
    claim_driver();
    // Ensure that the CRC16 value is incorrect; this should prevent the DUT responding to the
    // (apparent) SETUP token packet.
    inject_bad_data_crc16 = 1'b1;
    send_prnd_out_packet(ep, exp_out_toggle[ep] ? PidTypeData1 : PidTypeData0);
    check_no_response();
    // Restore normal operation.
    inject_bad_data_crc16 = 1'b0;
    release_driver();
  endtask

  // Induce a bit stuffing violation
  virtual task generate_bitstuff_error(bit [3:0] ep);
    byte unsigned data[];
    build_prnd_bitstuff_packet(data);
    `uvm_info(`gfn, "Generating data packet with bit stuffing violation", UVM_MEDIUM)
    claim_driver();
    // Disable the bit stuffing logic in the driver.
    cfg.m_usb20_agent_cfg.disable_bitstuffing = 1'b1;
    // Send the packet with the bit stuffing violation; the DUT should ignore it.
    send_out_packet(ep, exp_out_toggle[ep] ? PidTypeData1 : PidTypeData0, data);
    check_no_response();
    // Restore normal operation.
    cfg.m_usb20_agent_cfg.disable_bitstuffing = 1'b0;
    release_driver();
    // TODO: Check that a bitstuff error interrupt is raised by the DUT?
  endtask

  // Parallel process that injects bad traffic; the streaming test should continue unimpacted aside
  // from taking longer to transmit and check all of the data.
  virtual task generate_bad_traffic();
    // The set of bad traffic events from which we may choose.
    bit [NEventTypes-1:0] event_mask = {wt_bitstuff_errs, wt_bad_crc16, wt_bad_crc5,
                                        wt_spurious_pids, wt_bad_pids, wt_bad_syncs};
    while (event_mask && !traffic_stop) begin
      // Decide upon a random endpoint.
      bit [3:0] ep = $urandom_range(0, NEndpoints - 1);
      // Bad traffic/invalid packets may be generated with relatively high frequency because they
      // are short events, unlike suspend-resume signaling and bus resets.
      bit [11:0] event_delay;
      // Decide upon the time interval before the next bad traffic stimulus.
      `DV_CHECK_STD_RANDOMIZE_FATAL(event_delay)
      fork
        begin : isolation_fork
          fork
            cfg.clk_rst_vif.wait_clks(event_delay);
            wait (traffic_stop);
          join_any
          disable fork;
        end : isolation_fork
      join
      // Choose randomly from the stimuli that we are permitted to generate.
      randcase
        wt_bitstuff_errs: generate_bitstuff_error(ep);
        wt_bad_crc16:     generate_bad_crc16(ep);
        wt_bad_crc5:      generate_bad_crc5(ep);
        wt_spurious_pids: generate_spurious_pid(ep);
        wt_bad_pids:      generate_bad_pid(ep);
        wt_bad_syncs:     generate_bad_sync(ep);
      endcase
    end
  endtask

  virtual task body();
    // Collect additional configuration.
    void'($value$plusargs("wt_bad_syncs=%d", wt_bad_syncs));
    void'($value$plusargs("wt_bad_pids=%d", wt_bad_pids));
    void'($value$plusargs("wt_spurious_pids=%d", wt_spurious_pids));
    void'($value$plusargs("wt_bad_crc5=%d", wt_bad_crc5));
    void'($value$plusargs("wt_bad_crc16=%d", wt_bad_crc16));
    void'($value$plusargs("wt_bitstuff_errs=%d", wt_bitstuff_errs));
    // Confirm the configuration settings.
    `uvm_info(`gfn, $sformatf("wt_bad_syncs     %0d", wt_bad_syncs),     UVM_LOW)
    `uvm_info(`gfn, $sformatf("wt_bad_pids      %0d", wt_bad_pids),      UVM_LOW)
    `uvm_info(`gfn, $sformatf("wt_spurious_pids %0d", wt_spurious_pids), UVM_LOW)
    `uvm_info(`gfn, $sformatf("wt_bad_crc5      %0d", wt_bad_crc5),      UVM_LOW)
    `uvm_info(`gfn, $sformatf("wt_bad_crc16     %0d", wt_bad_crc16),     UVM_LOW)
    `uvm_info(`gfn, $sformatf("wt_bitstuff_errs %0d", wt_bitstuff_errs), UVM_LOW)
    fork
      super.body();
      generate_bad_traffic();
    join
  endtask
endclass : usbdev_bad_traffic_vseq
