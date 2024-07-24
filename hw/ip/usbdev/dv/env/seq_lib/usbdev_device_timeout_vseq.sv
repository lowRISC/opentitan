// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_device_timeout_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_device_timeout_vseq)

  `uvm_object_new

  // Types of response to IN DATA packet.
  typedef enum {
    // Host ignores the IN Data packet and sends no handshake within the timeout period; the DUT
    // shall not mark it as sent.
    ResponseNone,
    // This indicates that the host has successfully received the IN DATA packet and the DUT shall
    // mark it as sent.
    ResponseAck,
    // The following packets should be taken as indication that the handshake response from the host
    // has been missed; DUT shall not mark it as sent.
    ResponseSETUP,
    ResponseOUT,
    ResponseIN
  } response_type_e;

  // Check that the IN configuration of the specified endpoint matches expectations.
  task check_configin(bit [3:0] ep, bit exp_rdy, bit exp_sending, bit exp_pend);
    uvm_reg_data_t configin;
    csr_rd(.ptr(ral.configin[ep]), .value(configin));
    `DV_CHECK_EQ(get_field_val(ral.configin[0].rdy, configin), exp_rdy, "rdy not as expected")
    `DV_CHECK_EQ(get_field_val(ral.configin[0].pend, configin), exp_pend, "pend not as expected")
    `DV_CHECK_EQ(get_field_val(ral.configin[0].sending, configin), exp_sending,
                 "sending not as expected")
  endtask

  // Reset IN configuration in preparation for the next transaction.
  task reset_configin(bit [3:0] ep);
    uvm_reg_data_t configin;
    csr_rd(.ptr(ral.configin[ep]), .value(configin));
    if (get_field_val(ral.configin[ep].rdy, configin)) begin
      // The packet is still marked as 'rdy' so we need to remove it properly.
      int unsigned retracted_buf;
      bit sent, pend, retracted;
      retract_in_packet(ep, configin, sent, pend, retracted, retracted_buf);
      // Retraction should always occur at this point because there is nothing that can collect
      // it via an IN transaction.
      `DV_CHECK_EQ(retracted, 1, "Could not retract packet as expected")
      // We use only a single buffer in this test.
      `DV_CHECK_EQ(retracted_buf, in_buffer_id, "Buffer ID not as expected")
    end
  endtask

  // Check that the Data Toggle bit for the given IN endpoint is as expected.
  task check_in_toggle(bit [3:0] ep, bit exp_toggle);
    uvm_reg_data_t act_toggles;
    csr_rd(.ptr(ral.in_data_toggle.status), .value(act_toggles));
    `DV_CHECK_EQ(act_toggles[ep], exp_toggle, "IN data toggle not as expected")
  endtask

  // Check that the 'in_sent' bit for the given endpoint is as expected.
  task check_in_sent(bit [3:0] ep, bit exp_sent);
    uvm_reg_data_t in_sent;
    csr_rd(.ptr(ral.in_sent[0]), .value(in_sent));
    `DV_CHECK_EQ(in_sent[ep], exp_sent, "in_sent bit not as expected")
  endtask

  // Supply a buffer to the Available SETUP Buffer FIFO.
  task supply_buffer(int unsigned b);
    csr_wr(.ptr(ral.avsetupbuffer), .value(b));
  endtask

  virtual task body();
    // Expected DUT time out interval in terms of clock ticks.
    int unsigned dut_timeout = 18 * 4;
    bit exp_in_toggle = 1'b0;

    // Use the randomized default endpoint and buffer ID chosen by the base sequence.
    for (int unsigned txn = 0; txn < num_trans; txn++) begin
      // How shall we respond to the IN data packet?
      response_type_e response;
      // After how many bit intervals shall we respond?
      bit [4:0] response_delay;
      // Expectations for an unsuccessful transfer.
      bit exp_sending = 1'b1;
      bit exp_sent = 1'b0;
      bit exp_pend = 1'b0;
      bit exp_rdy = 1'b1;
      // Do we need to delay after this transaction?
      bit delay = 0;

      // See explanation in `usb20_agent_pkg.sv` => do not generate IN/OUT/SETUP after IN DATA
      // packet without an intervening handshake/timeout because it will corrupt the intended
      // streaming traffic.
      if (cfg.m_usb20_agent_cfg.rtl_must_have_host_handshake) begin
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(response, response == ResponseNone ||
                                                     response == ResponseAck;)
      end else begin
        `DV_CHECK_STD_RANDOMIZE_FATAL(response)
      end
      `DV_CHECK_STD_RANDOMIZE_FATAL(response_delay)

      `uvm_info(`gfn, $sformatf("Response type %0d delay %0d clocks", response, response_delay),
                UVM_MEDIUM)

      configure_in_trans(ep_default, in_buffer_id, .num_of_bytes(0));
      // The IN packet should be marked as 'rdy' at this point since it is available for collection.
      check_configin(ep_default, .exp_rdy(1'b1), .exp_sending(1'b0), .exp_pend(1'b0));
      check_in_toggle(ep_default, .exp_toggle(exp_in_toggle));

      // Initiate collection of the IN packet.
      `uvm_info(`gfn, $sformatf("Sending IN token to endpoint %0d", ep_default), UVM_MEDIUM)
      send_token_packet(ep_default, PidTypeInToken);
      // Collect and check the IN data packet.
      check_response_matches(exp_in_toggle ? PidTypeData1 : PidTypeData0);
      // Wait for a randomized number of bit intervals, and predict whether the DUT shall yet
      // have timed-out the IN transaction; we use the DUT clock to measure the bit intervals at the
      // device, and observe that the clock is 4 x the bit rate.
      if (response_delay) cfg.clk_rst_vif.wait_clks(response_delay);

      // How are we going to respond?
      case (response)
        ResponseSETUP, ResponseIN, ResponseOUT: begin
          // Send an unexpected SETUP/IN/OUT
          pid_type_e pid = (response == ResponseSETUP) ? PidTypeSetupToken :
                          ((response == ResponseOUT)   ? PidTypeOutToken   : PidTypeInToken);
          send_token_packet(ep_default, pid, .target_addr(dev_addr),
                            .await_response(response != ResponseIN));
          // Wait long enough for the effects of the SETUP packet to be visible in the CSRs.
          loopback_delay();
          // Having chosen to send a SETUP packet we'll have caused the IN packet to be retired from
          // 'rdy' to 'pend' to prevent interference with the ensuing Control Transfer.
          if (response == ResponseSETUP) begin
            // IN side toggle becomes set in response to SETUP token packet.
            exp_in_toggle = 1'b1;
          end
          // TODO: This relies upon a proposed RTL change #23717 which deasserts 'sending' in the
          // event of rollback, unless it's another IN request to the same endpoint.
          exp_sending = (response == ResponseIN);
          delay = 1;
        end
        ResponseAck: begin
          bit acked_promptly = (response_delay < dut_timeout);
          send_handshake(PidTypeAck, .delay_first(0));
          // IN packet successfully received if ACKed promptly; flip the data toggle bit.
          exp_in_toggle ^= acked_promptly;
          // Update expectations; the behavior here depends upon our tardiness.
          exp_sending = 1'b0;
          exp_pend = 1'b0;
          exp_sent = acked_promptly;
          exp_rdy  = !acked_promptly;
        end
        default: `DV_CHECK_EQ(response, ResponseNone)  // Nothing more to do.
      endcase

      // Check that the packet has the expected 'rdy' and 'pend' indications, according to whether
      // we acknowledged successful receipt of the packet within the DUT timeout interval.
      check_configin(ep_default, .exp_rdy(exp_rdy), .exp_sending(exp_sending), .exp_pend(exp_pend));
      if (exp_pend) begin
        ral.configin[ep_default].pend.set(1'b1);
        csr_update(ral.configin[ep_default]);
      end
      check_in_toggle(ep_default, .exp_toggle(exp_in_toggle));
      // Check that 'in_sent' indicates whether or not the packet has been sent as per expectations.
      check_in_sent(ep_default, .exp_sent(exp_sent));
      // Clear the sent bit
      if (exp_sent) csr_wr(.ptr(ral.in_sent[0]), .value(exp_sent << ep_default));

      // If we sent a SETUP/IN/OUT packet in place of the usual handshake then we need to wait long
      // enough here for the device to time out, because otherwise the next transaction could become
      // confused by this one.
      if (delay) begin
        cfg.clk_rst_vif.wait_clks(dut_timeout * 4);
      end
      reset_configin(ep_default);
    end
  endtask
endclass : usbdev_device_timeout_vseq
