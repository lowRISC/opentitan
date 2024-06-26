// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_data_toggle_restore_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_data_toggle_restore_vseq)

  `uvm_object_new

  // Collect endpoint count from the DUT description.
  localparam int unsigned NEndpoints = usbdev_reg_pkg::NEndpoints;

  // Strictly, the USB host should never NAK an IN transaction (8.4.6.2), however other PIDs and
  // transmission errors for an ACK may lead to the DUT regarding the transaction as unsuccessful,
  // so to exercise that behavior we just emit a NAK for simplicity.
  typedef enum {
    InResponseNone,
    InResponseAck,
    InResponseNak
  } in_response_e;

  // Send an OUT packet with the specified DATAx token to the DUT and check that it
  // receives the expected handshake response.
  task send_and_check_packet(bit [3:0] ep, bit data_toggle, bit exp_ack,
                             inout uvm_reg_data_t exp_out_data_toggles);
    // Set up the OUT EP and supply a randomly-chosen buffer.
    `DV_CHECK_STD_RANDOMIZE_FATAL(out_buffer_id);
    configure_out_trans(ep);

    send_prnd_out_packet(ep, data_toggle ? PidTypeData1 : PidTypeData0, 1, 0);

    // Check that the transaction received the expected response, which should either be ACK
    // for an accepted packet (matching data toggle) or no response (packet dropped).
    if (exp_ack) begin
      check_response_matches(PidTypeAck);

      // Check the contents of the packet buffer memory against the OUT packet that was sent.
      check_rx_packet(ep, 1'b0, out_buffer_id, m_data_pkt.data);

      exp_out_data_toggles[ep] ^= 1;
    end else begin
      // We use the FIFO reset here to prevent the Available OUT Buffer FIFO overflowing later.
      // Note: this functionality is not present in the engineering sample.
      csr_wr(.ptr(ral.fifo_ctrl.avout_rst), .value(1));
    end
  endtask

  // We'll read back the packet we sent using a random endpoint.
  task collect_in_packet(bit [3:0] ep, in_response_e rsp, byte unsigned exp_data[],
                         inout uvm_reg_data_t exp_in_data_toggles);
    data_pkt in_data;

    // Present an IN buffer for collection.
    configure_in_trans(ep, out_buffer_id, exp_data.size());

    // Perform the IN transaction.
    send_token_packet(ep, PidTypeInToken);
    check_in_packet(exp_in_data_toggles[ep] ? PidTypeData1 : PidTypeData0, exp_data);

    // Respond as chosen to the DATA packet sent by the DUT.
    case (rsp)
      InResponseAck: begin
        send_handshake(PidTypeAck);
        // The IN data toggle should now have flipped.
        exp_in_data_toggles[ep] ^= 1;
      end
      InResponseNak: begin
        send_handshake(PidTypeNak);
      end
      default: begin
        // No response, nothing to do; the test may proceed to send another a packet within the
        // timeout period of the DUT, but it should still regard the transaction as unsuccessful
        // and not flip the data toggle.
      end
    endcase
  endtask

  // Check that the OUT and IN data toggles match expectations.
  task check_toggles(input uvm_reg_data_t exp_out_data_toggles,
                     input uvm_reg_data_t exp_in_data_toggles);
    uvm_reg_data_t act_out_data_toggles;
    uvm_reg_data_t act_in_data_toggles;

    csr_rd(.ptr(ral.out_data_toggle), .value(act_out_data_toggles));
    csr_rd(.ptr(ral.in_data_toggle), .value(act_in_data_toggles));
    `DV_CHECK_EQ(act_out_data_toggles, exp_out_data_toggles);
    `DV_CHECK_EQ(act_in_data_toggles, exp_in_data_toggles);
  endtask

  // Permute a subset of the data toggles at random and update the expectations accordingly.
  task permute_toggles(inout uvm_reg_data_t exp_out_data_toggles,
                       inout uvm_reg_data_t exp_in_data_toggles);
    bit [NEndpoints-1:0] out_status;
    bit [NEndpoints-1:0] in_status;
    bit [NEndpoints-1:0] out_mask;
    bit [NEndpoints-1:0] in_mask;

    `DV_CHECK_STD_RANDOMIZE_FATAL(out_status)
    `DV_CHECK_STD_RANDOMIZE_FATAL(in_status)
    `DV_CHECK_STD_RANDOMIZE_FATAL(out_mask)
    `DV_CHECK_STD_RANDOMIZE_FATAL(in_mask)
    `uvm_info(`gfn, $sformatf("Permuting OUT [0x%x,0x%x] and IN [0x%x,0x%x]",
                              out_mask, out_status, in_mask, in_status), UVM_MEDIUM)

    ral.out_data_toggle.mask.set(out_mask);
    ral.out_data_toggle.status.set(out_status);
    csr_update(.csr(ral.out_data_toggle));
    ral.in_data_toggle.mask.set(in_mask);
    ral.in_data_toggle.status.set(in_status);
    csr_update(.csr(ral.in_data_toggle));

    // Update expectations
    exp_out_data_toggles = (exp_out_data_toggles & ~out_mask) | (out_status & out_mask);
    exp_in_data_toggles  = (exp_in_data_toggles  & ~in_mask)  | (in_status  & in_mask);
    `uvm_info(`gfn, $sformatf("Expecting OUT 0x%0x IN 0x0%0x",
                              exp_out_data_toggles, exp_in_data_toggles), UVM_MEDIUM)
  endtask

  task body();
    uvm_reg_data_t exp_out_data_toggles;
    uvm_reg_data_t exp_in_data_toggles;
    uvm_reg_data_t ep_odd_set = {((NEndpoints+1)/2){2'b10}}; // AAA
    uvm_reg_data_t ep_even_set = ep_odd_set >> 1; // 555
    uvm_reg_data_t ep_all = {NEndpoints{1'b1}};
    uvm_reg_data_t rd_data;

    // Basic test of Data Toggle CSR behavior without interference from the USB itself;
    // the reception of SETUP/OUT packets would modify the OUT side Data Toggles.

    ral.out_data_toggle.mask.set(ep_all);
    ral.out_data_toggle.status.set(ep_even_set);
    csr_update(.csr(ral.out_data_toggle));

    csr_rd(.ptr(ral.out_data_toggle), .value(rd_data));
    `DV_CHECK_EQ_FATAL(rd_data, ep_even_set)
    `uvm_info(`gfn, "Completed basic test of OUT data toggles", UVM_MEDIUM)

    ral.in_data_toggle.mask.set(ep_all);
    ral.in_data_toggle.status.set(ep_odd_set);
    csr_update(.csr(ral.in_data_toggle));

    csr_rd(.ptr(ral.in_data_toggle), .value(rd_data));
    `DV_CHECK_EQ_FATAL(rd_data, ep_odd_set)
    csr_rd(.ptr(ral.out_data_toggle), .value(rd_data));
    `DV_CHECK_EQ_FATAL(rd_data, ep_even_set)
    `uvm_info(`gfn, "Completed basic test of IN data toggles", UVM_MEDIUM)

    // Attempt to invert all of the Data Toggle bits.
    ral.out_data_toggle.mask.set(ep_all);
    ral.out_data_toggle.status.set(ep_all ^ ep_even_set);
    csr_update(.csr(ral.out_data_toggle));

    ral.in_data_toggle.mask.set(ep_all);
    ral.in_data_toggle.status.set(ep_all ^ ep_odd_set);
    csr_update(.csr(ral.in_data_toggle));
    `uvm_info(`gfn, "Completed basic test of inverting data toggles", UVM_MEDIUM)

    // Read back and check all bits.
    check_toggles(ep_odd_set, ep_even_set);

    // Try setting some random state for all of the Data Toggle bits.
    ral.out_data_toggle.mask.set(ep_all);
    ral.in_data_toggle.mask.set(ep_all);
    exp_out_data_toggles = $urandom_range(0, ep_all);
    exp_in_data_toggles  = $urandom_range(0, ep_all);
    ral.out_data_toggle.status.set(exp_out_data_toggles);
    ral.in_data_toggle.status.set(exp_in_data_toggles);
    csr_update(.csr(ral.out_data_toggle));
    csr_update(.csr(ral.in_data_toggle));
    `uvm_info(`gfn, $sformatf("Setting OUT 0x%0x and IN 0x%0x",
                              exp_out_data_toggles, exp_in_data_toggles), UVM_MEDIUM)

    check_toggles(exp_out_data_toggles, exp_in_data_toggles);

    // We shall be exercising any subset of the endpoints, so all must be capable of IN/OUT
    // transfers, but let's just enable the specific ones that we're testing at that instant.
    //
    // Note 1: we can do this with the device connected only because we have control of the USB
    //         traffic. Strictly, the DUT does not permit them to be enabled/disabled at arbitrary
    //         times, but doing so serves to make this testing a bit more thorough.
    csr_wr(.ptr(ral.ep_out_enable[0]), .value(0));
    csr_wr(.ptr(ral.ep_in_enable[0]), .value(0));

    // Ask the driver to perform Bus Reset Signaling; only a short reset of 100us because anything
    // longer just wastes simulation time. This also clears the device address.
    send_bus_reset(100);
    // After a Bus Reset we must reinstate the device address before traffic will be accepted.
    usbdev_set_address(dev_addr);

    // A Bus Reset should have occurred above, which resets all of the Data Toggle bits to zero.
    exp_out_data_toggles = 0;
    exp_in_data_toggles  = 0;

    // Randomized interaction of Data Toggle CSR access and USB-side IN/OUT packet transfers.
    for (int unsigned txn = 0; txn < num_trans; txn++) begin
      bit out_provoke_mismatch;
      in_response_e in_rsp;
      bit [3:0] ep_out;
      bit [3:0] ep_in;

      // Randomly modify the data toggles and update our expectations.
      permute_toggles(exp_out_data_toggles, exp_in_data_toggles);

      // Select an IN endpoint and an OUT endpoint to test.
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(ep_out, ep_out inside {[0:NEndpoints-1]};)
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(ep_in,  ep_in  inside {[0:NEndpoints-1]};)
      // Decide whether we wish to match or mismatch the expected toggle.
      `DV_CHECK_STD_RANDOMIZE_FATAL(out_provoke_mismatch);
      // TODO: the usb20_driver presently cannot cope with non-response from the device, so we must
      //       not provoke a data toggle mismatch presently; lose this when usb20_driver has been
      //       extended.
      out_provoke_mismatch = 0;
      // Decide upon our response to an IN DATA packet.
      `DV_CHECK_STD_RANDOMIZE_FATAL(in_rsp);

      // Send a randomized packet to the chosen OUT endpoint.
      send_and_check_packet(ep_out, exp_out_data_toggles[ep_out] ^ out_provoke_mismatch,
                           !out_provoke_mismatch, exp_out_data_toggles);
      // Disable all OUT endpoints. See Note 1.
      csr_wr(.ptr(ral.ep_out_enable[0]), .value(0));

      // If the packet was not received and stored, we shall just retrieve a zero length packet
      // because this always works and we're more interested in the PIDs than the content here.
      if (out_provoke_mismatch) m_data_pkt.data.delete();

      // Attempt to retrieve the packet (if accepted) via the chosen IN endpoint.
      collect_in_packet(ep_in, in_rsp, m_data_pkt.data, exp_in_data_toggles);
      // Disable all IN endpoints. See Note 1.
      csr_wr(.ptr(ral.ep_in_enable[0]), .value(0));

      // An OUT toggle and/or an IN toggle may have flipped; check all toggle bits.
      check_toggles(exp_out_data_toggles, exp_in_data_toggles);
    end
  endtask

endclass
