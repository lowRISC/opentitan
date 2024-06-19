// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_data_toggle_clear_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_data_toggle_clear_vseq)

  `uvm_object_new

  // Randomized initial state of toggles; updated with expectations during sequence.
  rand bit [NEndpoints-1:0] exp_in_toggles;
  rand bit [NEndpoints-1:0] exp_out_toggles;

  virtual task body();
    // All endpoints including the chosen one.
    bit [NEndpoints-1:0] all_endpoints = {NEndpoints{1'b1}};
    // Base sequence has chosen a default endpoint at random; use that.
    bit [NEndpoints-1:0] ep_mask = 1 << ep_default;
    // All endpoints other than the chosen one.
    bit [NEndpoints-1:0] all_others = ~ep_mask;

    // Set the data toggle bits to an arbitrary state.
    ral.out_data_toggle.status.set(exp_out_toggles);
    ral.out_data_toggle.mask.set(ep_mask);
    csr_update(ral.out_data_toggle);
    ral.in_data_toggle.status.set(exp_in_toggles);
    ral.in_data_toggle.mask.set(ep_mask);
    csr_update(ral.in_data_toggle);

    for (int unsigned txn = 0; txn < num_trans; txn++) begin
      bit [1:0] clear_toggles;
      bit test_in;

      // Are we testing IN or OUT traffic?
      `DV_CHECK_STD_RANDOMIZE_FATAL(test_in)
      // Decide which toggle bit(s) we're going to clear.
      `DV_CHECK_STD_RANDOMIZE_FATAL(clear_toggles)

      // Perform some traffic to/from the endpoint pair.
      if (test_in) begin
        usb20_item reply;
        // Present the IN packet for collection; because USB uses 'Zero Length Packets' we
        // actually don't need to supply any data here, so keep things simpler.
        configure_in_trans(ep_default, in_buffer_id, .num_of_bytes(0));
        retrieve_in_packet(ep_default, reply, .ack(1));
        // Flip the IN data toggle because the packet was successfully received by the host.
        exp_in_toggles[ep_default] ^= 1'b1;
      end else begin
        // Present a buffer for reception and then transmit an OUT packet.
        configure_out_trans(ep_default);
        send_prnd_out_packet(ep_default, exp_out_toggles[ep_default] ? PidTypeData1 : PidTypeData0);
        check_response_matches(PidTypeAck);
        check_rx_packet(ep_default, .setup(0), .exp_buffer_id(out_buffer_id),
                        .exp_byte_data(m_data_pkt.data), .buffer_known(1));
        // Flip the OUT data toggle because the packet was successfully received by the DUT.
        exp_out_toggles[ep_default] ^= 1'b1;
      end

      // Update the OUT side toggle bits.
      ral.out_data_toggle.status.set(exp_out_toggles & ~ep_mask);
      ral.out_data_toggle.mask.set(clear_toggles[0] ? all_endpoints : all_others);
      csr_update(ral.out_data_toggle);
      if (clear_toggles[0]) exp_out_toggles[ep_default] = 1'b0;
      // Update the IN side toggle bits.
      ral.in_data_toggle.status.set(exp_in_toggles & ~ep_mask);
      ral.in_data_toggle.mask.set(clear_toggles[1] ? all_endpoints : all_others);
      csr_update(ral.in_data_toggle);
      if (clear_toggles[1]) exp_in_toggles[ep_default] = 1'b0;
    end
  endtask
endclass : usbdev_data_toggle_clear_vseq
