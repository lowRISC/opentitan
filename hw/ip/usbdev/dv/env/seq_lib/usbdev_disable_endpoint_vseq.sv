// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_disable_endpoint_vseq extends usbdev_spray_packets_vseq;
  `uvm_object_utils(usbdev_disable_endpoint_vseq)

  `uvm_object_new

  // Keep the transaction count low because we're exercising just a single endpoint per seed and
  // there's no real benefit to performing lots of transactions.
  constraint num_trans_c {
    num_trans inside {[16:32]};
  }

  localparam int unsigned AllEndpoints = {NEndpoints{1'b1}};

  // Guarantee that the packets will be received for packets that match the device address, and
  // would be received in the event that the DUT responds to other addresses.
  constraint ep_accepts_c {
    (ep_out_enable & rxenable_setup & ~out_stall) != 0;  // At least one receptive SETUP endpoint.
    (ep_out_enable & rxenable_out &   ~out_stall) != 0;  // At least one receptive OUT endpoint.
    (ep_in_enable  &                   ~in_stall) != 0;  // At least one receptive IN endpoint.

    // Must have at least one disabled endpoint.
    (ep_out_enable != AllEndpoints);
    (ep_in_enable  != AllEndpoints);
  }

  // For this sequence we are always targeting the DUT address.
  constraint target_addr_c {
    target_addr == dev_addr;
  }

  // Ensure that we choose a disabled endpoint.
  virtual function void choose_target();
    bit [3:0] init_ep;
    super.choose_target();
    // Choose a disabled endpoint, but start looking from the unconstrained random choice so that
    // we don't favor specific endpoints.
    if (target_ep >= NEndpoints) target_ep -= NEndpoints;
    `DV_CHECK_LT(target_ep, NEndpoints)
    init_ep = target_ep;
    while (ep_out_enable[target_ep]) begin
      target_ep = (target_ep >= NEndpoints - 1) ? 0 : (target_ep + 1);
      `DV_CHECK_NE(target_ep, init_ep)  // There must always be at least one disabled endpoint.
    end
    `uvm_info(`gfn, $sformatf("Targeting disabled endpoint %d", target_ep), UVM_LOW)
  endfunction

  virtual task body();
    super.body();
    `DV_CHECK_EQ(rx_cnt, 0, "No packets should have been received by endpoint")
  endtask
endclass : usbdev_disable_endpoint_vseq
