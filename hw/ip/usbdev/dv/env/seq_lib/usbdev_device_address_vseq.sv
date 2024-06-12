// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_device_address_vseq extends usbdev_spray_packets_vseq;
  `uvm_object_utils(usbdev_device_address_vseq)

  `uvm_object_new

  constraint num_trans_c {
    num_trans inside {[256:1024]};
  }

  // Whether to target the correct address?
  bit hit;

  // Guarantee that the packets will be received for packets that match the device address, and
  // would be received in the event that the DUT responds to other addresses.
  constraint ep_accepts_c {
    (ep_out_enable & rxenable_setup & ~out_stall) != 0;  // At least one receptive SETUP endpoint.
    (ep_out_enable & rxenable_out &   ~out_stall) != 0;  // At least one receptive OUT endpoint.
    (ep_in_enable  &                   ~in_stall) != 0;  // At least one receptive IN endpoint.
  };

  virtual function choose_target();
    super.choose_target();
    if (hit) target_addr = dev_addr;
    else `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(target_addr, target_addr != dev_addr;)
  endfunction

  virtual task body();
    `uvm_info(`gfn, $sformatf("Device address is 0x%x", dev_addr), UVM_LOW)
    // Target the correct address.
    hit = 1;
    super.body();
    // Target only other addresses.
    `uvm_info(`gfn, "Targeting other device addresses", UVM_LOW)
    hit = 0;
    super.body();
  endtask
endclass : usbdev_device_address_vseq
