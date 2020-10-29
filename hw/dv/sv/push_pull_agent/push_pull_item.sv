// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class push_pull_item #(parameter int HostDataWidth = 32,
                       parameter int DeviceDataWidth = HostDataWidth)
  extends uvm_sequence_item;

  rand bit [HostDataWidth-1:0]      h_data;
  rand bit [DeviceDataWidth-1:0]    d_data;

  // Host-side delay for both Push/Pull protocols.
  rand int unsigned host_delay;

  // Device-side delay for both Push/Pull protocols.
  rand int unsigned device_delay;

  `uvm_object_param_utils_begin(push_pull_item#(HostDataWidth, DeviceDataWidth))
    `uvm_field_int(h_data,     UVM_DEFAULT)
    `uvm_field_int(d_data,     UVM_DEFAULT)
    `uvm_field_int(host_delay,   UVM_DEFAULT)
    `uvm_field_int(device_delay, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function string convert2string();
    return {$sformatf("h_data = 0x%0x ", h_data),
            $sformatf("d_data = 0x%0x ", d_data),
            $sformatf("host_delay = 0x%0x ", host_delay),
            $sformatf("device_delay = 0x%0x ", device_delay)};
  endfunction

endclass
