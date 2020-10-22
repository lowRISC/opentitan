// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class push_pull_item #(parameter int DataWidth = 32) extends uvm_sequence_item;

  rand bit [DataWidth-1:0] data;

  // Host-side delay for both Push/Pull protocols.
  rand int unsigned host_delay;

  // Device-side delay for both Push/Pull protocols.
  rand int unsigned device_delay;

  `uvm_object_param_utils_begin(push_pull_item#(DataWidth))
    `uvm_field_int(data,         UVM_DEFAULT)
    `uvm_field_int(host_delay,   UVM_DEFAULT)
    `uvm_field_int(device_delay, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function string convert2string();
    return {$sformatf("data = 0x%0x ", data),
            $sformatf("host_delay = 0x%0x ", host_delay),
            $sformatf("device_delay = 0x%0x ", device_delay)};
  endfunction

endclass
