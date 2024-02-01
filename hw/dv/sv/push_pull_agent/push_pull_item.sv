// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class push_pull_item #(parameter int HostDataWidth = 32,
                       parameter int DeviceDataWidth = HostDataWidth)
  extends uvm_sequence_item;

  rand bit [HostDataWidth-1:0]      h_data;
  rand bit [DeviceDataWidth-1:0]    d_data;

  // Host-side delay for both push/pull protocols.
  rand int unsigned host_delay;
  constraint host_delay_max_c {
    soft host_delay <= 1000;
  }

  // Device-side delay for both push/pull protocols.
  rand int unsigned device_delay;
  constraint device_delay_max_c  {
    soft device_delay <= 1000;
  }

  // 4-phase pull protocol delays to de-assert req. This delay is applied after ack assertion.
  rand int unsigned req_lo_delay;
  constraint req_lo_delay_max_c {
    soft req_lo_delay <= 1000;
  }

  // 4-phase pull protocol delays to de-assert ack. This delay is applied after req de-assertion.
  rand int unsigned ack_lo_delay;
  constraint ack_lo_delay_max_c {
    soft ack_lo_delay <= 1000;
  }

  `uvm_object_param_utils_begin(push_pull_item#(HostDataWidth, DeviceDataWidth))
    `uvm_field_int(h_data,     UVM_DEFAULT)
    `uvm_field_int(d_data,     UVM_DEFAULT)
    `uvm_field_int(host_delay,   UVM_DEFAULT)
    `uvm_field_int(device_delay, UVM_DEFAULT)
    `uvm_field_int(req_lo_delay, UVM_DEFAULT)
    `uvm_field_int(ack_lo_delay, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function string convert2string();
    return {$sformatf("h_data = 0x%0x ", h_data),
            $sformatf("d_data = 0x%0x ", d_data),
            $sformatf("host_delay = 0x%0d ", host_delay),
            $sformatf("device_delay = 0x%0d ", device_delay),
            $sformatf("req_lo_delay = 0x%0d ", req_lo_delay),
            $sformatf("ack_lo_delay = 0x%0d ", ack_lo_delay)};
  endfunction

endclass
