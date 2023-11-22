// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

typedef bit buff_t[512];
class usbdev_data_integrity extends uvm_object;
  `uvm_object_utils(usbdev_data_integrity)

  // first dimension is addr and second dimension is endpoint
  buff_t    m_ad_buff  [128][16];
  int       byte_count [128][16];
  bit [7:0] pid_array  [128][16];

  function new(string name = "usbdev_data_integrity");
    super.new(name);
  endfunction

  task write(bit[7:0] pid, bit[6:0] address, bit[3:0] endpoint, bit payload_in[]);
    foreach (payload_in[i]) begin
      m_ad_buff[address][endpoint][i] = payload_in[i];
      // Count number of byte in payload
      byte_count[address][endpoint] = i;
      // Store PID to specific address and endpoint
      pid_array[address][endpoint] = pid;
    end
  endtask

  // This task will read the payload and pid from specific address and endpoint
  task read(output bit [7:0] pid, input bit [6:0] address, input bit [3:0] endpoint,
            output bit payload_out []);
    pid = pid_array[address][endpoint];
    for(int i = 0; i <= byte_count[address][endpoint]; i++) begin
      payload_out = new[payload_out.size() + 1] (payload_out);
      payload_out[payload_out.size() - 1] = m_ad_buff[address][endpoint][i];
    end
  endtask
endclass
