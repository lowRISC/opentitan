// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// TileLink agent sequence library
// ---------------------------------------------

// Basic xbar TL host sequence
// TODO(taliu): Support illegal a_opcode
class xbar_tl_host_seq extends tl_host_seq;

  bit access_unclaimed_addr;
  int valid_device_id[$];

  `uvm_object_utils(xbar_tl_host_seq)

  function new (string name = "");
    super.new(name);
  endfunction : new

  virtual function void randomize_req(tl_seq_item req, int idx);
    int unsigned device_id;
    if (valid_device_id.size() > 0) begin
      device_id = $urandom_range(0, valid_device_id.size() - 1);
      device_id = valid_device_id[device_id];
    end else begin
      device_id = $urandom_range(0, xbar_devices.size() - 1);
    end
    if (!(req.randomize() with {a_valid_delay inside {[min_req_delay:max_req_delay]};
                                // Keep msb to zero as it's reserved to add host ID
                                a_source[(SourceWidth - 1):VALID_HOST_ID_WIDTH] == 0;
                                if (!access_unclaimed_addr) {
                                  a_addr inside {[xbar_devices[device_id].start_address :
                                                  xbar_devices[device_id].end_address]};
                                }})) begin
      `uvm_fatal(get_full_name(), "Cannot randomize req")
    end
  endfunction

endclass
