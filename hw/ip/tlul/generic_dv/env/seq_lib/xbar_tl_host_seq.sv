// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// TileLink agent sequence library
// ---------------------------------------------

// Basic xbar TL host sequence
class xbar_tl_host_seq extends tl_host_seq;

  // if enabled, will allow to access both mapped and unmapped addr
  bit en_unmapped_addr = 0;

  int valid_device_id[$];

  // control the chance to use last address for current item
  int use_last_item_addr_pct = 5;
  bit [AddrWidth - 1   : 0] last_item_addr;

  `uvm_object_utils(xbar_tl_host_seq)
  `uvm_object_new

  virtual function void randomize_req(tl_seq_item req, int idx);
    uint device_id;
    bit  is_mapped_addr;
    bit  use_last_item_addr;
    uint addr_range_id;

    // randomize device_id, is_mapped_addr, addr_range_id first
    if (valid_device_id.size() > 0) begin
      device_id = $urandom_range(0, valid_device_id.size() - 1);
      device_id = valid_device_id[device_id];
    end else begin
      device_id = $urandom_range(0, xbar_devices.size() - 1);
    end
    if (use_last_item_addr_pct > $urandom_range(99, 0)) use_last_item_addr = 1;
    if (en_unmapped_addr) begin
      is_mapped_addr = $urandom_range(0, 1);
    end else begin
      is_mapped_addr = 1;
      addr_range_id = $urandom_range(0, xbar_devices[device_id].addr_ranges.size() - 1);
    end
    if (!(req.randomize() with {
        a_valid_delay inside {[min_req_delay:max_req_delay]};
        if (use_last_item_addr) {
          a_addr == last_item_addr;
        } else if (is_mapped_addr) {
          a_addr inside {[xbar_devices[device_id].addr_ranges[addr_range_id].start_addr :
                          xbar_devices[device_id].addr_ranges[addr_range_id].end_addr]};
        } else {
          foreach (xbar_devices[device_id].addr_ranges[i]) {
            !(a_addr inside {[xbar_devices[device_id].addr_ranges[i].start_addr :
                              xbar_devices[device_id].addr_ranges[i].end_addr]});
          }
        }})) begin
      `uvm_fatal(get_full_name(), "Cannot randomize req")
    end

    last_item_addr = req.a_addr;
  endfunction

  // prevent seq runs out of source ID
  virtual task pre_start_item(tl_seq_item req);
    super.pre_start_item(req);
    wait(pending_req.size() < cfg.max_outstanding_req);
  endtask

endclass
