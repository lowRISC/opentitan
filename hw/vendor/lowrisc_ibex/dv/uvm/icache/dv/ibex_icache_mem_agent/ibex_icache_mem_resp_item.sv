// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An item that represents a memory response to the icache

class ibex_icache_mem_resp_item extends uvm_sequence_item;

  int unsigned min_response_delay = 0;
  int unsigned mid_response_delay = 5;
  int unsigned max_response_delay = 50;

  // True if this is a granted request. Otherwise, this is the first time we've seen an address (and
  // we might need to drive the PMP line).
  bit               is_grant;

  // If true, drive either a PMP error (if !is_grant) or respond later with a memory error.
  bit               err;

  // The address of the memory response (only used for requests that trigger a PMP error)
  bit [31:0]        address;

  // Only has an effect if is_grant. The number of cycles to wait between reading this from the
  // queue and responding with it.
  rand int unsigned delay;

  // Only has an effect if is_grant. The memory data to reply with (will be 'X if err is set)
  logic [31:0]      rdata;

  constraint c_delay_dist {
    delay dist {
      min_response_delay                        :/ 5,
      [min_response_delay+1:mid_response_delay] :/ 5,
      [mid_response_delay+1:max_response_delay] :/ 1
    };
  }

  // The delay field has no effect for requests (i.e. if is_grant is false). Force it to zero rather
  // than leave mysterious numbers in the logs.
  constraint c_no_delay_for_req {
    (!is_grant) -> delay == 0;
  }

  `uvm_object_utils_begin(ibex_icache_mem_resp_item)
    `uvm_field_int (is_grant, UVM_DEFAULT)
    `uvm_field_int (err,      UVM_DEFAULT)
    `uvm_field_int (address,  UVM_DEFAULT | UVM_HEX)
    `uvm_field_int (delay,    UVM_DEFAULT)
    `uvm_field_int (rdata,    UVM_DEFAULT | UVM_HEX)
  `uvm_object_utils_end

  `uvm_object_new
endclass
