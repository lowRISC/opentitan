// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class mbx_seq_item extends uvm_sequence_item;

  rand bit [top_pkg::TL_AW-1:0] ibmbx_base_addr;
  rand bit [top_pkg::TL_AW-1:0] ibmbx_limit_addr;
  rand bit [top_pkg::TL_AW-1:0] obmbx_base_addr;
  rand bit [top_pkg::TL_AW-1:0] obmbx_limit_addr;

  rand bit address_range_valid;
  rand mubi4_t address_range_regwen;

  // Sizes of Request and Response message in DWORDs
  rand bit [10:0] request_dwords;
  rand bit [10:0] response_dwords;

  `uvm_object_utils_begin(mbx_seq_item)
    `uvm_field_int(ibmbx_base_addr,      UVM_DEFAULT)
    `uvm_field_int(ibmbx_limit_addr,     UVM_DEFAULT)
    `uvm_field_int(obmbx_base_addr,      UVM_DEFAULT)
    `uvm_field_int(obmbx_limit_addr,     UVM_DEFAULT)
    `uvm_field_int(address_range_valid,  UVM_DEFAULT)
    `uvm_field_enum(mubi4_t, address_range_regwen, UVM_DEFAULT)
    `uvm_field_int(request_dwords,       UVM_DEFAULT)
    `uvm_field_int(response_dwords,      UVM_DEFAULT)
  `uvm_object_utils_end

  //  Constructor: new
  function new(string name = "");
    super.new(name);
  endfunction : new

  function void set_address_range_randomization(bit enabled);
    ibmbx_base_addr.rand_mode(enabled);
    ibmbx_limit_addr.rand_mode(enabled);
    obmbx_base_addr.rand_mode(enabled);
    obmbx_limit_addr.rand_mode(enabled);
  endfunction

  constraint legal_ibmbx_addr_range_c {
    // TODO: Should have a full 32-bit address space!
    (ibmbx_limit_addr < 32'h4000_0000);

    (ibmbx_limit_addr >= ibmbx_base_addr);
    // Ensure that the allocated address range is large enough for all valid messages because
    // otherwise we run the risk of making all subsequent response messages artificially small
    // because the address range has been locked.
    ((ibmbx_limit_addr - ibmbx_base_addr) / 4 >= MBX_DV_MAX_DW);
  }

  constraint legal_obmbx_addr_range_c {
    // TODO: Should have a full 32-bit address space!
    (obmbx_limit_addr < 32'h4000_0000);

    (obmbx_limit_addr >= obmbx_base_addr);
  }

  constraint legal_address_range_valid_c {
    // TODO: presently we are concerned only with generating valid hardware configurations.
    address_range_valid == 1'b1;
  }

  constraint legal_request_dwords_c {
    request_dwords > 0 && request_dwords < 'h400;
  }

  constraint legal_response_dwords_c {
    // There is an additioanl constraint upon the length of the Response because the register
    // OUTBOUND_OBJECT_SIZE is limited.
    response_dwords > 0 && response_dwords <= MBX_DV_MAX_DW;
  }

  constraint legal_non_overlapping_region_c {
    ibmbx_limit_addr < obmbx_base_addr || ibmbx_base_addr > obmbx_limit_addr;
  }

  constraint legal_addr_alignment_c {
    (ibmbx_base_addr[1:0] == 0);
    (ibmbx_limit_addr[1:0] == 0);
    (obmbx_base_addr[1:0] == 0);
    (obmbx_limit_addr[1:0] == 0);
  }

endclass : mbx_seq_item
