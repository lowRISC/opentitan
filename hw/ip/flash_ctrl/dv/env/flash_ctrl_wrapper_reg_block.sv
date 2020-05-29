// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Class: eflash_mem
class eflash_mem extends dv_base_mem;

  `uvm_object_utils(eflash_mem)

  function new(string           name = "eflash_mem",
               longint unsigned size = 131072,
               int unsigned     n_bits = 32,
               string           access = "RW",
               int              has_coverage = UVM_NO_COVERAGE);
    super.new(name, size, n_bits, access, has_coverage);
  endfunction : new

endclass : eflash_mem

// Class: flash_ctrl_wrapper_reg_block
class flash_ctrl_wrapper_reg_block extends flash_ctrl_reg_block;
  // Create a separate map for eflash since it is attached to a different TL interface.
  uvm_reg_map eflash_map;

  // memories
  rand eflash_mem eflash;

  `uvm_object_utils(flash_ctrl_wrapper_reg_block)

  function new(string name = "flash_ctrl_wrapper_reg_block",
               int    has_coverage = UVM_NO_COVERAGE);
    super.new(name, has_coverage);
  endfunction : new


  virtual function void build(uvm_reg_addr_t base_addr,
                              csr_utils_pkg::csr_excl_item csr_excl = null);
    super.build(base_addr, csr_excl);
    // TODO: Uncomment once CSR sequence fixes are made.
    // // create eflash map
    // this.eflash_map = create_map(.name("eflash_map"),
    //                              .base_addr(base_addr),
    //                              .n_bytes(4),
    //                              .endian(UVM_LITTLE_ENDIAN));
    // // create memory
    // eflash = eflash_mem::type_id::create("eflash");
    // eflash.configure(.parent(this));
    // eflash_map.add_mem(.mem(eflash),
    //                    .offset(32'h0),
    //                    .rights("RW"));
  endfunction : build

endclass : flash_ctrl_wrapper_reg_block
