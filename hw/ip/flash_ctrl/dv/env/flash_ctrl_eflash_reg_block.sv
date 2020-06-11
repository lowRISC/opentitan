// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Class: flash_ctrl_mem_eflash
class flash_ctrl_mem_eflash extends dv_base_mem;

  `uvm_object_utils(flash_ctrl_mem_eflash)

  function new(string           name = "flash_ctrl_mem_eflash",
               longint unsigned size = 131072,
               int unsigned     n_bits = 32,
               string           access = "RW",
               int              has_coverage = UVM_NO_COVERAGE);
    super.new(name, size, n_bits, access, has_coverage);
  endfunction : new

endclass : flash_ctrl_mem_eflash

// Class: flash_ctrl_eflash_reg_block
class flash_ctrl_eflash_reg_block extends dv_base_reg_block;
  // memories
  rand flash_ctrl_mem_eflash eflash;

  `uvm_object_utils(flash_ctrl_eflash_reg_block)

  function new(string name = "flash_ctrl_eflash_reg_block",
               int    has_coverage = UVM_NO_COVERAGE);
    super.new(name, has_coverage);
  endfunction : new

  virtual function void build(uvm_reg_addr_t base_addr,
                              dv_base_reg_pkg::csr_excl_item csr_excl = null);
    // create default map
    `uvm_info("eflash ral", "Creating the eflash default_map", UVM_LOW)
    this.default_map = create_map(.name("default_map"),
                                  .base_addr(base_addr),
                                  .n_bytes(4),
                                  .endian(UVM_LITTLE_ENDIAN));
    // create memory
    eflash = flash_ctrl_mem_eflash::type_id::create("eflash");
    eflash.configure(.parent(this));
    default_map.add_mem(.mem(eflash),
                       .offset(32'h0),
                       .rights("RW"));
  endfunction : build

endclass : flash_ctrl_eflash_reg_block
