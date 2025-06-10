// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package rom_ctrl_prim_ral_pkg;

  import uvm_pkg::*;
  import dv_base_reg_pkg::*;

  `include "uvm_macros.svh"

  typedef class rom_ctrl_prim_mem_rom_mem;
  typedef class rom_ctrl_prim_reg_block;

  class rom_ctrl_prim_mem_rom_mem #(parameter int MemDepth = 32) extends dv_base_mem;

    `uvm_object_param_utils(rom_ctrl_prim_mem_rom_mem#(MemDepth))

    extern function new(string           name = "",
                        longint unsigned size = MemDepth,
                        int unsigned     n_bits = 32,
                        string           access = "RO",
                        int              has_coverage = UVM_NO_COVERAGE);

  endclass : rom_ctrl_prim_mem_rom_mem

  function rom_ctrl_prim_mem_rom_mem::new(string           name = "",
                                          longint unsigned size = MemDepth,
                                          int unsigned     n_bits = 32,
                                          string           access = "RO",
                                          int              has_coverage = UVM_NO_COVERAGE);
    super.new(name, size, n_bits, access, has_coverage);
    set_mem_partial_write_support(1);
    set_data_intg_passthru(1);
  endfunction : new


  class rom_ctrl_prim_reg_block #(parameter int AddrWidth = 10) extends dv_base_reg_block;
    // memories
    rand rom_ctrl_prim_mem_rom_mem #(2 ** AddrWidth) rom_mem;

    `uvm_object_param_utils(rom_ctrl_prim_reg_block#(AddrWidth))

    extern function new(string name = "",
                        int has_coverage = UVM_NO_COVERAGE);

    extern virtual function void build(uvm_reg_addr_t base_addr, csr_excl_item csr_excl = null);

  endclass : rom_ctrl_prim_reg_block

  function rom_ctrl_prim_reg_block::new(string name = "",
                                        int    has_coverage = UVM_NO_COVERAGE);
    super.new(name, has_coverage);
  endfunction : new

  function void rom_ctrl_prim_reg_block::build(uvm_reg_addr_t base_addr,
                                               csr_excl_item csr_excl = null);
    // create default map
    this.default_map = create_map(.name("default_map"),
                                  .base_addr(base_addr),
                                  .n_bytes(4),
                                  .endian(UVM_LITTLE_ENDIAN));
    if (csr_excl == null) begin
      csr_excl = csr_excl_item::type_id::create("csr_excl");
      this.csr_excl = csr_excl;
    end

    // create memories
    rom_mem = rom_ctrl_prim_mem_rom_mem#(2 ** AddrWidth)::type_id::create("rom_mem");
    rom_mem.configure(.parent(this));
    default_map.add_mem(.mem(rom_mem),
                        .offset(32'h0),
                        .rights("RO"));

  endfunction : build

endpackage
