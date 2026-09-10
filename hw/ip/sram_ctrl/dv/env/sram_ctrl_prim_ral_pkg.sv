// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package sram_ctrl_prim_ral_pkg;

  import uvm_pkg::*;
  import dv_base_reg_pkg::*;

  `include "uvm_macros.svh"

  typedef class sram_ctrl_prim_mem_sram_mem;
  typedef class sram_ctrl_prim_reg_block;

  class sram_ctrl_prim_mem_sram_mem #(parameter int MemDepth = 32) extends dv_base_mem;

    `uvm_object_param_utils(sram_ctrl_prim_mem_sram_mem#(MemDepth))

    function new(string           name = "sram_ctrl_prim_mem_sram_mem",
                 longint unsigned size = MemDepth,
                 int unsigned     n_bits = 32,
                 string           access = "RW",
                 int              has_coverage = UVM_NO_COVERAGE);
      super.new(name, size, n_bits, access, has_coverage);
      set_mem_partial_write_support(1);
      set_data_intg_passthru(1);
    endfunction : new

  endclass : sram_ctrl_prim_mem_sram_mem


  class sram_ctrl_prim_reg_block #(parameter int MemDepth = 1024) extends dv_base_reg_block;
    // memories
    rand sram_ctrl_prim_mem_sram_mem #(MemDepth) sram_mem;

    `uvm_object_param_utils(sram_ctrl_prim_reg_block#(MemDepth))

    function new(string name = "sram_ctrl_prim_reg_block",
                 int    has_coverage = UVM_NO_COVERAGE);
      super.new(name, has_coverage);
    endfunction : new

    virtual function void build(uvm_reg_addr_t base_addr,
                                csr_excl_item  csr_excl,
                                int unsigned   addr_width,
                                int unsigned   data_width,
                                int unsigned   be_width);
      super.build(base_addr, csr_excl, addr_width, data_width, be_width);

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
      sram_mem = sram_ctrl_prim_mem_sram_mem#(MemDepth)::type_id::create("sram_mem");
      sram_mem.configure(.parent(this));
      default_map.add_mem(.mem(sram_mem),
                          .offset(32'h0),
                          .rights("RW"));

    endfunction : build
  endclass : sram_ctrl_prim_reg_block

endpackage
