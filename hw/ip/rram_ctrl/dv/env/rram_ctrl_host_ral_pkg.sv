// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package rram_ctrl_host_ral_pkg;

  import uvm_pkg::*;
  import dv_base_reg_pkg::*;

  `include "uvm_macros.svh"

  typedef class rram_ctrl_host_mem;
  typedef class rram_ctrl_host_reg_block;

  class rram_ctrl_host_mem #(
    parameter int MemDepth = rram_ctrl_pkg::TotalBytes / 4
  ) extends dv_base_mem;

    `uvm_object_param_utils(rram_ctrl_host_mem#(MemDepth))

    function new(string name = "rram_ctrl_host_mem", longint unsigned size = MemDepth,
                 int unsigned n_bits = 32, string access = "RO",
                 int has_coverage = UVM_NO_COVERAGE);
      super.new(name, size, n_bits, access, has_coverage);
    endfunction : new

  endclass : rram_ctrl_host_mem


  class rram_ctrl_host_reg_block extends dv_base_reg_block;
    // memories
    rand rram_ctrl_host_mem rram_mem;

    `uvm_object_utils(rram_ctrl_host_reg_block)

    function new(string name = "rram_ctrl_host_ral_pkg", int has_coverage = UVM_NO_COVERAGE);
      super.new(name, has_coverage);
    endfunction : new

    virtual function void build(uvm_reg_addr_t base_addr, csr_excl_item csr_excl = null);
      // create default map
      this.default_map = create_map(.name("default_map"), .base_addr(base_addr), .n_bytes(
                                    4), .endian(UVM_LITTLE_ENDIAN));
      if (csr_excl == null) begin
        csr_excl = csr_excl_item::type_id::create("csr_excl");
        this.csr_excl = csr_excl;
      end

      // create memory
      rram_mem = rram_ctrl_host_mem#(rram_ctrl_pkg::TotalBytes/4)::type_id::create("rram_mem");
      rram_mem.configure(.parent(this));
      default_map.add_mem(.mem(rram_mem), .offset(0), .rights("RO"));

    endfunction : build
  endclass : rram_ctrl_host_reg_block

endpackage
