// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package flash_ctrl_eflash_ral_pkg;

  import uvm_pkg::*;
  import dv_base_reg_pkg::*;

  `include "uvm_macros.svh"

  typedef class flash_ctrl_eflash_mem;
  typedef class flash_ctrl_eflash_reg_block;

  class flash_ctrl_eflash_mem #(
    parameter int MemDepth = flash_ctrl_reg_pkg::BytesPerBank / 4
  ) extends dv_base_mem;

    `uvm_object_param_utils(flash_ctrl_eflash_mem#(MemDepth))

    function new(string name = "flash_ctrl_eflash_mem", longint unsigned size = MemDepth,
                 int unsigned n_bits = 32, string access = "RO",
                 int has_coverage = UVM_NO_COVERAGE);
      super.new(name, size, n_bits, access, has_coverage);
    endfunction : new

  endclass : flash_ctrl_eflash_mem


  class flash_ctrl_eflash_reg_block extends dv_base_reg_block;
    // memories
    rand flash_ctrl_eflash_mem flash_mem[flash_ctrl_reg_pkg::RegNumBanks];

    `uvm_object_utils(flash_ctrl_eflash_reg_block)

    function new(string name = "flash_ctrl_eflash_ral_pkg", int has_coverage = UVM_NO_COVERAGE);
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

      // create memories
      foreach (flash_mem[i]) begin
        flash_mem[i] =
            flash_ctrl_eflash_mem#(flash_ctrl_reg_pkg::BytesPerBank/4)::type_id::create(
            $sformatf("flash_mem[%0d]", i));
        flash_mem[i].configure(.parent(this));
        default_map.add_mem(.mem(flash_mem[i]), .offset(i * flash_ctrl_reg_pkg::BytesPerBank),
                            .rights("RO"));
      end
    endfunction : build
  endclass : flash_ctrl_eflash_reg_block

endpackage
