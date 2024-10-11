// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package mbx_mem_ral_pkg;

  import uvm_pkg::*;
  import dv_base_reg_pkg::*;

  `include "uvm_macros.svh"

  typedef int unsigned uint;
  typedef class mbx_mem;
  typedef class mbx_mem_reg_block;

  class mbx_mem #(parameter int unsigned MemDepth = 32) extends dv_base_mem;

    `uvm_object_param_utils(mbx_mem#(MemDepth))

    function new(string           name = "mbx_mem",
                 longint unsigned size = MemDepth,
                 int unsigned     n_bits = 32,
                 string           access = "RW",
                 int              has_coverage = UVM_NO_COVERAGE);
      super.new(name, size, n_bits, access, has_coverage);
    endfunction : new

  endclass : mbx_mem


  class mbx_mem_reg_block extends dv_base_reg_block;
    // memories
    // TODO: The dv_reg_base_block uses int to calculate max_offset in max2 function.
    // To map the complete range, 30 bits are required but int type supports at max only 31 bits.
    rand mbx_mem #(uint'(2 ** 29)) m_mem;

    `uvm_object_param_utils(mbx_mem_reg_block)

    function new(string name = "mbx_mem_reg_block",
                 int    has_coverage = UVM_NO_COVERAGE);
      super.new(name, has_coverage);
    endfunction : new

    virtual function void build(uvm_reg_addr_t base_addr,
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
      m_mem = mbx_mem#(uint'(2 ** 29))::type_id::create("m_mem");
      m_mem.configure(.parent(this));
      default_map.add_mem(.mem(m_mem),
                          .offset(32'h0),
                          .rights("RW"));

    endfunction : build
  endclass : mbx_mem_reg_block

endpackage
