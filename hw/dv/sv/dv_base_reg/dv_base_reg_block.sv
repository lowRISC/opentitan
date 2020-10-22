// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// base register block class which will be used to generate the reg blocks
class dv_base_reg_block extends uvm_reg_block;
  `uvm_object_utils(dv_base_reg_block)

  csr_excl_item csr_excl;

  function new (string name = "", int has_coverage = UVM_NO_COVERAGE);
    super.new(name, has_coverage);
  endfunction

  // provide build function to supply base addr
  virtual function void build(uvm_reg_addr_t base_addr,
                              csr_excl_item csr_excl = null);
    `uvm_fatal(`gfn, "this method is not supposed to be called directly!")
  endfunction

  // use below to get the addr map size #3317
  // max2(biggest_reg_offset+reg_size, biggest_mem_offset+mem_size) and then round up to 2**N
  virtual function bit[`UVM_REG_ADDR_WIDTH:0] get_addr_map_size();
    uvm_reg_addr_t mem_biggest_offset;
    uvm_reg_addr_t reg_biggest_offset;
    uvm_reg_addr_t biggest_offset;
    uvm_reg_block  blocks[$];
    uvm_reg        regs[$];
    uvm_mem        mems[$];

    // TODO: assume IP only contains 1 reg block, find a better way to handle chip-level and IP
    // with multiple reg blocks
    this.get_blocks(blocks);
    if (blocks.size > 0) return 1 << `UVM_REG_ADDR_WIDTH;

    this.get_registers(regs);
    this.get_memories(mems);
    `DV_CHECK_GT_FATAL(regs.size + mems.size, 0)

    foreach (regs[i]) begin
      biggest_offset = max2(regs[i].get_offset() + regs[i].get_n_bytes() - 1, biggest_offset);
    end

    foreach (mems[i]) begin
      biggest_offset = max2(mems[i].get_offset() + mems[i].get_size() * mems[i].get_n_bytes() - 1,
                            biggest_offset);
    end

    get_addr_map_size = 1;
    while (biggest_offset > 0) begin
      biggest_offset = biggest_offset >> 1;
      get_addr_map_size = get_addr_map_size << 1;
    end
    return get_addr_map_size;
  endfunction

  function void get_dv_base_reg_blocks(ref dv_base_reg_block blks[$]);
    uvm_reg_block uvm_blks[$];
    this.get_blocks(uvm_blks);
    foreach (uvm_blks[i]) `downcast(blks[i], uvm_blks[i])
  endfunction

  function void get_dv_base_regs(ref dv_base_reg dv_regs[$]);
    uvm_reg ral_regs[$];
    this.get_registers(ral_regs);
    foreach (ral_regs[i]) `downcast(dv_regs[i], ral_regs[i])
  endfunction

  function void get_enable_regs(ref dv_base_reg enable_regs[$]);
    dv_base_reg_block blks[$];
    this.get_dv_base_reg_blocks(blks);
    if (blks.size() == 0) begin
      dv_base_reg all_regs[$];
      this.get_dv_base_regs(all_regs);
      foreach (all_regs[i]) begin
        if (all_regs[i].is_enable_reg()) enable_regs.push_back(all_regs[i]);
      end
      return;
    end else begin
      foreach (blks[i]) blks[i].get_enable_regs(enable_regs);
    end
  endfunction

  // override RAL's reset function to support enable registers
  // when reset issued - the locked registers' access will be reset to original access
  virtual function void reset(string kind = "HARD");
    dv_base_reg enable_regs[$];
    `uvm_info(`gfn, "Resetting RAL reg block", UVM_MEDIUM)
    super.reset(kind);
    get_enable_regs(enable_regs);
    foreach (enable_regs[i]) enable_regs[i].set_locked_regs_access();
  endfunction

endclass
