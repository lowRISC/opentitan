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
    super.reset(kind);
    get_enable_regs(enable_regs);
    foreach (enable_regs[i]) enable_regs[i].set_locked_regs_access();
  endfunction

endclass
