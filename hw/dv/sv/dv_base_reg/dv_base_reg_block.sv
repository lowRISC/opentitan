// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// base register block class which will be used to generate the reg blocks
class dv_base_reg_block extends uvm_reg_block;
  `uvm_object_utils(dv_base_reg_block)

  csr_excl_item csr_excl;

  // The address mask for the register block. This will be (1 << K) - 1 for some K. All relative
  // offsets in the register block have addresses less than (1 << K), so an address decoder that
  // starts by discarding all higher bits will work correctly so long as the chosen base address of
  // the register block has no bits in common with this mask.
  //
  // This is initialized to zero (which means "unset") and then set by compute_mask(), which must
  // run after locking the model.
  protected uvm_reg_addr_t addr_mask = 0;

  function new (string name = "", int has_coverage = UVM_NO_COVERAGE);
    super.new(name, has_coverage);
  endfunction

  // provide build function to supply base addr
  virtual function void build(uvm_reg_addr_t base_addr,
                              csr_excl_item csr_excl = null);
    `uvm_fatal(`gfn, "this method is not supposed to be called directly!")
  endfunction

  // Get the address mask. This should only be called after locking the model (because it depends on
  // the layout of registers and memories in the block).
  function uvm_reg_addr_t get_addr_mask();
    `DV_CHECK_FATAL(is_locked())
    if (this.addr_mask == 0) begin
      this.compute_mask();
      `DV_CHECK_FATAL(this.addr_mask != 0)
    end
    return addr_mask;
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

  // Internal function, used to compute the address mask for this register block.
  //
  // This is quite an expensive computation, so we memoize the results in addr_mask
  //
  // use below to get the addr map size #3317
  // max2(biggest_reg_offset+reg_size, biggest_mem_offset+mem_size) and then round up to 2**N
  protected function void compute_mask();
    uvm_reg_addr_t max_addr, max_offset;
    uvm_reg_block  blocks[$];
    uvm_reg        regs[$];
    uvm_mem        mems[$];
    int unsigned   alignment;

    // TODO: assume IP only contains 1 reg block, find a better way to handle chip-level and IP
    // with multiple reg blocks
    this.get_blocks(blocks);
    if (blocks.size > 0) begin
      this.addr_mask = '1;
      return;
    end

    this.get_registers(regs);
    this.get_memories(mems);
    `DV_CHECK_GT_FATAL(regs.size + mems.size, 0)

    // Walk the known registers and memories, calculating the largest byte address visible. Note
    // that the get_offset() calls will return absolute addresses, including any base address in the
    // default register map.
    max_addr = 0;
    foreach (regs[i]) begin
      max_addr = max2(regs[i].get_offset() + regs[i].get_n_bytes() - 1, max_addr);
    end

    foreach (mems[i]) begin
      max_addr = max2(mems[i].get_offset() + mems[i].get_size() * mems[i].get_n_bytes() - 1,
                      max_addr);
    end

    // Subtract the base address in the default register map to get the maximum relative offset.
    max_offset = max_addr - this.default_map.get_base_addr();

    // Set alignment to be ceil(log2(biggest_offset))
    alignment = 0;
    while (max_offset > 0) begin
      alignment++;
      max_offset = max_offset >> 1;
    end

    // Note that we know alignment > 0 (because we've already checked that we have at least one
    // register or memory).
    `DV_CHECK_GT_FATAL(alignment, 0)

    // Finally, extract a mask corresponding to the alignment
    this.addr_mask = (1 << alignment) - 1;

  endfunction

  // Pick or check a base address for the given register map
  //
  // Check that base_addr is aligned as required by the register block and return it again. If
  // base_addr is the "magic" address '1, randomly pick an appropriately aligned base address and
  // return it.
  function uvm_reg_addr_t pick_base_addr(uvm_reg_addr_t base_addr);
    uvm_reg_addr_t mask = this.get_addr_mask();

    // If base_addr is '1, randomly pick an aligned base address
    if (base_addr == '1) begin
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(base_addr, (base_addr & mask) == '0;)
    end

    // Check base addr alignment (which should be guaranteed if we just picked it, but needs
    // checking if not).
    `DV_CHECK_FATAL((base_addr & mask) == '0)

    return base_addr;
  endfunction

  // Round the given address down to the start of the containing word. For example, if the address
  // is 'h123, it will be rounded down to 'h120.
  //
  // This is useful if you have a possibly misaligned address and you want to know whether it hits a
  // register (since get_reg_by_offset needs the aligned address for the start of the register).
  function uvm_reg_addr_t align_to_word_addr(uvm_reg_addr_t byte_addr);
    return (byte_addr >> 2) << 2;
  endfunction

  // Get the absolute address (in the default register map) for the given offset. For example, if
  // the base address is 'h100 and offset is 'h13, this will return 'h113.
  function uvm_reg_addr_t offset_to_addr(uvm_reg_addr_t byte_offset);
    uvm_reg_addr_t word_offset = byte_offset >> 2;
    return (word_offset << 2) + this.default_map.get_base_addr();
  endfunction

endclass
