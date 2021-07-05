// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// base register block class which will be used to generate the reg blocks
class dv_base_reg_block extends uvm_reg_block;
  `uvm_object_utils(dv_base_reg_block)

  csr_excl_item csr_excl;

  // The address mask for the register block specific to a map. This will be (1 << K) - 1 for some
  // K. All relative offsets in the register block have addresses less than (1 << K), so an address
  // decoder that starts by discarding all higher bits will work correctly so long as the chosen
  // base address of the register block has no bits in common with this mask.
  //
  // This is set by compute_addr_mask(), which must run after locking the model.
  protected uvm_reg_addr_t addr_mask[uvm_reg_map];

  uvm_reg_addr_t csr_addrs[$];

  addr_range_t mem_ranges[$];

  addr_range_t mapped_addr_ranges[$];

  bit has_unmapped_addrs;
  addr_range_t unmapped_addr_ranges[$];

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
    // if the ral has hier, this function will recursively includes the registers in the sub-blocks
    this.get_registers(ral_regs);
    foreach (ral_regs[i]) `downcast(dv_regs[i], ral_regs[i])
  endfunction

  function dv_base_reg get_dv_base_reg_by_name(string csr_name, bit check_csr_exist = 1'b1);
    uvm_reg csr = get_reg_by_name(csr_name);
    `downcast(get_dv_base_reg_by_name, csr)
    if (check_csr_exist) begin
      `DV_CHECK_NE_FATAL(get_dv_base_reg_by_name, null,
                         $sformatf("%0s does not exist in block %0s",csr_name, get_name()))
    end
  endfunction

  function void get_shadowed_regs(ref dv_base_reg shadowed_regs[$]);
    dv_base_reg all_regs[$];
    this.get_dv_base_regs(all_regs);
    foreach (all_regs[i]) begin
      if (all_regs[i].get_is_shadowed()) shadowed_regs.push_back(all_regs[i]);
    end
  endfunction

  // Internal function, used to compute the address mask for this register block.
  //
  // This is quite an expensive computation, so we memoize the results in addr_mask[map].
  // Use below to get the addr map size #3317
  // max2(biggest_reg_offset+reg_size, biggest_mem_offset+mem_size) and then round up to 2**N
  protected function void compute_addr_mask(uvm_reg_map map);
    uvm_reg_addr_t max_offset;
    uvm_reg_block  blocks[$];
    int unsigned   alignment;

    // TODO: assume IP only contains 1 reg block, find a better way to handle chip-level and IP
    // with multiple reg blocks
    get_blocks(blocks);
    if (blocks.size > 0) begin
      addr_mask[map] = '1;
      return;
    end

    max_offset = get_max_offset(map);

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
    addr_mask[map] = (1 << alignment) - 1;

    // Computed mask must be non-zero.
    `DV_CHECK_FATAL(addr_mask[map])
  endfunction

  // Internal function, used to get a list of all valid CSR addresses.
  protected function void compute_csr_addrs();
    uvm_reg csrs[$];
    get_registers(csrs);
    foreach (csrs[i]) begin
      csr_addrs.push_back(csrs[i].get_address());
    end
  endfunction

  // Internal function, used to get a list of all valid memory ranges
  protected function void compute_mem_addr_ranges();
    uvm_mem mems[$];
    get_memories(mems);
    foreach (mems[i]) begin
      addr_range_t mem_range;
      mem_range.start_addr = mems[i].get_address();
      mem_range.end_addr   = mem_range.start_addr +
                             mems[i].get_size() * mems[i].get_n_bytes() - 1;
      mem_ranges.push_back(mem_range);
    end
  endfunction

  // Used to get a list of all valid address ranges covered by this reg block
  function void compute_mapped_addr_ranges();
    uvm_reg csrs[$];
    get_registers(csrs);

    // Compute all CSR addresses and mem ranges known to this reg block
    compute_csr_addrs();
    compute_mem_addr_ranges();

    // Convert each CSR into an address range
    foreach (csrs[i]) begin
      addr_range_t csr_addr_range;
      csr_addr_range.start_addr = csrs[i].get_address();
      csr_addr_range.end_addr   = csr_addr_range.start_addr + csrs[i].get_n_bytes() - 1;
      mapped_addr_ranges.push_back(csr_addr_range);
    end

    mapped_addr_ranges = {mapped_addr_ranges, mem_ranges};

    // Sort the mapped address ranges in ascending order based on the start_addr of each range
    mapped_addr_ranges.sort(m) with (m.start_addr);

  endfunction

  // Used to get a list of all invalid address ranges in this reg block
  function void compute_unmapped_addr_ranges();
    addr_range_t range;

    // convert the address mask into a relative address,
    // this is the highest addressable location in the register block
    uvm_reg_addr_t highest_addr = default_map.get_base_addr() + get_addr_mask();

    // unmapped address ranges consist of:
    // - the address space between all mapped address ranges (if exists)
    // - space between csr_base_addr and the first mapped address range (if exists)
    // - space between the last mapped address and the highest address mapped by the address mask
    if (mapped_addr_ranges.size() == 0) begin
      range.start_addr = default_map.get_base_addr();
      range.end_addr = highest_addr;
      unmapped_addr_ranges.push_back(range);
    end else begin
      // 0 -> start_addr-1
      if (mapped_addr_ranges[0].start_addr - default_map.get_base_addr() > 0) begin
        range.start_addr = default_map.get_base_addr();
        range.end_addr   = mapped_addr_ranges[0].start_addr - 1;
        unmapped_addr_ranges.push_back(range);
      end

      // all address ranges in the "middle" - only applies if
      // there are more than 1 mapped address ranges
      if (mapped_addr_ranges.size() > 1) begin
        for (int i = 0; i < mapped_addr_ranges.size() - 1; i++) begin
          range.start_addr = mapped_addr_ranges[i].end_addr + 1;
          range.end_addr   = mapped_addr_ranges[i+1].start_addr - 1;
          if (range.start_addr < range.end_addr) begin
            unmapped_addr_ranges.push_back(range);
          end
        end
      end

      // end_addr+1 -> highest_addr
      if (mapped_addr_ranges[$].end_addr < highest_addr) begin
        range.start_addr = mapped_addr_ranges[$].end_addr + 1;
        range.end_addr   = highest_addr;
        unmapped_addr_ranges.push_back(range);
      end
    end
    has_unmapped_addrs = (unmapped_addr_ranges.size() > 0);
  endfunction

  // Return the offset of the highest byte contained in either a register or a memory
  function uvm_reg_addr_t get_max_offset(uvm_reg_map map = null);
    uvm_reg_addr_t max_offset;
    uvm_reg        regs[$];
    uvm_mem        mems[$];

    if (map == null) map = get_default_map();

    get_registers(regs);
    get_memories(mems);
    `DV_CHECK_GT_FATAL(regs.size() + mems.size(), 0)

    // Walk the known registers and memories, calculating the largest byte address visible. Note
    // that the get_offset() calls will return absolute addresses, including any base address in the
    // specified register map.
    max_offset = 0;
    foreach (regs[i]) begin
      max_offset = max2(regs[i].get_offset(map) + regs[i].get_n_bytes() - 1, max_offset);
    end

    foreach (mems[i]) begin
      uvm_reg_addr_t mem_size;
      mem_size = mems[i].get_offset(.map(map)) + mems[i].get_size() * mems[i].get_n_bytes() - 1;
      max_offset = max2(mem_size, max_offset);
    end

    return max_offset;
  endfunction

  // Get the address mask. This should only be called after locking the model (because it depends on
  // the layout of registers and memories in the block).
  function uvm_reg_addr_t get_addr_mask(uvm_reg_map map = null);
    `DV_CHECK_FATAL(is_locked())
    if (map == null) map = get_default_map();
    if (!addr_mask.exists(map)) compute_addr_mask(map);
    return addr_mask[map];
  endfunction

  // Set the base address for the given register map
  //
  // Check that base_addr is aligned as required by the register block. If the supplied base_addr is
  // the "magic" address '1, randomly pick an appropriately aligned base address and set it for the
  // specified map.
  function void set_base_addr(uvm_reg_addr_t base_addr = '1, uvm_reg_map map = null);
    uvm_reg_addr_t mask;

    if (map == null) map = get_default_map();
    mask = get_addr_mask(map);


    // If base_addr is '1, randomly pick an aligned base address
    if (base_addr == '1) begin
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(base_addr, (base_addr & mask) == '0;)
    end

    // Check base addr alignment (which should be guaranteed if we just picked it, but needs
    // checking if not).
    `DV_CHECK_FATAL((base_addr & mask) == '0)
    `uvm_info(`gfn, $sformatf("Setting register base address to 0x%0h", base_addr), UVM_HIGH)
    map.set_base_addr(base_addr);
  endfunction

  // Round the given address down to the start of the containing word. For example, if the address
  // is 'h123, it will be rounded down to 'h120.
  //
  // This is useful if you have a possibly misaligned address and you want to know whether it hits a
  // register (since get_reg_by_offset needs the aligned address for the start of the register).
  function uvm_reg_addr_t get_word_aligned_addr(uvm_reg_addr_t byte_addr);
    uvm_reg_addr_t shift = $clog2(`UVM_REG_BYTENABLE_WIDTH);
    return (byte_addr >> shift) << shift;
  endfunction

  // Get the absolute address (in the default register map) for the given offset. For example, if
  // the base address is 'h100 and offset is 'h13, this will return 'h113 ('h110 if word_aligned is
  // set).
  function uvm_reg_addr_t get_addr_from_offset(uvm_reg_addr_t byte_offset,
                                               bit word_aligned = 1'b1,
                                               uvm_reg_map map = null);
    if (map == null) map = get_default_map();
    return (word_aligned ? get_word_aligned_addr(byte_offset) : byte_offset) + map.get_base_addr();
  endfunction

endclass
