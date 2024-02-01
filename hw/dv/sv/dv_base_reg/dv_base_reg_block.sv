// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// base register block class which will be used to generate the reg blocks
class dv_base_reg_block extends uvm_reg_block;
  `uvm_object_utils(dv_base_reg_block)

  // The default addr, data and byte widths.
  //
  // The UVM reg data structures are built on `UVM_REG_ADDR|DATA|BYTEENABLE_WIDTH settings which
  // are compile time, i.e. fixed for all RAL models across the project. What if we have multiple
  // RAL models that have different width needs? The solution is to let the UVM data structures be
  // created with large enough widths to accommodate a heterogeneous set of RAL models, and use
  // these runtime settings below instead, to perform associated computations. Values retrieved
  // for comparisons, such as uvm_reg::get_mirrored_value() may return data that is wider than
  // needed. It would then be upto the testbench to cast it to the appropriate width if necessary.
  // TODO: These are ideally passed via `build` method.
  uint addr_width = `UVM_REG_ADDR_WIDTH;
  uint data_width = `UVM_REG_DATA_WIDTH;
  uint be_width = `UVM_REG_BYTENABLE_WIDTH;

  // Since an IP may contains more than one reg block we construct reg_block name as
  // {ip_name}_{reg_interface_name}.
  // All the reg_blocks in the IP share the same alert. In top-level, We construct the alert
  // name as {ip_name}_{alert_name}. Hence, we need this ip_name in reg_block
  local string ip_name;

  // CSR exclusion object that holds exclusion tags for the sub-blocks, CSRs and fields.
  protected csr_excl_item csr_excl;

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

  // Indicates whether accesses to unmapped regions of this block returns an error response (0).
  protected bit unmapped_access_ok;

  // Indicates whether byte writes are supported (enabled by default).
  // TODO: Remove this in future - this is really a property of the physical interface that is used
  // to access design through this RAL model (a.k.a, the map & adapter), and not the RAL model
  // itself. This information should be sought using uvm_reg_adapter::supports_byte_enable instead.
  // This is added for ease of rv_dm testbench development.
  protected bit supports_byte_enable = 1'b1;

  // Custom RAL models may support sub-word CSR writes smaller than CSR width.
  protected bit supports_sub_word_csr_writes = 1'b0;

  // Enables functional coverage of comportable IP-specific specialized registers, such as regwen
  // and mubi. This flag can only be disabled before invoking `create_dv_reg_cov`.
  protected bit en_dv_reg_cov = 1;

  bit has_unmapped_addrs;
  addr_range_t unmapped_addr_ranges[$];

  // Lookup table for alias registers and fields.
  string register_alias_lookup[string];
  string field_alias_lookup[string];

  function new (string name = "", int has_coverage = UVM_NO_COVERAGE);
    super.new(name, has_coverage);
  endfunction

  function void set_ip_name(string name);
    ip_name = name;
  endfunction

  function string get_ip_name();
    // `DV_CHECK_NE_FATAL can't take "" as an input
    string empty_str = "";
    `DV_CHECK_NE_FATAL(ip_name, empty_str, "ip_name hasn't been set yet")
    return ip_name;
  endfunction

  // Returns the CSR exclusion item attached to the block.
  virtual function csr_excl_item get_excl_item();
    return csr_excl;
  endfunction

  function void set_unmapped_access_ok(bit ok);
    unmapped_access_ok = ok;
  endfunction

  function bit get_unmapped_access_ok();
    return unmapped_access_ok;
  endfunction

  function void set_supports_byte_enable(bit enable);
    supports_byte_enable = enable;
  endfunction

  function bit get_supports_byte_enable();
    return supports_byte_enable;
  endfunction

  function void set_supports_sub_word_csr_writes(bit enable);
    supports_sub_word_csr_writes = enable;
  endfunction

  function bit get_supports_sub_word_csr_writes();
    return supports_sub_word_csr_writes;
  endfunction

  // provide build function to supply base addr
  virtual function void build(uvm_reg_addr_t base_addr,
                              csr_excl_item csr_excl = null);
    `uvm_fatal(`gfn, "this method is not supposed to be called directly!")
  endfunction

  // This function is invoked at the end of `build` method in uvm_reg_base.sv template to create
  // IP-specific functional coverage for this block and its registers and fields.
  function void create_cov();
    dv_base_reg_block blks[$];
    dv_base_reg regs[$];

    get_dv_base_reg_blocks(blks);
    foreach (blks[i]) blks[i].create_cov();

    get_dv_base_regs(regs);
    foreach (regs[i]) regs[i].create_cov();
    // Create block-specific covergroups here.
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

  function bit has_shadowed_regs();
    dv_base_reg regs[$];
    get_shadowed_regs(regs);
    return (regs.size() > 0);
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

    // Assumption:
    // Only chip-level RAL has multiple sub reg_blocks. Its addr_mask is '1
    // In block-level, we have one RAL for one TLUL interface. We don't put multiple reg_block in a
    // RAL, as UVM RAL can't handle the case that each sub-block uses a different map:
    //  - ral.blk1 -> use map_TL1
    //  - ral.blk2 -> use map_TL2
    get_blocks(blocks);
    if (blocks.size > 0) begin // if true, this is a chip-level RAL
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
    `uvm_info(`gfn, $sformatf("csr_addrs: %0p", csr_addrs), UVM_HIGH)
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
    `uvm_info(`gfn, $sformatf("mem_ranges: %0p", mem_ranges), UVM_HIGH)
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
    `uvm_info(`gfn, $sformatf("mapped_addr_ranges: %0p", mapped_addr_ranges), UVM_HIGH)
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
    `uvm_info(`gfn, $sformatf("unmapped_addr_ranges: %0p", unmapped_addr_ranges), UVM_HIGH)
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
  // Checks if the provided base_addr is aligned as required by the register block. If
  // randomize_base_addr arg is set, then the base_addr arg is ignored - the function randomizes and
  // sets the base_addr itself.
  function void set_base_addr(uvm_reg_addr_t base_addr, uvm_reg_map map = null,
                              bit randomize_base_addr = 0);
    uvm_reg_addr_t mask;

    if (map == null) map = get_default_map();
    mask = get_addr_mask(map);

    // If randomize_base_addr is set, randomly pick an aligned base address.
    if (randomize_base_addr) begin
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(base_addr,
                                         (base_addr & mask) == '0;
                                         base_addr >> addr_width == 0;)
    end else begin
      `DV_CHECK_FATAL((base_addr & mask) == '0)
      `DV_CHECK_FATAL((base_addr >> addr_width) == '0)
    end

    `uvm_info(`gfn, $sformatf("Setting register base address to 0x%0h", base_addr), UVM_HIGH)
    map.set_base_addr(base_addr);
  endfunction

  // Round the given address down to the start of the containing word. For example, if the address
  // is 'h123, it will be rounded down to 'h120.
  //
  // This is useful if you have a possibly misaligned address and you want to know whether it hits a
  // register (since get_reg_by_offset needs the aligned address for the start of the register).
  function uvm_reg_addr_t get_word_aligned_addr(uvm_reg_addr_t byte_addr);
    uvm_reg_addr_t shift = $clog2(be_width);
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

  // The design ignores the address bits that aren't enabled by addr_mask.
  // Normalize these ignored bits to enable locating which CSR/mem is at the returned address.
  function uvm_reg_addr_t get_normalized_addr(uvm_reg_addr_t byte_addr, uvm_reg_map map = null);
    if (map == null) map = get_default_map();
    return get_addr_from_offset(.byte_offset(byte_addr & addr_mask[map]),
                                .word_aligned(1),
                                .map(map));
  endfunction

  // Set default map for this block and all its sub-blocks by name.
  // This function only works if user is setting default map for all blocks under the hierarchy
  // with the same map name.
  function void set_default_map_w_subblks_by_name(string map_name);
    dv_base_reg_block subblks[$];
    uvm_reg_map map = this.get_map_by_name(map_name);
    `DV_CHECK(map != null)
    this.set_default_map(map);

    get_dv_base_reg_blocks(subblks);
    foreach (subblks[i]) subblks[i].set_default_map_w_subblks_by_name(map_name);
  endfunction

  // this overrides the get_reg_by_name function
  function dv_base_reg get_reg_by_name(string name);
    dv_base_reg retval;
    if (register_alias_lookup.exists(name)) begin
      `downcast(retval, super.get_reg_by_name(register_alias_lookup[name]))
    end else begin
      `downcast(retval, super.get_reg_by_name(name))
    end
    return retval;
  endfunction

  // this overrides the get_field_by_name function
  // note however that this function is only meaningful if the fields are unique within a regblock!
  function dv_base_reg_field get_field_by_name(string name);
    dv_base_reg_field retval;
    if (field_alias_lookup.exists(name)) begin
      `downcast(retval, super.get_field_by_name(field_alias_lookup[name]))
    end else begin
      `downcast(retval, super.get_field_by_name(name))
    end
    return retval;
  endfunction

  function void set_en_dv_reg_cov(bit val);
    uvm_reg csrs[$];
    get_registers(csrs);
    `DV_CHECK_FATAL(!csrs.size(),
        "Cannot set en_dv_base_reg_cov when covergroups are built already!")
    en_dv_reg_cov = val;
  endfunction

  function bit get_en_dv_reg_cov();
    return en_dv_reg_cov;
  endfunction

endclass
