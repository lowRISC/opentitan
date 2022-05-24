// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_scoreboard
  extends dv_base_scoreboard #(.CFG_T(ibex_icache_env_cfg), .COV_T(ibex_icache_env_cov));

  `uvm_component_utils(ibex_icache_scoreboard)

  // TLM agent fifos
  //
  // core_fifo comes from the core monitor. mem_fifo comes from the memory monitor. seed_fifo comes
  // from the memory driver (not monitor) and tells us about new seeds in the backing memory. These
  // are generated in the sequence, but don't cause any change on the interface, so need reporting
  // by the driver.
  uvm_tlm_analysis_fifo #(ibex_icache_core_bus_item) core_fifo;
  uvm_tlm_analysis_fifo #(ibex_icache_mem_bus_item)  mem_fifo;
  uvm_tlm_analysis_fifo #(bit [31:0])                seed_fifo;

  localparam BusWidth = 32;

  // A memory model. Note that the model is stateful (because of the seed). Since we need to try out
  // different seeds to check whether a fetch was correct, we need our own instance, rather than a
  // handle to the model used by the agent. The actual seed inside mem_model is ephemeral: we keep
  // track of state in mem_states, below.
  ibex_icache_mem_model #(BusWidth) mem_model;

  // A queue of memory seeds, together with their associated mem_err_shift values. This gets a new
  // item every time we read a value from seed_fifo, and we store the associated mem_err_shift at
  // that point.
  bit [63:0]   mem_states[$] = {};

  // Tracks the next address we expect to see on a fetch. This gets reset to 'X, then is set to an
  // address after each branch transaction.
  logic [31:0] next_addr;

  // This counter is used for tracking invalidations. When we see an invalidation happen, we set
  // this to the index of the last seed in mem_states. When the next branch happens, we clear out
  // memory seeds up to that index.
  int unsigned invalidate_seed = 0;

  // This counter points to the index (in mem_states) of the seed that was in use when the last
  // branch happened. If the cache is supposed to be disabled, a fetch is only allowed to return
  // data corresponding to that seed or later.
  int unsigned last_branch_seed = 0;

  // A counter of outstanding transactions on the memory bus. The busy flag should never go to zero
  // when this is non-zero.
  int unsigned mem_trans_count = 0;

  // Track the current enabled state. The enabled flag tracks whether the cache is currently
  // enabled. The no_cache flag is high if the cache has been disabled since before the last branch.
  // If this is set, we can be stricter about the data that can be fetched.
  //
  // TODO: Our enable tracking checks that we don't get cache hits when the cache is disabled. It
  //       doesn't yet check that the cache doesn't store fetches when disabled.
  bit          enabled = 0;
  bit          no_cache = 1'b1;

  // Track the current busy state
  bit          busy = 0;

  // Track how well the cache is doing at caching stuff. The basic idea is that every fixed-size
  // window of N instruction fetches, we look to see how many memory requests we've done. We only
  // count fetches and memory requests when the cache is enabled. We reset the window if we see a
  // cache invalidation and then only start counting again once we've seen the busy signal go low.
  //
  // If we get to the end of the window, suppose we've seen I instruction fetches and M words
  // fetched from memory. With random memory data, the expected insns/word is
  // (1/4*1 + 3/4(1/4*3/2+3/4*2)) = 53/32. (1 in 4 instructions is a fully uncompressed instruction
  // and the other three times, it could be 2 fully compressed instructions or 1 compressed and 1
  // uncompressed instruction. The kind of instruction is based on last two bits in the insn_data
  // field). Thus, we define the dimensionless R = (M * 53/32) / I. If R == 1 then our cache hasn't
  // helped at all. If R is large, something has gone horribly wrong. If R is small, our cache has
  // avoided lots of lookups.
  //
  // We can get a lower-bound estimate of the cache hit rate we'd expect by tracking the addresses
  // that we saw in our window (lowest and highest addresses fetched). Suppose this range contains K
  // words and our cache is large enough to hold C words. Then we should expect to see lots of cache
  // hits if K <= C and N >> C. ("We fetched enough from a small enough range").
  //
  // This check is intentionally very loose. We assume the cache is at least 1kB (the default
  // configuration is 4kB), so C = 256 and we'll pick K = 250 (called max_window_width below). To
  // pick N (called window_len below), note that 53/32 * C * 2 ~= 848, so we should expect to see an
  // instruction repeated at least twice on average once we've seen N = 850 fetches. With perfect
  // caching and each instruction fetched twice, you would expect an R of 0.5, so we will require R
  // <= 2/3. With each instruction fetched twice, this corresponds to the cache having the second
  // instruction half the time.
  //
  // Note that we also reset the window if we see an error. If this happens, it's easy to see "read
  // amplification" where the cache reads a couple of fill buffers' worth of data and we only
  // actually get one instruction.
  protected int unsigned max_window_width = 250;
  protected int unsigned window_len       = 850;

  // The number of instructions seen in the current window.
  protected int unsigned insns_in_window;

  // The number of memory reads seen in the current window
  protected int unsigned reads_in_window;

  // Set if we've seen busy_o == 0 since the last invalidation (so we know that the cache isn't
  // currently invalidating)
  protected bit not_invalidating;

  // Address range seen in the current window
  protected bit [31:0] window_range_lo, window_range_hi;

  // Set by check_compatible_1/check_compatible_2 on a hit. Gives the "age" of the seed
  // corresponding to the last fetch. If the hit matched the most recent version of the seed, the
  // "age" is zero. For the next most recent version, it's one and so on.
  protected int unsigned last_fetch_age;

  // The number of fetches that might have had an old seed and the number that actually did.
  int unsigned possible_old_count = 0;
  int unsigned actual_old_count = 0;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    core_fifo = new("core_fifo", this);
    mem_fifo  = new("mem_fifo",  this);
    seed_fifo = new("seed_fifo", this);
    mem_model = new("mem_model", cfg.mem_agent_cfg.disable_mem_errs);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);

    mem_states.push_back({32'd0, cfg.mem_agent_cfg.mem_err_shift});
    tracking_reset();
    fork
      process_core_fifo();
      process_mem_fifo();
      process_seed_fifo();
      monitor_negedge_reset();
    join_none
  endtask

  task process_core_fifo();
    ibex_icache_core_bus_item item;
    forever begin
      core_fifo.get(item);
      `uvm_info(`gfn, $sformatf("received core transaction:\n%0s", item.sprint()), UVM_HIGH)
      case (item.trans_type)
        ICacheCoreBusTransTypeBranch:     process_branch(item);
        ICacheCoreBusTransTypeFetch:      process_fetch(item);
        ICacheCoreBusTransTypeInvalidate: process_invalidate(item);
        ICacheCoreBusTransTypeEnable:     process_enable(item);
        ICacheCoreBusTransTypeBusy:       process_busy(item);
        default: `uvm_fatal(`gfn, $sformatf("Bad transaction type %0d", item.trans_type))
      endcase
    end
  endtask

  task process_branch(ibex_icache_core_bus_item item);
    next_addr = item.address;

    if (invalidate_seed > 0) begin
      // We've seen an invalidate signal recently. Clear out any expired seeds.
      assert(invalidate_seed < mem_states.size);
      mem_states = mem_states[invalidate_seed:$];
      invalidate_seed = 0;
    end

    assert(mem_states.size > 0);
    last_branch_seed = mem_states.size - 1;

    if (!enabled) no_cache = 1'b1;
  endtask

  task process_fetch(ibex_icache_core_bus_item item);
    // Check that the address is what we expect
    `DV_CHECK_EQ(item.address, next_addr)

    // Update expected address, incrementing by 2 or 4.
    next_addr = next_addr + ((item.insn_data[1:0] == 2'b11) ? 32'd4 : 32'd2);

    // Check the received data is compatible with one of our seeds
    check_compatible(item);

    // Do any caching tracking for this fetch
    window_take_insn(item.address, item.err);
  endtask

  task process_invalidate(ibex_icache_core_bus_item item);
    assert(mem_states.size > 0);
    invalidate_seed = mem_states.size - 1;

    not_invalidating = 1'b0;
    window_reset();
  endtask

  task process_enable(ibex_icache_core_bus_item item);
    enabled = item.enable;
    if (enabled) no_cache = 0;
  endtask

  task process_busy(ibex_icache_core_bus_item item);
    busy = item.busy;
    if (!busy) begin
      busy_check();
      not_invalidating = 1'b1;
    end
  endtask

  task process_mem_fifo();
    ibex_icache_mem_bus_item item;
    forever begin
      mem_fifo.get(item);
      `uvm_info(`gfn, $sformatf("received mem transaction:\n%0s", item.sprint()), UVM_HIGH)

      // Looks like we are in reset. Discard the item.
      if (!cfg.clk_rst_vif.rst_n) continue;

      if (item.is_grant) begin
        mem_trans_count += 1;
        window_take_mem_read();
      end else begin
        busy_check();
        `DV_CHECK_FATAL(mem_trans_count > 0);
        mem_trans_count -= 1;
      end
    end
  endtask

  task process_seed_fifo();
    int unsigned seed;
    forever begin
      seed_fifo.get(seed);
      `uvm_info(`gfn,
                $sformatf("received new seed: %08h; mem_err_shift: %0d",
                          seed, cfg.mem_agent_cfg.mem_err_shift),
                UVM_HIGH)
      mem_states.push_back({seed, cfg.mem_agent_cfg.mem_err_shift});
    end
  endtask

  // Trigger start_reset on every negedge of the reset line. Never returns.
  task monitor_negedge_reset();
    forever begin
      @(negedge cfg.clk_rst_vif.rst_n) start_reset();
    end
  endtask

  // A function called on negedge of rst_n
  function void start_reset();
    next_addr = 'X;

    // Throw away any old seeds
    invalidate_seed = mem_states.size - 1;
    mem_states = mem_states[invalidate_seed:$];
    invalidate_seed = 0;
    last_branch_seed = 0;

    // Forget about any pending bus transactions (they've been thrown away anyway)
    mem_trans_count = 0;
  endfunction

  // Called on the posedge of rst_n which ends the reset period.
  function void reset(string kind = "HARD");
    super.reset(kind);
    tracking_reset();
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(ibex_icache_core_bus_item, core_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(ibex_icache_mem_bus_item,  mem_fifo)
  endfunction

  // Check whether observed fetched instruction data matches the given single memory fetch.
  //
  // This is used to check aligned accesses or misaligned accesses where we saw an error in the
  // lower word or where the lower 16 bits of instruction data give a compressed instruction. If
  // chatty is true, print a message about why the fetch is compatible or not (used to help
  // debugging failures)
  function automatic logic is_fetch_compatible_1(logic [31:0] seen_insn_data,
                                                 logic        seen_err,

                                                 bit          exp_err,
                                                 bit [31:0]   exp_insn_data,

                                                 bit [31:0]   seed,
                                                 bit          chatty);

    logic is_compressed;

    if (exp_err) begin
      if (!seen_err) begin
        // The (lower) memory fetch should have failed, but we haven't got an error flag.
        if (chatty) begin
          `uvm_info(`gfn,
                    $sformatf("Not seed 0x%08h: expected seen_err but saw 0.", seed),
                    UVM_LOW)
        end
        return 0;
      end

      // If we have seen an expected error, that's a match (and we shouldn't have gone around again
      // with the chatty flag set)
      `DV_CHECK_FATAL(!chatty)

      return 1'b1;
    end

    if (seen_err) begin
      if (chatty) begin
        `uvm_info(`gfn,
                  $sformatf("Not seed 0x%08h: got unexpected error flag.", seed),
                  UVM_LOW)
      end
      return 0;
    end

    is_compressed = exp_insn_data[1:0] != 2'b11;
    if (is_compressed) begin
      if (seen_insn_data[15:0] != exp_insn_data[15:0]) begin
        if (chatty) begin
          `uvm_info(`gfn,
                    $sformatf("Not seed 0x%08h (expected cmp 0x(%04h)%04h; saw 0x(%04h)%04h).",
                              seed, exp_insn_data[31:16], exp_insn_data[15:0],
                              seen_insn_data[31:16], seen_insn_data[15:0]),
                    UVM_LOW)
        end
        return 0;
      end
    end else begin
      if (seen_insn_data != exp_insn_data) begin
        if (chatty) begin
          `uvm_info(`gfn,
                    $sformatf("Not seed 0x%08h (expected uncomp 0x%08h; saw 0x%08h).",
                              seed, exp_insn_data, seen_insn_data),
                    UVM_LOW)
        end
        return 0;
      end
    end

    // This seed matches, so we shouldn't have been called with the chatty flag set.
    `DV_CHECK_FATAL(!chatty)
    return 1'b1;
  endfunction

  // Check whether observed fetched instruction data matches the given pair of memory fetches.
  //
  // This is used to check misaligned accesses where the instruction data gives an uncompressed
  // instruction. If chatty is true, print a message about why the fetch is compatible or not (used
  // to help debugging failures)
  function automatic logic is_fetch_compatible_2(logic [31:0] seen_insn_data,
                                                 logic        seen_err_plus2,

                                                 bit          exp_err_lo,
                                                 bit          exp_err_hi,
                                                 bit [31:0]   exp_insn_data,

                                                 bit [31:0]   seed_lo,
                                                 bit [31:0]   seed_hi,
                                                 bit          chatty);

    // We should only be called when the seen instruction data for the lower word is uncompressed
    assert(seen_insn_data[1:0] == 2'b11);

    if (exp_err_lo) begin
      if (chatty) begin
        `uvm_info(`gfn,
                  $sformatf("Not seeds 0x%08h/0x%08h (expected error in low word).",
                            seed_lo, seed_hi),
                  UVM_LOW)
      end
      return 0;
    end

    if (exp_err_hi != seen_err_plus2) begin
      if (chatty) begin
        `uvm_info(`gfn,
                  $sformatf("Not seeds 0x%08h/0x%08h (exp/seen top errors %0d/%0d).",
                            seed_lo, seed_hi, exp_err_hi, seen_err_plus2),
                  UVM_LOW)
      end
      return 0;
    end

    if (exp_err_hi) begin
      if (chatty) begin
        `uvm_info(`gfn,
                  $sformatf("Match for seeds 0x%08h/0x%08h (seen upper error).",
                            seed_lo, seed_hi),
                  UVM_LOW)
      end
      return 1'b1;
    end

    // No errors seen or expected. Check the data matches (for a full uncompressed insn)
    if (exp_insn_data != seen_insn_data) begin
      if (chatty) begin
        `uvm_info(`gfn,
                  $sformatf("Not seeds 0x%08h/0x%08h (exp/seen data 0x%08h/0x%08h).",
                            seed_lo, seed_hi, exp_insn_data, seen_insn_data),
                  UVM_LOW)
      end
      return 0;
    end

    // This seed matches, so we shouldn't have been called with the chatty flag set.
    `DV_CHECK_FATAL(!chatty)

    return 1'b1;

  endfunction

  // Do a single read from the memory model, rounding down the address and re-aligning the returned
  // data if necessary. Use is_fetch_compatible_1 to decide whether the result seen is compatible
  // with the seed.
  function automatic logic is_state_compatible_1(logic [31:0] address,
                                                 logic [31:0] seen_insn_data,
                                                 logic        seen_err,
                                                 bit [63:0]   mem_state,
                                                 bit          chatty);
    int                bus_shift;
    logic [31:0]       addr_lo;
    int unsigned       lo_bits_to_drop;

    logic              retval;

    bit [BusWidth-1:0] rdata;

    bit [31:0]         seed;
    int unsigned       mem_err_shift;      

    bus_shift = $clog2(BusWidth / 8);
    addr_lo = (address >> bus_shift) << bus_shift;

    // If address is not aligned to BusWidth, the aligned read that we do from mem_model will have
    // some data that needs shifting out of the way. We'll fill the top with zeroes, but that's fine
    // because we only use this function for misaligned accesses if seen_insn_data looks like it's a
    // compressed instruction, in which case we don't care about the top bits anyway.
    lo_bits_to_drop = 8 * (address - addr_lo);

    {seed, mem_err_shift} = mem_state;
    rdata = mem_model.read_data(seed, addr_lo) >> lo_bits_to_drop;

    return is_fetch_compatible_1(seen_insn_data,
                                 seen_err,
                                 mem_model.is_mem_error(seed, addr_lo, mem_err_shift),
                                 rdata[31:0],
                                 seed,
                                 chatty);
  endfunction

  // Do a pair of reads from the memory model with the given pair of seeds to model a misaligned
  // access. Glue together the results and pass them to is_fetch_compatible_2 to decide whether the
  // result seen is compatible with the given pair of seeds.
  function automatic logic is_state_compatible_2(logic [31:0] address,
                                                 logic [31:0] seen_insn_data,
                                                 logic        seen_err_plus2,

                                                 bit [63:0]   mem_state_lo,
                                                 bit [63:0]   mem_state_hi,
                                                 bit          chatty);
    int          bus_shift;
    logic [31:0] addr_lo, addr_hi;

    bit                exp_err_lo, exp_err_hi;
    bit [31:0]         exp_data;
    bit [BusWidth-1:0] rdata;

    int unsigned lo_bits_to_take, lo_bits_to_drop;

    bit [31:0]         seed_lo, seed_hi;
    int unsigned       mem_err_shift_lo, mem_err_shift_hi;

    bus_shift = $clog2(BusWidth / 8);
    addr_lo = (address >> bus_shift) << bus_shift;
    addr_hi = addr_lo + (32'd1 << bus_shift);

    // This is only supposed to be used for misaligned reads
    assert (addr_lo < address);

    // How many bits do we get from each read? (Note that for half-word aligned reads on a 32-bit
    // bus, both of these numbers will be 16, but this code should be correct with other values of
    // BusWidth).
    lo_bits_to_take = 8 * (address - addr_lo);
    lo_bits_to_drop = BusWidth - lo_bits_to_take;

    {seed_lo, mem_err_shift_lo} = mem_state_lo;
    {seed_hi, mem_err_shift_hi} = mem_state_hi;

    // Do the first read (from the low address) and shift right to drop the bits that we don't need.
    exp_err_lo = mem_model.is_mem_error(seed_lo, addr_lo, mem_err_shift_lo);
    rdata      = mem_model.read_data(seed_lo, addr_lo) >> lo_bits_to_drop;
    exp_data   = rdata[31:0];

    // Now do the second read (from the upper address). Shift the result up by lo_bits_to_take,
    // which will discard some top bits. Then extract 32 bits and OR with what we have so far.
    exp_err_hi = mem_model.is_mem_error(seed_hi, addr_hi, mem_err_shift_hi);
    rdata      = mem_model.read_data(seed_hi, addr_hi) << lo_bits_to_take;
    exp_data   = exp_data | rdata[31:0];

    return is_fetch_compatible_2(seen_insn_data, seen_err_plus2,
                                 exp_err_lo, exp_err_hi, exp_data,
                                 seed_lo, seed_hi, chatty);
  endfunction

  // The logic to check whether a fetch that's been seen is compatible with some memory state that's
  // visible at the moment.
  function automatic bit check_compatible_1(logic [31:0] address,
                                            logic [31:0] seen_insn_data,
                                            logic        seen_err,
                                            int unsigned min_idx,
                                            bit          chatty);

    for (int unsigned i = min_idx; i < mem_states.size; i++) begin
      if (is_state_compatible_1(address, seen_insn_data, seen_err, mem_states[i], chatty)) begin
        last_fetch_age = mem_states.size - 1 - i;
        return 1'b1;
      end
    end

    return 1'b0;
  endfunction

  // The logic to check whether a fetch that's been seen is compatible with some pair of memory
  // states that are visible at the moment.
  function automatic bit check_compatible_2(logic [31:0] address,
                                            logic [31:0] seen_insn_data,
                                            logic        seen_err_plus2,
                                            int unsigned min_idx,
                                            bit          chatty);

    // We want to iterate over all pairs of states. We can do this with a nested pair of foreach
    // loops, but we expect that usually we'll get a hit on the "diagonal", so we check that first.
    for (int unsigned i = min_idx; i < mem_states.size; i++) begin
      if (is_state_compatible_2(address, seen_insn_data, seen_err_plus2,
                                mem_states[i], mem_states[i], chatty)) begin
        last_fetch_age = mem_states.size - 1 - i;
        return 1'b1;
      end
    end
    for (int unsigned i = min_idx; i < mem_states.size; i++) begin
      for (int unsigned j = min_idx; j < mem_states.size; j++) begin
        if (i != j) begin
          if (is_state_compatible_2(address, seen_insn_data, seen_err_plus2,
                                    mem_states[i], mem_states[j], chatty)) begin
            last_fetch_age = mem_states.size - 1 - (i < j ? i : j);
            return 1'b1;
          end
        end
      end
    end
  endfunction

  // Check whether a fetch might be correct.
  task automatic check_compatible(ibex_icache_core_bus_item item);
    logic misaligned;
    logic good_bottom_word;
    logic uncompressed;
    int unsigned min_idx;

    bit [31:0]   last_seed;
    int unsigned last_mem_err_shift;

    misaligned       = (item.address & 3) != 0;
    good_bottom_word = (~item.err) | item.err_plus2;
    uncompressed     = item.insn_data[1:0] == 2'b11;

    min_idx          = no_cache ? last_branch_seed : 0;
    `DV_CHECK_LT_FATAL(min_idx, mem_states.size);

    // If the current value of mem_err_shift in the configuration object doesn't match the back of
    // mem_states, append a fake entry with the same seed, but the current mem_err_shift.
    {last_seed, last_mem_err_shift} = mem_states[mem_states.size() - 1];
    if (last_mem_err_shift != cfg.mem_agent_cfg.mem_err_shift) begin
      `uvm_info(`gfn,
                $sformatf("Change of mem_err_shift (%0d -> %0d) with no new seed.",
                          last_mem_err_shift, cfg.mem_agent_cfg.mem_err_shift),
                UVM_HIGH)
      mem_states.push_back({last_seed, cfg.mem_agent_cfg.mem_err_shift});
    end

    if (misaligned && good_bottom_word && uncompressed) begin
      // It looks like this was a misaligned fetch (so came from two fetches from memory) and the
      // bottom word's fetch succeeded, giving an uncompressed result (so we care about the upper
      // fetch).
      logic err = item.err & item.err_plus2;
      if (!check_compatible_2(item.address, item.insn_data, err, min_idx, 1'b0)) begin
        void'(check_compatible_2(item.address, item.insn_data, err, min_idx, 1'b1));
        `uvm_error(`gfn,
                   $sformatf("Fetch at address 0x%08h got data incompatible with available seeds.",
                             item.address));
      end
    end else begin
      // The easier case: either the fetch was aligned, the lower word seems to have caused an error
      // or the bits in the lower word are a compressed instruction (so we don't care about the
      // upper 16 bits anyway).
      if (!check_compatible_1(item.address, item.insn_data, item.err, min_idx, 1'b0)) begin
        void'(check_compatible_1(item.address, item.insn_data, item.err, min_idx, 1'b1));
        `uvm_error(`gfn,
                   $sformatf("Fetch at address 0x%08h got data incompatible with available seeds.",
                             item.address));
      end
    end

    // All is well. The call to check_compatible_* will have set last_fetch_age. The maximum
    // possible value is mem_states.size - 1 - min_idx. If this is positive, count whether we got a
    // value corresponding to an old seed or not.
    if (mem_states.size > min_idx + 1) begin
      possible_old_count += 1;
      if (last_fetch_age > 0) actual_old_count += 1;
    end

  endtask

  // Check that the busy line isn't low when there are outstanding memory transactions
  //
  // Since we're operating in the world of transactions (with no clock edges to guide us), we have
  // to be careful about ordering: if the device had been quiescent and it is now issuing a memory
  // transaction, we might see the request be granted before we see the busy pin go high.
  //
  // To avoid this problem, we actually run the check when
  //
  //     (a) The busy line goes low
  //     (b) Just before a pending request gets a response
  //
  // Suppose that at some point the check would fail. Then it can only start passing again if either
  // the busy line goes high or if the last pending request gets a response. The times above mean
  // we'll spot immediately if the busy line goes low when there are pending transactions. We'll
  // also spot a bug where a request goes out and gets a response before the busy line goes high.
  //
  // We'll miss cases where the busy line is slow to go high, but still manages to do so before the
  // response comes back.
  //
  // TODO: Is this ok (because sometimes the memory will come back quick enough to catch us) or do
  //       we need to do something cleverer? For example, we could have an SVA property (bound into
  //       the design, or at testbench level) that checked the busy pin was high the cycle after a
  //       request went out.

  task automatic busy_check();
    if (mem_trans_count > 0) begin
      `DV_CHECK(busy,
                $sformatf("Busy line low with %d outstanding memory transactions.",
                          mem_trans_count))
    end
  endtask

  // Completely reset cache tracking, waiting for busy to drop to be certain that invalidation is
  // done
  function automatic void tracking_reset();
    not_invalidating = 1'b0;
    window_reset();
  endfunction

  // Reset the caching tracking window
  function automatic void window_reset();
    insns_in_window = 0;
    reads_in_window = 0;
    window_range_lo = ~(31'b0);
    window_range_hi = 0;
  endfunction

  // Is the caching tracking window is currently enabled?
  function automatic bit window_enabled();
    // The window is enabled if the cache is enabled and we know we're not still invalidating.
    return enabled & not_invalidating;
  endfunction

  // Register an instruction fetch with the caching tracking window
  function automatic void window_take_insn(bit [31:0] addr, bit err);
    bit [32:0]   window_width;
    int unsigned fetch_ratio_pc;

    // Ignore instructions and reset the window if this check is disabled in the configuration.
    // Resetting the window each time avoids cases where we run an ECC sequence for a while (where
    // the check should be disabled), then switch to a normal sequence (where the check should be
    // enabled) just before the window finishes.
    //
    // Similarly, bail on an error since that would significantly lower the cache hit ratio.
    if (err || cfg.disable_caching_ratio_test) begin
      window_reset();
      return;
    end

    if (window_enabled()) begin
      insns_in_window++;
      if (addr < window_range_lo) window_range_lo = addr;
      if (addr > window_range_hi) window_range_hi = addr;
    end

    if (insns_in_window < window_len) begin
      return;
    end

    // We have a full window. Has the address range been sufficiently small? The fatal check is for
    // the scoreboard logic: this should hold true as soon as we've seen an instruction.
    `DV_CHECK_LE_FATAL(window_range_lo, window_range_hi);
    window_width = ({1'b0, window_range_hi} - {1'b0, window_range_lo} + 33'd3) / 4;

    `uvm_info(`gfn,
              $sformatf("Completed window with %0d insns and %0d reads, range [0x%08h, 0x%08h].",
                        insns_in_window, reads_in_window, window_range_lo, window_range_hi),
              UVM_HIGH)

    if (window_width[31:0] <= max_window_width) begin
      // The range has been small enough, so we can actually check whether the caching is working.
      // Calculate the R we've seen (as a percentage).
      fetch_ratio_pc = (reads_in_window * 100 * 53 / 32) / insns_in_window;

      `uvm_info(`gfn, $sformatf("Fetch ratio %0d%%", fetch_ratio_pc), UVM_HIGH)
      `DV_CHECK(fetch_ratio_pc <= 67,
                $sformatf({"Fetch ratio too high (%0d%%; max allowed 67%%) with ",
                           "%0d instructions and address range [0x%08h, 0x%08h] ",
                           "(window width %0d)"},
                          fetch_ratio_pc, insns_in_window,
                          window_range_lo, window_range_hi, window_width[31:0]))
    end

    // Start the next window
    window_reset();
  endfunction

  // Register a memory read with the caching tracking window
  function automatic void window_take_mem_read();
    if (window_enabled()) reads_in_window += 1;
  endfunction

endclass
