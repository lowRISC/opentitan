// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_core_base_seq extends dv_base_seq #(
    .REQ         (ibex_icache_core_req_item),
    .RSP         (ibex_icache_core_rsp_item),
    .CFG_T       (ibex_icache_core_agent_cfg),
    .SEQUENCER_T (ibex_icache_core_sequencer)
  );
  `uvm_object_utils(ibex_icache_core_base_seq)

  `uvm_object_new

  // Non-null if this is an item after the first in a "combo" run, which runs several of these
  // sequences back-to-back. Must be set before pre_start to have any effect.
  ibex_icache_core_base_seq prev_sequence = null;

  // If this is set, any branch target address should be within 64 bytes of base_addr and runs of
  // instructions should have a maximum length of 100.
  bit constrain_branches = 1'b0;

  // Should the cache be enabled for the first fetch? Probably only interesting if you also set
  // const_enable.
  bit initial_enable = 1'b0;

  // If this bit is set, we will never change whether the cache is enabled from the initial_enable
  // setting.
  bit const_enable = 1'b0;

  // If this bit is set, the next request will invalidate the cache.
  bit must_invalidate = 1'b0;

  // If this bit is set, we will never invalidate the cache (useful for hit ratio tracking), except
  // if must_invalidate is set.
  bit avoid_invalidation = 1'b0;

  // The expected number of items between each new memory seed when the cache is disabled. A new
  // memory seed when the cache is disabled implies that the next time the cache is enabled, we must
  // start an invalidation. As such, this shouldn't normally be set too low.
  int unsigned gap_between_seeds = 49;

  // The expected number of items between each invalidation. This shouldn't be too small because an
  // invalidation takes ages and we don't want to accidentally spend most of the test waiting for
  // invalidation.
  int unsigned gap_between_invalidations = 49;

  // The expected number of items between enable/disable toggles.
  int unsigned gap_between_toggle_enable = 49;

  // Number of test items (note that a single test item may contain many instruction fetches)
  //
  // The default value is for convenience. This should be constrained by whatever virtual sequence
  // is using the core sequence.
  int unsigned num_trans = 1000;

  // The base address used when constrain_branches is true.
  protected rand bit[31:0] base_addr;

  // The top of the possible range of addresses used when constrain_branches is true. Set at the
  // start of body().
  protected bit [31:0] top_restricted_addr;

  // Distribution for base_addr which adds extra weight to each end of the address space
  constraint c_base_addr { base_addr dist { [0:15]                      :/ 1,
                                            [16:32'hfffffff0]           :/ 2,
                                            [32'hfffffff0:32'hffffffff] :/ 1 }; }

  // Make sure that base_addr is even (otherwise you can fail to generate items if you pick a base
  // addr of 32'hffffffff with constrained addresses enabled: the only address large enough is
  // 32'hffffffff, but it doesn't have a zero bottom bit).
  constraint c_base_addr_alignment {
    // The branch address is always required to be half-word aligned. We don't bother conditioning
    // this on the type of transaction because branch_addr is forced to be zero in anything but a
    // branch transaction.
    !base_addr[0];
  }

  // If this is set, the next request should be constrained to have trans_type
  // ICacheCoreTransTypeBranch. It's initially 1 because the core must start with a branch to tell
  // the cache where to fetch from in the first place.
  protected bit force_branch = 1'b1;

  // A count of the number of instructions fetched since the last branch. This is only important
  // when constrain_branches is true, in which case we want to ensure that we don't fetch too much
  // in a straight line between branches.
  protected int unsigned insns_since_branch = 0;

  // Whether the cache is enabled at the moment
  protected bit cache_enabled;

  // Whether the cache must be invalidated next time it is enabled (because we changed the seed
  // under its feet while it was disabled)
  protected bit stale_seed = 0;

  virtual task body();
    // Set cache_enabled from initial_enable here (rather than at the declaration). This way, a user
    // can set initial_enable after constructing the sequence, but before running it.
    cache_enabled = initial_enable;

    // If constrain_branches is true, any branch must land in [base_addr:(base_addr + 64)]. We need
    // to make sure that this doesn't wrap, though.
    top_restricted_addr = (base_addr <= (32'hffffffff - 64)) ? base_addr + 64 : 32'hffffffff;

    run_reqs();
  endtask

  // Generate and run a single item using class parameters
  protected virtual task run_req(ibex_icache_core_req_item req, ibex_icache_core_rsp_item rsp);
    start_item(req);

    if (constrain_branches && insns_since_branch >= 100)
      force_branch = 1'b1;

    `DV_CHECK_RANDOMIZE_WITH_FATAL(
       req,

       // Force a branch if necessary
       force_branch -> req.trans_type == ICacheCoreTransTypeBranch;

       // If this is a branch and constrain_branches is true then constrain any branch target.
       (constrain_branches && (req.trans_type == ICacheCoreTransTypeBranch)) ->
         req.branch_addr inside {[base_addr:top_restricted_addr]};

       // If this is a branch and constrain_branches is false, we don't constrain the branch target,
       // but we do weight the bottom and top of the address space a bit higher. This is a weaker
       // version of the weighting that we place on base_addr.
       (!constrain_branches && (req.trans_type == ICacheCoreTransTypeBranch)) ->
         req.branch_addr dist { [0:63]                      :/ 1,
                                [64:32'hffffffbf]           :/ 20,
                                [32'hffffffc0:32'hffffffff] :/ 1 };

       // If this is a branch and constrain_branches is true, we can ask for up to 100 instructions
       // (independent of insns_since_branch)
       (constrain_branches && (req.trans_type == ICacheCoreTransTypeBranch)) ->
         num_insns <= 100;

       // If this isn't a branch and constrain_branches is true, we can ask for up to 100 -
       // insns_since_branch instructions. This will be positive because of the check above.
       (constrain_branches && (req.trans_type != ICacheCoreTransTypeBranch)) ->
         num_insns <= 100 - insns_since_branch;

       const_enable -> enable == cache_enabled;

       // Toggle the cache enable line one time in 50. This should allow us a reasonable amount of
       // time in each mode (note that each transaction here results in multiple instruction
       // fetches)
       enable dist { cache_enabled :/ gap_between_toggle_enable, ~cache_enabled :/ 1 };

       // If must_invalidate is set, we have to invalidate with this item.
       must_invalidate -> invalidate == 1'b1;

       // If avoid_invalidation is set, we won't touch the invalidate line, unless we have to.
       (avoid_invalidation && !(must_invalidate || (stale_seed && enable))) -> invalidate == 1'b0;

       // Start an invalidation every 1+gap_between_invalidations items.
       invalidate dist { 1'b0 :/ gap_between_invalidations, 1'b1 :/ 1 };

       // If we have seen a new seed since the last invalidation (which must have happened while the
       // cache was disabled) and this item is enabled, force the cache to invalidate.
       stale_seed && enable -> invalidate == 1'b1;
    )

    finish_item(req);
    get_response(rsp);

    // Update whether we think the cache is enabled
    cache_enabled = req.enable;

    // Update the stale_seed flag. It is cleared if we just invalidated and should be set if we
    // didn't invalidate and picked a new seed.
    if (req.invalidate) stale_seed = 0;
    else if (req.new_seed != 0) stale_seed = 1;

    // The next transaction must start with a branch if this one ended with an error
    force_branch = rsp.saw_error;

    // Update insns_since_branch. Note that this will be an overestimate if we saw an error, but
    // that doesn't matter because we'll force a branch next time either way.
    insns_since_branch = (((req.trans_type == ICacheCoreTransTypeBranch) ? 0 : insns_since_branch) +
                          req.num_insns);
  endtask

  // Generate and run num_trans items. Subclasses probably want to configure the parameters above before
  // running this.
  protected task run_reqs();
    req = ibex_icache_core_req_item::type_id::create("req");
    rsp = ibex_icache_core_rsp_item::type_id::create("rsp");

    repeat (num_trans - 1) begin
      run_req(req, rsp);

      // Always clear the must_invalidate flag after an item (it's a 1-shot thing)
      must_invalidate = 1'b0;
    end
  endtask

  // Called from the environment when resetting the DUT. Should ensure that the req_i signal is
  // dropped (to avoid any memory requests making it out of the DUT when it should be in reset)
  //
  // This must not be called while we're in body (otherwise we'd have multiple drivers for req_i).
  task reset_ifs();
    cfg.vif.driver_cb.req <= 1'b0;
  endtask

endclass
