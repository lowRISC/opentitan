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

  // If this is set, any branch target address should be within 64 bytes of base_addr and runs of
  // instructions should have a maximum length of 100.
  bit constrain_branches = 1'b0;

  // Should the cache be enabled for the first fetch? Probably only interesting if you also set
  // const_enable.
  bit initial_enable = 1'b0;

  // If this bit is set, we will never change whether the cache is enabled from the initial_enable
  // setting.
  bit const_enable = 1'b0;

  // If this bit is set, we will never invalidate the cache (useful for hit ratio tracking)
  bit no_invalidate = 1'b0;

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
  protected rand int count;
  constraint c_count { count inside {[800:1000]}; }

  // The base address used when constrain_branches is true.
  protected rand bit[31:0] base_addr;

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
         req.branch_addr inside {[base_addr:(base_addr + 64)]};

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

       // If no_invalidate is set, we shouldn't ever touch the invalidate line.
       no_invalidate -> invalidate == 1'b0;

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

  // Generate and run count items. Subclasses probably want to configure the parameters above before
  // running this.
  protected task run_reqs();
    req = ibex_icache_core_req_item::type_id::create("req");
    rsp = ibex_icache_core_rsp_item::type_id::create("rsp");

    repeat (count - 1) begin
      run_req(req, rsp);
    end
  endtask

endclass
