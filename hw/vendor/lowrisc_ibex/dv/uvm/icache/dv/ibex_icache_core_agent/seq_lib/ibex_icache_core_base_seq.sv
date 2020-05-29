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

  // If this bit is set, we will never enable the cache
  bit force_disable = 1'b0;


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

  virtual task body();
    run_reqs();
  endtask

  // Generate and run a single item using class parameters
  protected task run_req(ibex_icache_core_req_item req, ibex_icache_core_rsp_item rsp);
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

       force_disable -> !toggle_enable;
    )

    finish_item(req);
    get_response(rsp);

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
