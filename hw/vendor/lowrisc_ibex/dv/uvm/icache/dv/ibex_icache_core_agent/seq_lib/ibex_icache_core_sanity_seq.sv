// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Sanity test seq
//
// This is unlikely to find many cache hits (since it branches all over the 4GiB address space).
class ibex_icache_core_sanity_seq extends ibex_icache_core_base_seq;
  `uvm_object_utils(ibex_icache_core_sanity_seq)
  `uvm_object_new

  rand int count;
  constraint c_count { count inside {[800:1000]}; }

  task body();
    // If this is set, the next request will be constrained to have trans_type
    // ICacheCoreTransTypeBranch. It's initially 1 because the core must start with a branch to tell
    // the cache where to fetch from in the first place.
    bit force_branch = 1'b1;

    req = ibex_icache_core_req_item::type_id::create("req");
    rsp = ibex_icache_core_rsp_item::type_id::create("rsp");

    repeat (count - 1) begin
      start_item(req);
      if (force_branch) begin
        `DV_CHECK_RANDOMIZE_WITH_FATAL(req, req.trans_type == ICacheCoreTransTypeBranch;)
      end else begin
        `DV_CHECK_RANDOMIZE_FATAL(req)
      end
      finish_item(req);
      get_response(rsp);

      // The next transaction must start with a branch if this one ended with an error.
      force_branch = rsp.saw_error;
    end
  endtask
endclass
