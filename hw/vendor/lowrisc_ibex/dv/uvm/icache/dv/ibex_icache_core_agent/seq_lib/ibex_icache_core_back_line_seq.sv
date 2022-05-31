// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_core_back_line_seq extends ibex_icache_core_base_seq;

  `uvm_object_utils(ibex_icache_core_back_line_seq)
  `uvm_object_new

  bit        req_phase = 0;
  bit [31:0] last_branch;

  protected virtual task run_req(ibex_icache_core_req_item req, ibex_icache_core_rsp_item rsp);
    bit [31:0] min_addr, max_addr;

    start_item(req);

    // The allowed address range depends on the phase. In the first phase, we behave like the normal
    // caching sequence: pick something somewhere near the base address. In the second phase, we go
    // "back a bit" from the previous address.
    if (!req_phase) begin
      min_addr = base_addr;
      max_addr = top_restricted_addr;
    end else begin
      min_addr = last_branch < 16 ? 0 : last_branch - 16;
      max_addr = last_branch;
    end

    `DV_CHECK_RANDOMIZE_WITH_FATAL(
       req,

       // Lots of branches!
       req.trans_type == ICacheCoreTransTypeBranch;

       // Constrain branch targets
       req.branch_addr inside {[min_addr:max_addr]};

       // Ask for at most 5 insns in either phase (in the first phase, this means we have a chance
       // of jumping back when the cache isn't ready yet).
       num_insns <= 5;

       // The cache should always be enabled and never invalidated (unless must_invalidate is true)
       enable == 1'b1;
       invalidate == must_invalidate;
    )

    finish_item(req);
    get_response(rsp);

    last_branch = req.branch_addr;
    req_phase = !req_phase;
  endtask

endclass : ibex_icache_core_back_line_seq
