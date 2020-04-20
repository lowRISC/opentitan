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
  constraint c_count { count > 0; count < 100; }

  task body();
    // Generate a request which is constrained to have trans_type ICacheCoreTransTypeBranch: the
    // core must start with a branch to tell the cache where to fetch from in the first place.
    req = ibex_icache_core_item::type_id::create("req");
    start_item(req);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(req, req.trans_type == ICacheCoreTransTypeBranch;)
    finish_item(req);

    // Generate and run count ibex_icache_item sequence items (with no other constraint) through the
    // req port.
    repeat (count - 1) begin
      start_item(req);
      `DV_CHECK_RANDOMIZE_FATAL(req)
      finish_item(req);
    end
  endtask
endclass
