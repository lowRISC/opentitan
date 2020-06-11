// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_core_req_item extends uvm_sequence_item;

  // The type of transaction
  rand ibex_icache_core_trans_type_e trans_type;

  // The branch address for a branch transaction (only has effect if trans_type is
  // ICacheCoreTransTypeBranch)
  rand bit [31:0]                    branch_addr;

  // Whether the cache should be enabled
  rand bit                           enable;

  // Whether to invalidate the cache
  rand bit                           invalidate;

  // The number of instructions to read (always non-negative, but may be zero)
  rand int                           num_insns;

  // A possible new memory seed. This has no effect when zero. When nonzero, the driver will pass
  // the seed through a "backdoor" to the memory agent.
  rand bit [31:0]                    new_seed;

  constraint c_non_branch_trans_addr {
    // If the transaction type is ICacheCoreTransTypeBranch then branch_addr can be anything. To
    // make reading debug logs a bit easier, we force it to be zero otherwise.
    (trans_type != ICacheCoreTransTypeBranch) -> branch_addr == 0;

    // Pick trans_type before the other values. We need to do this because constraining branch_addr
    // to 0 for non-branch transactions would otherwise mean branch transactions got weighted 2^32
    // times higher.
    solve trans_type before branch_addr;
  }

  constraint c_branch_addr_alignment {
    // The branch address is always required to be half-word aligned. We don't bother conditioning
    // this on the type of transaction because branch_addr is forced to be zero in anything but a
    // branch transaction.
    !branch_addr[0];
  }

  constraint c_num_insns_dist {
    // For branch transactions, we want to read zero instructions reasonably frequently. For req
    // transactions, much less so. Also, we don't bother with long sequences for req transactions:
    // they won't look any different from the tail end of branch transactions from the cache's point
    // of view.
    if (trans_type == ICacheCoreTransTypeBranch)
      num_insns dist { 0 :/ 5, [1:20] :/ 20, [21:100] :/ 1 };
    else
      num_insns dist { 0 :/ 1, [1:20] :/ 20 };
  }

  constraint c_new_seed_dist {
    // We always want to pick a new seed when we start an invalidation (for maximum test
    // sensitivity). If we aren't starting an invalidation, we mustn't pick a new seed if the cache
    // is enabled (because that could cause multi-way hits). If the cache isn't enabled, pick a new
    // seed sometimes.
    new_seed dist { 0 :/ 1, [1:32'hffffffff] :/ (invalidate ? 1000 : enable ? 0 : 1) };
  }

  `uvm_object_utils_begin(ibex_icache_core_req_item)
    `uvm_field_enum(ibex_icache_core_trans_type_e, trans_type, UVM_DEFAULT)
    `uvm_field_int (branch_addr, UVM_DEFAULT | UVM_HEX)
    `uvm_field_int (enable,      UVM_DEFAULT)
    `uvm_field_int (invalidate,  UVM_DEFAULT)
    `uvm_field_int (num_insns,   UVM_DEFAULT)
    `uvm_field_int (new_seed,    UVM_DEFAULT | UVM_HEX)
  `uvm_object_utils_end

  `uvm_object_new

endclass
