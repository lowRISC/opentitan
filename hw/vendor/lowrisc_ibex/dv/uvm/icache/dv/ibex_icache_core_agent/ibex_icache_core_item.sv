// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_core_item extends uvm_sequence_item;

  // The type of transaction
  rand ibex_icache_core_trans_type_e trans_type;

  // The branch address for a branch transaction (only has effect if trans_type is
  // ICacheCoreTransTypeBranch)
  rand bit [31:0]                    branch_addr;

  // Whether the cache enable/disable should be toggled
  rand bit                           toggle_enable;

  // Whether to invalidate the cache
  rand bit                           invalidate;

  // The number of instructions to read (always non-negative, but may be zero)
  rand int                           num_insns;

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

  constraint c_toggle_enable_dist {
    // Toggle the cache enable line one time in 50. This should allow us a reasonable amount of time
    // in each mode (note that each transaction here results in multiple instruction fetches)
    toggle_enable dist { 0 :/ 49, 1 :/ 1 };
  }

  constraint c_invalidate_dist {
    // Poke the cache invalidate line one time in 500. This takes ages and we don't want to
    // accidentally spend most of the test waiting for invalidation.
    invalidate dist { 0 :/ 499, 1 :/ 1 };
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


  `uvm_object_utils_begin(ibex_icache_core_item)
    `uvm_field_enum(ibex_icache_core_trans_type_e, trans_type, UVM_DEFAULT)
    `uvm_field_int (branch_addr,   UVM_DEFAULT | UVM_HEX)
    `uvm_field_int (toggle_enable, UVM_DEFAULT)
    `uvm_field_int (invalidate,    UVM_DEFAULT)
    `uvm_field_int (num_insns,     UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass
