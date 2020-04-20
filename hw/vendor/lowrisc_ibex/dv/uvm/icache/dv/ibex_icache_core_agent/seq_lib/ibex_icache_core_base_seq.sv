// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_core_base_seq extends dv_base_seq #(
    .REQ         (ibex_icache_core_item),
    .CFG_T       (ibex_icache_core_agent_cfg),
    .SEQUENCER_T (ibex_icache_core_sequencer)
  );
  `uvm_object_utils(ibex_icache_core_base_seq)

  `uvm_object_new

  virtual task body();
    `uvm_fatal(`gtn, "Need to override this when you extend from this class!")
  endtask

endclass
