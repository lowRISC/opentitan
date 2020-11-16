// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class keymgr_kmac_base_seq extends dv_base_seq #(
    .REQ         (keymgr_kmac_item),
    .CFG_T       (keymgr_kmac_agent_cfg),
    .SEQUENCER_T (keymgr_kmac_sequencer)
  );
  `uvm_object_utils(keymgr_kmac_base_seq)

  `uvm_object_new

  virtual task body();
    // FIXME
    `uvm_fatal(`gtn, "Need to override this when you extend from this class!")
  endtask

endclass
