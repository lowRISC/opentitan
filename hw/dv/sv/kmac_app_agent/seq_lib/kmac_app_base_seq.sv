// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_app_base_seq extends dv_base_seq #(
    .REQ         (kmac_app_item),
    .CFG_T       (kmac_app_agent_cfg),
    .SEQUENCER_T (kmac_app_sequencer)
  );
  `uvm_object_utils(kmac_app_base_seq)

  `uvm_object_new

  virtual task body();
    // FIXME
    `uvm_fatal(`gtn, "Need to override this when you extend from this class!")
  endtask

endclass
