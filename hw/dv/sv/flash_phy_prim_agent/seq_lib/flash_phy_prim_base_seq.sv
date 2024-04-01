// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_phy_prim_base_seq extends dv_base_seq #(
    .REQ         (flash_phy_prim_item),
    .CFG_T       (flash_phy_prim_agent_cfg),
    .SEQUENCER_T (flash_phy_prim_sequencer)
  );
  `uvm_object_utils(flash_phy_prim_base_seq)

  `uvm_object_new

  virtual task body();
    `uvm_fatal(`gtn, "Need to override this when you extend from this class!")
  endtask

endclass
