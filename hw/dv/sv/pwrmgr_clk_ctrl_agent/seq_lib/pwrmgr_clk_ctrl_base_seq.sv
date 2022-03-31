// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwrmgr_clk_ctrl_base_seq extends dv_base_seq #(
    .REQ         (pwrmgr_clk_ctrl_item),
    .CFG_T       (pwrmgr_clk_ctrl_agent_cfg),
    .SEQUENCER_T (pwrmgr_clk_ctrl_sequencer)
  );
  `uvm_object_utils(pwrmgr_clk_ctrl_base_seq)

  `uvm_object_new

  virtual task body();
    `uvm_fatal(`gtn, "Need to override this when you extend from this class!")
  endtask

endclass
