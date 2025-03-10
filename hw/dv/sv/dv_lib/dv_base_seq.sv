// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dv_base_seq #(type REQ         = uvm_sequence_item,
                    type RSP         = REQ,
                    type CFG_T       = dv_base_agent_cfg,
                    type SEQUENCER_T = dv_base_sequencer) extends uvm_sequence#(REQ, RSP);
  `uvm_object_param_utils(dv_base_seq #(REQ, RSP, CFG_T, SEQUENCER_T))
  `uvm_declare_p_sequencer(SEQUENCER_T)

  CFG_T cfg;

  `uvm_object_new

  task pre_start();
    super.pre_start();
    cfg = p_sequencer.cfg;
  endtask

  virtual task set_priority_item(int m_priority = -1);
    this.set_priority(m_priority);
  endtask

  task body();
    `uvm_fatal(`gtn, "Need to override this when you extend from this class!")
  endtask : body

endclass
