// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class keymgr_dpe_agent_cfg extends dv_base_agent_cfg;
  `uvm_object_utils(keymgr_dpe_agent_cfg)

  virtual keymgr_dpe_if m_vif;

  // Handle to the agent's sequencer, set via set_sequencer().
  local keymgr_dpe_sequencer m_sqr;

  extern function new(string name="");

  // Called by the agent to set the m_sqr handle.
  extern function void set_sequencer(keymgr_dpe_sequencer sqr);

  // Returns the sequencer handle. Used by keymgr_dpe_base_test to give the sequencer to
  // keymgr_dpe_base_vseq.
  extern function keymgr_dpe_sequencer get_sequencer();
endclass : keymgr_dpe_agent_cfg

function keymgr_dpe_agent_cfg::new(string name="");
  super.new(name);
endfunction

function void keymgr_dpe_agent_cfg::set_sequencer(keymgr_dpe_sequencer sqr);
  m_sqr = sqr;
endfunction

function keymgr_dpe_sequencer keymgr_dpe_agent_cfg::get_sequencer();
  return m_sqr;
endfunction
