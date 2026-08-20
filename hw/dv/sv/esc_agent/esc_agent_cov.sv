// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A general covergroup to track completion / alerts in an escalation interface. The status input to
// the sample() function should be an esc_handshake_e enum value, but the function takes an int
// unsigned (the encoding of the enum) to avoid needing to parameterise the type.
covergroup handshake_complete_cg (int unsigned complete_status)
  with function sample(int unsigned handshake_status);
  option.per_instance = 1;

  cp_handshake_complete: coverpoint handshake_status {
    bins complete = {complete_status};
  }
endgroup

covergroup esc_trans_cg with function sample(esc_trans_type_e trans);
  option.per_instance = 1;

  cp_handshake_complete: coverpoint trans {
    bins esc_trans  = {EscSigTrans};
    bins ping_trans = {EscPingTrans};
  }
endgroup

// If a module contains alert or escalation ports, these covergroups can check if all
// escalations/pings have been completed.
class esc_agent_cov extends dv_base_agent_cov #(esc_agent_cfg);
  `uvm_component_utils(esc_agent_cov)

  handshake_complete_cg m_handshake_complete_cg;
  esc_trans_cg          m_esc_trans_cg;

  extern function new (string name, uvm_component parent);
  extern function void build_phase(uvm_phase phase);
endclass : esc_agent_cov

function esc_agent_cov::new (string name, uvm_component parent);
  super.new(name, parent);
endfunction : new

function void esc_agent_cov::build_phase(uvm_phase phase);
  super.build_phase(phase);
  if (cfg.en_ping_cov) begin
    m_esc_trans_cg = new();
  end
  m_handshake_complete_cg = new(EscRespComplete);
endfunction : build_phase
