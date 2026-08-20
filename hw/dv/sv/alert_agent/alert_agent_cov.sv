// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A general covergroup to track completion / alerts in an alert interface. The status input to the
// sample() function should be an alert_handshake_e enum value, but the function takes an int
// unsigned (the encoding of the enum) to avoid needing to parameterise the type.
covergroup handshake_complete_cg (int unsigned complete_status)
  with function sample(int unsigned handshake_status);
  option.per_instance = 1;

  cp_handshake_complete: coverpoint handshake_status {
    bins complete = {complete_status};
  }
endgroup : handshake_complete_cg

covergroup alert_trans_cg with function sample(alert_trans_type_e trans);
  option.per_instance = 1;

  cp_handshake_complete: coverpoint trans {
    bins alert_trans = {AlertSigTrans};
    bins ping_trans  = {AlertPingTrans};
  }
endgroup : alert_trans_cg

covergroup alert_lpg_cg with function sample(bit alert_lpg_en);
  option.per_instance = 1;
  cp_alert_lpg: coverpoint alert_lpg_en;
endgroup

// If a module contains alert ports, these covergroups can check if all alerts/pings have been
// completed.
class alert_agent_cov extends dv_base_agent_cov #(alert_agent_cfg);

  handshake_complete_cg m_handshake_complete_cg;
  alert_trans_cg        m_alert_trans_cg;
  alert_lpg_cg          m_alert_lpg_cg;

  `uvm_component_utils(alert_agent_cov)

  extern function new (string name, uvm_component parent);
  extern function void build_phase(uvm_phase phase);

endclass : alert_agent_cov

function alert_agent_cov::new (string name, uvm_component parent);
  super.new(name, parent);
endfunction : new

function void alert_agent_cov::build_phase(uvm_phase phase);
  super.build_phase(phase);

  if (cfg.en_ping_cov) m_alert_trans_cg = new();
  if (cfg.en_lpg_cov)  m_alert_lpg_cg = new();

  m_handshake_complete_cg = new(AlertAckComplete);
endfunction : build_phase
