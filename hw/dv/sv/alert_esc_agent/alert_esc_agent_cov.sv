// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A general covergroup to track completion / alerts in an alert or escalation interface. The status
// input to the sample() function should be an alert_handshake_e or esc_handshake_e enum value, but
// the function takes an int unsigned (the encoding of the enum) to avoid needing to parameterise
// the type.
covergroup handshake_complete_cg (int unsigned complete_status)
  with function sample(alert_esc_trans_type_e trans,
                       int unsigned handshake_status);
  option.per_instance = 1;

  cp_handshake_complete: coverpoint handshake_status {
    bins complete = {complete_status};
  }
  cp_trans_type: coverpoint trans {
    bins alert_triggered = {AlertEscSigTrans};
  }

  alert_handshake_complete: cross cp_handshake_complete, cp_trans_type;
endgroup : handshake_complete_cg

covergroup alert_esc_trans_cg with function sample(alert_esc_trans_type_e trans);
  option.per_instance = 1;

  cp_handshake_complete: coverpoint trans {
    bins alert_esc_trans = {AlertEscSigTrans};
    bins ping_trans      = {AlertEscPingTrans};
  }
endgroup : alert_esc_trans_cg

covergroup alert_lpg_cg with function sample(bit alert_lpg_en);
  option.per_instance = 1;
  cp_alert_lpg: coverpoint alert_lpg_en;
endgroup

// If a module contains alert or escalation ports, these covergroups can check if all
// alerts/escalations/pings have been completed.
class alert_esc_agent_cov extends dv_base_agent_cov #(alert_esc_agent_cfg);

  handshake_complete_cg m_handshake_complete_cg;
  alert_esc_trans_cg    m_alert_trans_cg;
  alert_esc_trans_cg    m_esc_trans_cg;
  alert_lpg_cg          m_alert_lpg_cg;

  `uvm_component_utils(alert_esc_agent_cov)

  extern function new (string name, uvm_component parent);
  extern function void build_phase(uvm_phase phase);

endclass : alert_esc_agent_cov

function alert_esc_agent_cov::new (string name, uvm_component parent);
  super.new(name, parent);
endfunction : new

function void alert_esc_agent_cov::build_phase(uvm_phase phase);
  super.build_phase(phase);
  if (cfg.en_ping_cov) begin
    if (cfg.is_alert) m_alert_trans_cg = new();
    else m_esc_trans_cg = new();
  end
  if (cfg.en_lpg_cov && cfg.is_alert) begin
    m_alert_lpg_cg = new();
  end
  m_handshake_complete_cg = new(cfg.is_alert ? AlertAckComplete : EscRespComplete);
endfunction : build_phase
