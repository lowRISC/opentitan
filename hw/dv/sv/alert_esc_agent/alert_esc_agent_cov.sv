// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

covergroup alert_handshake_complete_cg with function sample(alert_esc_trans_type_e trans,
                                                            alert_handshake_e      status);
  option.per_instance = 1;

  cp_handshake_complete: coverpoint status {
    bins complete = {AlertAckComplete};
  }
  cp_trans_type: coverpoint trans {
    bins alert_triggered = {AlertEscSigTrans};
  }

  alert_handshake_complete: cross cp_handshake_complete, cp_trans_type;
endgroup : alert_handshake_complete_cg

covergroup esc_handshake_complete_cg with function sample(alert_esc_trans_type_e trans,
                                                          esc_handshake_e        status);
  option.per_instance = 1;

  cp_handshake_complete: coverpoint status {
    bins complete = {EscRespComplete};
  }
  cp_trans_type: coverpoint trans {
    bins esc_triggered = {AlertEscSigTrans};
  }

  esc_handshake_complete: cross cp_handshake_complete, cp_trans_type;
endgroup : esc_handshake_complete_cg

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

  alert_handshake_complete_cg m_alert_handshake_complete_cg;
  esc_handshake_complete_cg   m_esc_handshake_complete_cg;
  alert_esc_trans_cg          m_alert_trans_cg;
  alert_esc_trans_cg          m_esc_trans_cg;
  alert_lpg_cg                m_alert_lpg_cg;

  `uvm_component_utils(alert_esc_agent_cov)
  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (cfg.en_ping_cov) begin
      if (cfg.is_alert) m_alert_trans_cg = new();
      else m_esc_trans_cg = new();
    end
    if (cfg.en_lpg_cov && cfg.is_alert) begin
      m_alert_lpg_cg = new();
    end
    if (cfg.is_alert)    m_alert_handshake_complete_cg = new();
    else                 m_esc_handshake_complete_cg = new();
  endfunction : build_phase

endclass
