// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class alert_handler_env extends cip_base_env #(
    .CFG_T              (alert_handler_env_cfg),
    .COV_T              (alert_handler_env_cov),
    .VIRTUAL_SEQUENCER_T(alert_handler_virtual_sequencer),
    .SCOREBOARD_T       (alert_handler_scoreboard)
  );
  `uvm_component_utils(alert_handler_env)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // get vifs
    if (!uvm_config_db#(esc_en_vif)::get(this, "", "esc_en_vif", cfg.esc_en_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get esc_en_vif from uvm_config_db")
    end
    if (!uvm_config_db#(entropy_vif)::get(this, "", "entropy_vif", cfg.entropy_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get entropy_vif from uvm_config_db")
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

endclass
