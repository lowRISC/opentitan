// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aon_timer_env extends cip_base_env #(
    .CFG_T              (aon_timer_env_cfg),
    .COV_T              (aon_timer_env_cov),
    .VIRTUAL_SEQUENCER_T(aon_timer_virtual_sequencer),
    .SCOREBOARD_T       (aon_timer_scoreboard)
  );
  `uvm_component_utils(aon_timer_env)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // get the vifs from config db
    if (!uvm_config_db#(virtual clk_rst_if)::
        get(this, "", "aon_clk_rst_vif", cfg.aon_clk_rst_vif)) begin
      `uvm_fatal(`gfn, "failed to get aon_clk_rst_vif from uvm_config_db")
    end
    if (!uvm_config_db#(virtual pins_if #(1))::
        get(this, "", "lc_escalate_en_vif", cfg.lc_escalate_en_vif)) begin
      `uvm_fatal(`gfn, "failed to get lc_escalate_en_vif from uvm_config_db")
    end
    if (!uvm_config_db#(virtual pins_if #(2))::
        get(this, "", "aon_intr_vif", cfg.aon_intr_vif)) begin
      `uvm_fatal(`gfn, "failed to get aon_intr_vif from uvm_config_db")
    end
    if (!uvm_config_db#(virtual pins_if #(1))::
        get(this, "", "sleep_vif", cfg.sleep_vif)) begin
      `uvm_fatal(`gfn, "failed to get sleep_vif from uvm_config_db")
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

endclass
