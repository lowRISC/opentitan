// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aon_timer_env extends cip_base_env #(
    .CFG_T              (aon_timer_env_cfg),
    .COV_T              (aon_timer_env_cov),
    .VIRTUAL_SEQUENCER_T(aon_timer_virtual_sequencer),
    .SCOREBOARD_T       (aon_timer_scoreboard)
  );
  `uvm_component_utils(aon_timer_env)

  extern function new (string name="", uvm_component parent=null);
  extern function void build_phase(uvm_phase phase);

endclass : aon_timer_env

function aon_timer_env::new (string name="", uvm_component parent=null);
  super.new(name, parent);
endfunction : new

function void aon_timer_env::build_phase(uvm_phase phase);
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
endfunction : build_phase
