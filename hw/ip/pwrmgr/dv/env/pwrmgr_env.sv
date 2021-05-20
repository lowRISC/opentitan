// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwrmgr_env extends cip_base_env #(
    .CFG_T              (pwrmgr_env_cfg),
    .COV_T              (pwrmgr_env_cov),
    .VIRTUAL_SEQUENCER_T(pwrmgr_virtual_sequencer),
    .SCOREBOARD_T       (pwrmgr_scoreboard)
  );
  `uvm_component_utils(pwrmgr_env)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual clk_rst_if)::get(
        this, "", "slow_clk_rst_vif", cfg.slow_clk_rst_vif)) begin
      `uvm_fatal(`gfn, "failed to get slow_clk_rst_vif from uvm_config_db")
    end

  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

endclass
