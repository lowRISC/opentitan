// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class lc_ctrl_env extends cip_base_env #(
    .CFG_T              (lc_ctrl_env_cfg),
    .COV_T              (lc_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T(lc_ctrl_virtual_sequencer),
    .SCOREBOARD_T       (lc_ctrl_scoreboard)
  );
  `uvm_component_utils(lc_ctrl_env)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // config power manager pin
    if (!uvm_config_db#(pwr_lc_vif)::get(this, "", "pwr_lc_vif", cfg.pwr_lc_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get pwr_lc_vif from uvm_config_db")
    end
    if (!uvm_config_db#(lc_ctrl_vif)::get(this, "", "lc_ctrl_vif", cfg.lc_ctrl_vif)) begin
      `uvm_fatal(`gfn, "failed to get lc_ctrl_vif from uvm_config_db")
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

endclass
