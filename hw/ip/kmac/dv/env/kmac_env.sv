// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_env extends cip_base_env #(
    .CFG_T              (kmac_env_cfg),
    .COV_T              (kmac_env_cov),
    .VIRTUAL_SEQUENCER_T(kmac_virtual_sequencer),
    .SCOREBOARD_T       (kmac_scoreboard)
  );
  `uvm_component_utils(kmac_env)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // get ext interfaces
    if (!uvm_config_db#(idle_vif)::get(this, "", "idle_vif", cfg.idle_vif)) begin
      `uvm_fatal(`gfn, "failed to get idle_vif handle from uvm_config_db")
    end
    if (!uvm_config_db#(sideload_vif)::get(this, "", "sideload_vif", cfg.sideload_vif)) begin
      `uvm_fatal(`gfn, "failed to get sideload_vif handle from uvm_config_db")
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

endclass
