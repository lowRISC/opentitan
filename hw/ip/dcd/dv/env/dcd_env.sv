// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dcd_env extends cip_base_env #(
    .CFG_T              (dcd_env_cfg),
    .COV_T              (dcd_env_cov),
    .VIRTUAL_SEQUENCER_T(dcd_virtual_sequencer),
    .SCOREBOARD_T       (dcd_scoreboard)
  );
  `uvm_component_utils(dcd_env)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // get the vifs from config db
    if (!uvm_config_db#(virtual clk_rst_if)::get(this, "", "clk_aon_rst_vif",
        cfg.clk_aon_rst_vif)) begin
      `uvm_fatal(`gfn, "failed to get clk_aon_rst_vif from uvm_config_db")
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

endclass
