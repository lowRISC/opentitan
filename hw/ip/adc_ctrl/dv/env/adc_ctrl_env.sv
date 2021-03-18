// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class adc_ctrl_env extends cip_base_env #(
    .CFG_T              (adc_ctrl_env_cfg),
    .COV_T              (adc_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T(adc_ctrl_virtual_sequencer),
    .SCOREBOARD_T       (adc_ctrl_scoreboard)
  );
  `uvm_component_utils(adc_ctrl_env)

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
