// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otp_ctrl_env extends cip_base_env #(
    .CFG_T              (otp_ctrl_env_cfg),
    .COV_T              (otp_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T(otp_ctrl_virtual_sequencer),
    .SCOREBOARD_T       (otp_ctrl_scoreboard)
  );
  `uvm_component_utils(otp_ctrl_env)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(pwr_otp_vif)::get(this, "", "pwr_otp_vif", cfg.pwr_otp_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get pwr_otp_vif from uvm_config_db")
    end
    if (!uvm_config_db#(lc_provision_en_vif)::get(this, "", "lc_provision_en_vif",
                                                  cfg.lc_provision_en_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get lc_provision_en_vif from uvm_config_db")
    end
    if (!uvm_config_db#(mem_bkdr_vif)::get(this, "", "mem_bkdr_vif", cfg.mem_bkdr_vif)) begin
      `uvm_fatal(`gfn, "failed to get mem_bkdr_vif from uvm_config_db")
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

endclass
