// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_env extends cip_base_env#(
    .CFG_T(entropy_src_env_cfg),
    .COV_T(entropy_src_env_cov),
    .VIRTUAL_SEQUENCER_T(entropy_src_virtual_sequencer),
    .SCOREBOARD_T(entropy_src_scoreboard)
);
  `uvm_component_utils(entropy_src_env)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(virtual pins_if)::get(this, "", "efuse_es_sw_reg_en_vif",
                                              cfg.efuse_es_sw_reg_en_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get efuse_es_sw_reg_en_vif from uvm_config_db")
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

endclass
