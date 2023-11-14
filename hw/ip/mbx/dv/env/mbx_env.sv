// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class mbx_env extends cip_base_env #(
    .CFG_T              (mbx_env_cfg),
    .COV_T              (mbx_env_cov),
    .VIRTUAL_SEQUENCER_T(mbx_virtual_sequencer),
    .SCOREBOARD_T       (mbx_scoreboard)
  );

  `uvm_component_utils(mbx_env)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(intr_vif)::get(this, "", "intr_soc_vif", cfg.intr_soc_vif) &&
        cfg.num_interrupts > 0) begin
      `uvm_fatal(get_full_name(), "failed to get intr_soc_vif from uvm_config_db")
    end
  endfunction: build_phase

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction: connect_phase

endclass: mbx_env
