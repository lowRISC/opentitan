// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class hmac_env extends cip_base_env #(.CFG_T               (hmac_env_cfg),
                                      .COV_T               (hmac_env_cov),
                                      .VIRTUAL_SEQUENCER_T (hmac_virtual_sequencer),
                                      .SCOREBOARD_T        (hmac_scoreboard));
  `uvm_component_utils(hmac_env)
  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // get vifs
    if (!uvm_config_db#(d2h_a_ready_vif)::get(this, "", "d2h_a_ready_vif",
        cfg.d2h_a_ready_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get d2h_a_ready_vif from uvm_config_db")
    end
  endfunction

endclass
