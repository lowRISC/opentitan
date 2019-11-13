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
    if (!uvm_config_db#(msg_push_sha_disabled_alert_vif)::get(this, "",
        "msg_push_sha_disabled_alert_vif", cfg.msg_push_sha_disabled_alert_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get msg_push_sha_disabled_alert from uvm_config_db")
    end
  endfunction

endclass
