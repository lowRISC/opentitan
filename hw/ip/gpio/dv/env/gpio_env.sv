// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class gpio_env extends cip_base_env #(
        .CFG_T               (gpio_env_cfg),
        .COV_T               (gpio_env_cov),
        .VIRTUAL_SEQUENCER_T (gpio_virtual_sequencer),
        .SCOREBOARD_T        (gpio_scoreboard)
    );
  `uvm_component_utils(gpio_env)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(gpio_vif)::get(this, "", "gpio_vif", cfg.gpio_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get gpio_vif from uvm_config_db")
    end
  endfunction

endclass
