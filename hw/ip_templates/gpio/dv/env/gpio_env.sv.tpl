// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ${module_instance_name}_env extends cip_base_env #(
  .CFG_T              (${module_instance_name}_env_cfg),
  .COV_T              (${module_instance_name}_env_cov),
  .VIRTUAL_SEQUENCER_T(${module_instance_name}_virtual_sequencer),
  .SCOREBOARD_T       (${module_instance_name}_scoreboard)
);
  `uvm_component_utils(${module_instance_name}_env)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(gpio_vif)::get(this, "", "gpio_vif", cfg.gpio_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get gpio_vif from uvm_config_db")
    end
    if (!uvm_config_db#(straps_vif)::get(this, "", "straps_vif", cfg.straps_vif_inst)) begin
      `uvm_fatal(get_full_name(), "Virtual interface straps_vif_inst is not set")
    end
  endfunction

endclass
