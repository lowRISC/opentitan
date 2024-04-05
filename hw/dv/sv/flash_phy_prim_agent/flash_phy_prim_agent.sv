// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_phy_prim_agent extends dv_base_agent #(
  .CFG_T          (flash_phy_prim_agent_cfg),
  .DRIVER_T       (flash_phy_prim_driver),
  .SEQUENCER_T    (flash_phy_prim_sequencer),
  .MONITOR_T      (flash_phy_prim_monitor),
  .COV_T          (flash_phy_prim_agent_cov)
);

  `uvm_component_utils(flash_phy_prim_agent)
  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // get flash_phy_prim_if handle
    if (!uvm_config_db#(virtual flash_phy_prim_if)::get(this, "", "vif", cfg.vif)) begin
      `uvm_fatal(`gfn, "failed to get flash_phy_prim_if handle from uvm_config_db")
    end
  endfunction

endclass
