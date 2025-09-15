// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_ctrl_virtual_sequencer extends cip_base_virtual_sequencer #(
  .CFG_T(flash_ctrl_env_cfg),
  .COV_T(flash_ctrl_env_cov)
);
  `uvm_component_utils(flash_ctrl_virtual_sequencer)

  uvm_analysis_port #(flash_otf_item) eg_exp_ctrl_port[NumBanks];
  uvm_analysis_port #(flash_otf_item) eg_exp_host_port[NumBanks];

  function new(string name, uvm_component parent);
    super.new(name, parent);
    foreach (eg_exp_ctrl_port[i]) begin
      eg_exp_ctrl_port[i] = new($sformatf("eg_exp_ctrl_port[%0d]", i), this);
      eg_exp_host_port[i] = new($sformatf("eg_exp_host_port[%0d]", i), this);
    end
  endfunction // new

endclass
