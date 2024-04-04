// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_virtual_sequencer extends cip_base_virtual_sequencer #(.CFG_T(i2c_env_cfg),
                                                                 .COV_T(i2c_env_cov));
  i2c_sequencer    i2c_sequencer_h;
  uvm_analysis_port #(i2c_item) target_mode_wr_exp_port;
  uvm_analysis_port #(i2c_item) target_mode_rd_exp_port;

  `uvm_component_utils(i2c_virtual_sequencer)
  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    target_mode_wr_exp_port = new("target_mode_wr_exp_port", this);
    target_mode_rd_exp_port = new("target_mode_rd_exp_port", this);
  endfunction
endclass : i2c_virtual_sequencer
