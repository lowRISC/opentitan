// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class soc_dbg_ctrl_env_cfg extends cip_base_env_cfg #(.RAL_T(soc_dbg_ctrl_core_reg_block));
  `uvm_object_utils(soc_dbg_ctrl_env_cfg)

  // External interfaces
  misc_vif_t misc_vif;

  string jtag_ral_name = "soc_dbg_ctrl_jtag_reg_block";

  // Standard SV/UVM methods
  extern function new(string name="");

  // Class specific methods
  extern virtual function void initialize(bit inherit_ral_models = 1'b0);
endclass : soc_dbg_ctrl_env_cfg


function soc_dbg_ctrl_env_cfg::new(string name="");
  super.new(name);
endfunction : new

function void soc_dbg_ctrl_env_cfg::initialize(bit inherit_ral_models = 1'b0);
  list_of_alerts = soc_dbg_ctrl_env_pkg::LIST_OF_ALERTS;

  // Request a second RAL model for JTAG registers by adding jtag_ral_name to the set of known model
  // names. The associated value has no meaning.
  ral_model_names[jtag_ral_name] = 1'b0;
  clk_freqs_mhz[jtag_ral_name] = clk_freq_mhz;

  super.initialize(inherit_ral_models);
endfunction : initialize
