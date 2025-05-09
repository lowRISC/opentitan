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
  extern function void initialize(bit [31:0] csr_base_addr = '1);
endclass : soc_dbg_ctrl_env_cfg


function soc_dbg_ctrl_env_cfg::new(string name="");
  super.new(name);
endfunction : new

function void soc_dbg_ctrl_env_cfg::initialize(bit [31:0] csr_base_addr = '1);
  list_of_alerts = soc_dbg_ctrl_env_pkg::LIST_OF_ALERTS;

  // Set up second RAL model for JTAG registers
  ral_model_names.push_back(jtag_ral_name);
  clk_freqs_mhz[jtag_ral_name] = clk_freq_mhz;

  super.initialize(csr_base_addr);
endfunction : initialize
