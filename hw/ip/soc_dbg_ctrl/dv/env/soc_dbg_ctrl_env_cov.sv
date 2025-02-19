// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Covergoups that are dependent on run-time parameters that may be available
 * only in build_phase can be defined here
 * Covergroups may also be wrapped inside helper classes if needed.
 */

class soc_dbg_ctrl_env_cov extends cip_base_env_cov #(.CFG_T(soc_dbg_ctrl_env_cfg));
  `uvm_component_utils(soc_dbg_ctrl_env_cov)

  // The base class provides the following handles for use:
  // soc_dbg_ctrl_env_cfg: cfg

  // Covergroups
  // TODO MVy [add covergroups here]

  // Standard SV/UVM methods
  extern function new(string name, uvm_component parent);
  extern function void build_phase(uvm_phase phase);
endclass : soc_dbg_ctrl_env_cov


function soc_dbg_ctrl_env_cov::new(string name, uvm_component parent);
  super.new(name, parent);
  // TODO MVy [instantiate covergroups here]
endfunction : new

function void soc_dbg_ctrl_env_cov::build_phase(uvm_phase phase);
  super.build_phase(phase);
  // TODO MVy [or instantiate covergroups here]
  // Please instantiate sticky_intr_cov array of objects for all interrupts that are sticky
  // See cip_base_env_cov for details
endfunction : build_phase
