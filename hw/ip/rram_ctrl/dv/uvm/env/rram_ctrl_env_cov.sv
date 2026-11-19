// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Covergroups that are dependent on run-time parameters that may be available
 * only in build_phase can be defined here
 * Covergroups may also be wrapped inside helper classes if needed.
 */

class rram_ctrl_env_cov extends cip_base_env_cov #(.CFG_T(rram_ctrl_env_cfg));
  `uvm_component_utils(rram_ctrl_env_cov)

  // Covergroups

  // Standard SV/UVM methods
  extern function new(string name, uvm_component parent);
  extern function void build_phase(uvm_phase phase);
endclass : rram_ctrl_env_cov


function rram_ctrl_env_cov::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction : new

function void rram_ctrl_env_cov::build_phase(uvm_phase phase);
  super.build_phase(phase);
  // Please instantiate sticky_intr_cov array of objects for all interrupts that are sticky
  // See cip_base_env_cov for details
endfunction : build_phase
