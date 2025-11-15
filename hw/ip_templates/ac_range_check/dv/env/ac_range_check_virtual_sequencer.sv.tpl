// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ${module_instance_name}_virtual_sequencer extends cip_base_virtual_sequencer #(
    .CFG_T(${module_instance_name}_env_cfg),
    .COV_T(${module_instance_name}_env_cov)
  );
  `uvm_component_utils(${module_instance_name}_virtual_sequencer)

  tl_sequencer tl_unfilt_sqr;
  tl_sequencer tl_filt_sqr;

  // Standard SV/UVM methods
  extern function new(string name, uvm_component parent);
endclass : ${module_instance_name}_virtual_sequencer

function ${module_instance_name}_virtual_sequencer::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction : new
