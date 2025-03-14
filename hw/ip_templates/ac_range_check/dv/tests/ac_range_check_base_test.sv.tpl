// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ${module_instance_name}_base_test extends cip_base_test #(
    .CFG_T(${module_instance_name}_env_cfg),
    .ENV_T(${module_instance_name}_env)
  );

  `uvm_component_utils(${module_instance_name}_base_test)

  // The base class dv_base_test creates the following instances:
  //   - ${module_instance_name}_env_cfg: cfg
  //   - ${module_instance_name}_env:     env

  // The base class also looks up UVM_TEST_SEQ plusarg to create and run that seq in the run_phase.
  // As such, nothing more needs to be done

  // Standard SV/UVM methods
  extern function new(string name="", uvm_component parent=null);
endclass : ${module_instance_name}_base_test


function ${module_instance_name}_base_test::new(string name="", uvm_component parent=null);
  super.new(name, parent);
endfunction : new
