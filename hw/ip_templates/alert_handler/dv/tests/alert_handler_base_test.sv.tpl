// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ${module_instance_name}_base_test extends cip_base_test #(
    .ENV_T(${module_instance_name}_env),
    .CFG_T(${module_instance_name}_env_cfg)
  );

  `uvm_component_utils(${module_instance_name}_base_test)
  `uvm_component_new

  // the base class dv_base_test creates the following instances:
  // ${module_instance_name}_env_cfg: cfg
  // ${module_instance_name}_env:     env

  // the base class also looks up UVM_TEST_SEQ plusarg to create and run that seq in
  // the run_phase; as such, nothing more needs to be done

endclass : ${module_instance_name}_base_test
