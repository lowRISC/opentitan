// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

% if is_cip:
class ${name}_base_test extends cip_base_test #(
% else:
class ${name}_base_test extends dv_base_test #(
% endif
    .CFG_T(${name}_env_cfg),
    .ENV_T(${name}_env)
  );

  `uvm_component_utils(${name}_base_test)
  `uvm_component_new

  // the base class dv_base_test creates the following instances:
  // ${name}_env_cfg: cfg
  // ${name}_env:     env

% if not has_ral:
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    cfg.has_ral = 1'b0;
  endfunction

% endif
  // the base class also looks up UVM_TEST_SEQ plusarg to create and run that seq in
  // the run_phase; as such, nothing more needs to be done

endclass : ${name}_base_test
