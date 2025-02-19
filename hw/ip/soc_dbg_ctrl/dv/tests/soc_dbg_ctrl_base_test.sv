// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class soc_dbg_ctrl_base_test extends cip_base_test #(
    .CFG_T(soc_dbg_ctrl_env_cfg),
    .ENV_T(soc_dbg_ctrl_env)
  );

  `uvm_component_utils(soc_dbg_ctrl_base_test)

  // The base class dv_base_test creates the following instances:
  //   - soc_dbg_ctrl_env_cfg: cfg
  //   - soc_dbg_ctrl_env:     env

  // The base class also looks up UVM_TEST_SEQ plusarg to create and run that seq in the run_phase.
  // As such, nothing more needs to be done

  // Standard SV/UVM methods
  extern function new(string name="", uvm_component parent=null);
endclass : soc_dbg_ctrl_base_test


function soc_dbg_ctrl_base_test::new(string name="", uvm_component parent=null);
  super.new(name, parent);
endfunction : new
