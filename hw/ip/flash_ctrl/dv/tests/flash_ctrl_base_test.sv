// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_ctrl_base_test extends cip_base_test #(
    .CFG_T(flash_ctrl_env_cfg),
    .ENV_T(flash_ctrl_env)
  );

  `uvm_component_utils(flash_ctrl_base_test)
  `uvm_component_new

  virtual function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    if (uvm_top.get_report_verbosity_level() > UVM_LOW) begin
      uvm_top.print_topology();
    end
   endfunction // end_of_elaboration

  // the base class dv_base_test creates the following instances:
  // flash_ctrl_env_cfg: cfg
  // flash_ctrl_env:     env

  // the base class also looks up UVM_TEST_SEQ plusarg to create and run that seq in
  // the run_phase; as such, nothing more needs to be done

endclass : flash_ctrl_base_test
