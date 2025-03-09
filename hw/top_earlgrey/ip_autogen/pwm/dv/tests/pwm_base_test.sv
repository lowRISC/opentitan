// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwm_base_test extends cip_base_test #(
  .CFG_T(pwm_env_cfg),
  .ENV_T(pwm_env)
);

  `uvm_component_utils(pwm_base_test)
  `uvm_component_new

  // the base class dv_base_test creates the following instances:
  // pwm_env_cfg: cfg
  // pwm_env:     env

  // the base class also looks up UVM_TEST_SEQ plusarg to create and run that seq in
  // the run_phase; as such, nothing more needs to be done
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction : build_phase

  virtual function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    if (uvm_top.get_report_verbosity_level() > UVM_LOW) begin
      uvm_top.print_topology();
    end
  endfunction // end_of_elaboration

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
  endtask

endclass : pwm_base_test
