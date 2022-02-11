// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aon_timer_base_test extends cip_base_test #(
    .CFG_T(aon_timer_env_cfg),
    .ENV_T(aon_timer_env)
  );

  `uvm_component_utils(aon_timer_base_test)
  `uvm_component_new

  // the base class dv_base_test creates the following instances:
  // aon_timer_env_cfg: cfg
  // aon_timer_env:     env

  // the base class also looks up UVM_TEST_SEQ plusarg to create and run that seq in
  // the run_phase; as such, nothing more needs to be done

  // Add message demotes here
  virtual function void add_message_demotes(dv_report_catcher catcher);
    string msg;

    super.add_message_demotes(catcher);

    // Demote intr_enable register non-existent warnings to infos
    msg = "\s*Unable to locate register 'intr_enable' in block 'aon_timer_reg_block'*";
    catcher.add_change_sev("RegModel", msg, UVM_INFO);

  endfunction

endclass : aon_timer_base_test
