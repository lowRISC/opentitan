// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ac_range_check_base_test extends cip_base_test #(
    .CFG_T(ac_range_check_env_cfg),
    .ENV_T(ac_range_check_env)
  );

  `uvm_component_utils(ac_range_check_base_test)

  // The base class dv_base_test creates the following instances:
  //   - ac_range_check_env_cfg: cfg
  //   - ac_range_check_env:     env

  // The base class also looks up UVM_TEST_SEQ plusarg to create and run that seq in the run_phase.
  // As such, nothing more needs to be done

  // Standard SV/UVM methods
  extern function new(string name="", uvm_component parent=null);
  extern function void build_phase(uvm_phase phase);
endclass : ac_range_check_base_test


function ac_range_check_base_test::new(string name="", uvm_component parent=null);
  super.new(name, parent);
endfunction : new

function void ac_range_check_base_test::build_phase(uvm_phase phase);
  string test_seq_s;

  super.build_phase(phase);

  // Disable some scoreboard checks for the CSR tests (unfortunately we cannot simply avoid the
  // scoreboard to be created by setting this config flag, which should be the case)
  void'($value$plusargs("UVM_TEST_SEQ=%0s", test_seq_s));
  $display("test_seq_s = %s", test_seq_s);
  if (test_seq_s == "ac_range_check_common_vseq") begin
    cfg.en_scb = 0;
  end
endfunction : build_phase
