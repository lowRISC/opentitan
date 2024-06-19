// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_base_test extends cip_base_test #(
    .CFG_T(rv_dm_env_cfg),
    .ENV_T(rv_dm_env)
  );

  `uvm_component_utils(rv_dm_base_test)
  `uvm_component_new

  // the base class dv_base_test creates the following instances:
  // rv_dm_env_cfg: cfg
  // rv_dm_env:     env

  // the base class also looks up UVM_TEST_SEQ plusarg to create and run that seq in
  // the run_phase; as such, nothing more needs to be done

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // This timeout number is configured in the test, rather than vseqs (where we have more
    // knowledge of what we're waiting for).
    //
    // Long vseqs include the csr_aliasing test over DMI. We have roughly 50 registers visible over
    // DMI. So this test needs to do 50*50 = 2500 register reads for each time around (and we might
    // go round up to two times). Such a register read takes roughly 50 TCK ticks, giving 125,000
    // TCK ticks in total. With a TCK frequency of 1MHz, comes to 2 * 125ms = 250ms. Round up to
    // 300ms to give a bit of headroom.
    test_timeout_ns = 300_000_000;  // 300ms.
  endfunction : build_phase

endclass : rv_dm_base_test
