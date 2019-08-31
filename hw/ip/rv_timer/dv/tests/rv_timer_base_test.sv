// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_timer_base_test extends cip_base_test #(.ENV_T(rv_timer_env), .CFG_T(rv_timer_env_cfg));
  `uvm_component_utils(rv_timer_base_test)
  `uvm_component_new

  virtual function void build_phase(uvm_phase phase);
    test_timeout_ns = 1_000_000_000; // 1s
    super.build_phase(phase);
  endfunction : build_phase

endclass : rv_timer_base_test
