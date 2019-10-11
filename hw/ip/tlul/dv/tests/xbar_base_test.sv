// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class xbar_base_test extends dv_base_test #(.ENV_T(xbar_env), .CFG_T(xbar_env_cfg));
  `uvm_component_utils(xbar_base_test)
  `uvm_component_new

  virtual function void build_phase(uvm_phase phase);
    max_quit_count  = 50;
    test_timeout_ns = 600_000_000; // 600ms
    super.build_phase(phase);
  endfunction : build_phase

endclass : xbar_base_test
