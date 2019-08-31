// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class gpio_base_test extends cip_base_test #(.ENV_T(gpio_env), .CFG_T(gpio_env_cfg));
  `uvm_component_utils(gpio_base_test)
  `uvm_component_new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction : build_phase

endclass : gpio_base_test
