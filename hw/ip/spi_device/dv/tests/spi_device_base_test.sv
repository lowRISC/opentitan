// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_device_base_test extends cip_base_test #(.ENV_T(spi_device_env),
                                                   .CFG_T(spi_device_env_cfg));
  `uvm_component_utils(spi_device_base_test)
  `uvm_component_new

  virtual function void build_phase(uvm_phase phase);
    max_quit_count  = 50;
    test_timeout_ns = 1500_000_000; // 1.5s
    super.build_phase(phase);
    // configure the spi agent to be in Host mode
    cfg.m_spi_agent_cfg.if_mode = Host;
  endfunction

endclass : spi_device_base_test
