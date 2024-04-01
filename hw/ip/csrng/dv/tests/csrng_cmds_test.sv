// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_cmds_test extends csrng_base_test;

  `uvm_component_utils(csrng_cmds_test)
  `uvm_component_new

  function void configure_env();
    super.configure_env();

    cfg.num_cmds_min      = 0;
    cfg.num_cmds_max      = 20;
    cfg.aes_halt_pct      = 80;
    cfg.min_aes_halt_clks = 400;
    cfg.max_aes_halt_clks = 600;
    cfg.force_state_pct   = 100;
    cfg.min_num_disable_enable = 0;
    cfg.max_num_disable_enable = 10;
    cfg.min_enable_clks = 1;
    cfg.max_enable_clks = 10000;
    cfg.min_disable_edn_before_csrng_clks = 10;
    cfg.max_disable_edn_before_csrng_clks = 200;
    cfg.min_disable_csrng_before_entropy_src_clks = 10;
    cfg.max_disable_csrng_before_entropy_src_clks = 200;
    cfg.min_disable_clks = 20;
    cfg.max_disable_clks = 200;
    cfg.min_enable_entropy_src_before_csrng_clks = 10;
    cfg.max_enable_entropy_src_before_csrng_clks = 200;
    cfg.min_enable_csrng_before_edn_clks = 10;
    cfg.max_enable_csrng_before_edn_clks = 200;

    for (int i = 0; i < NUM_HW_APPS; i++) begin
      // CSRNG has a single AES primitive shared among the three application interfaces. To hit the
      // different genbits_depth_cross coverpoints, the maximum delay for asserting genbits_ready
      // and reading the previously requested bits from the genbits FIFO must be chosen
      // sufficiently large. Four times the latency of the AES primitive (16 cycles) seems
      // sufficient. The smallest generate command takes 4 AES encryptions (3x for CTR_DRBG update,
      // 1x for actual generate).
      cfg.m_edn_agent_cfg[i].min_genbits_rdy_dly = 0;
      cfg.m_edn_agent_cfg[i].max_genbits_rdy_dly = 70;
    end

    `DV_CHECK_RANDOMIZE_FATAL(cfg)
    `uvm_info(`gfn, $sformatf("%s", cfg.convert2string()), UVM_LOW)
  endfunction
endclass : csrng_cmds_test
