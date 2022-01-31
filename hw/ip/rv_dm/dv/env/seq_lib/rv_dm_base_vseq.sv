// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_base_vseq extends cip_base_vseq #(
    .RAL_T               (rv_dm_regs_reg_block),
    .CFG_T               (rv_dm_env_cfg),
    .COV_T               (rv_dm_env_cov),
    .VIRTUAL_SEQUENCER_T (rv_dm_virtual_sequencer)
  );
  `uvm_object_utils(rv_dm_base_vseq)
  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    // Initialize input pins with known values.
    cfg.rv_dm_vif.lc_hw_debug_en = lc_ctrl_pkg::Off;
    cfg.rv_dm_vif.scanmode = prim_mubi_pkg::MuBi4False;
    cfg.rv_dm_vif.unavailable = '{default:0};

    super.dut_init();

    // Randomize the contents of debug ROM once out of reset.
  endtask

  // Have scan reset also applied at the start.
  virtual task apply_reset(string kind = "HARD");
    fork
      if (kind inside {"HARD", "TRST"}) cfg.m_jtag_agent_cfg.do_trst_n();
      if (kind inside {"HARD", "SCAN"}) apply_scan_reset();
      if (kind == "HARD")               super.apply_reset(kind);
    join
  endtask

  // Apply scan reset.
  virtual task apply_scan_reset();
    uint delay;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(delay, delay inside {[0:1000]};) // ns
    #(delay * 1ns);
    cfg.rv_dm_vif.scan_rst_n <= 1'b0;
    // Wait for core clock cycles.
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(delay, delay inside {[2:50]};) // cycles
    cfg.clk_rst_vif.wait_clks(delay);
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(delay, delay inside {[0:1000]};) // ns
    cfg.rv_dm_vif.scan_rst_n <= 1'b1;
  endtask

  virtual task dut_shutdown();
    // check for pending rv_dm operations and wait for them to complete
  endtask

endclass : rv_dm_base_vseq
