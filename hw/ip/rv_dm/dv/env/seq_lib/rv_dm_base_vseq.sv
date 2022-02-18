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

  // Randomize the initial inputs to the DUT.
  rand lc_ctrl_pkg::lc_tx_t   lc_hw_debug_en;
  rand prim_mubi_pkg::mubi4_t scanmode;
  rand logic [NUM_HARTS-1:0]  unavailable;

  task pre_start();
    // Initialize the input signals with defaults at the start of the sim.
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(lc_hw_debug_en)
    cfg.rv_dm_vif.lc_hw_debug_en <= lc_hw_debug_en;
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(scanmode)
    cfg.rv_dm_vif.scanmode <= scanmode;
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(unavailable)
    cfg.rv_dm_vif.unavailable <= unavailable;
    super.pre_start();
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    // TODO: Randomize the contents of the debug ROM & the program buffer once out of reset.
  endtask

  // Have scan reset also applied at the start.
  virtual task apply_reset(string kind = "HARD");
    fork
      if (kind inside {"HARD", "TRST"}) cfg.m_jtag_agent_cfg.vif.do_trst_n();
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
    // Check for pending rv_dm operations and wait for them to complete.
  endtask

endclass : rv_dm_base_vseq
