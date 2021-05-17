// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class clkmgr_base_vseq extends cip_base_vseq #(
    .RAL_T               (clkmgr_reg_block),
    .CFG_T               (clkmgr_env_cfg),
    .COV_T               (clkmgr_env_cov),
    .VIRTUAL_SEQUENCER_T (clkmgr_virtual_sequencer)
  );
  `uvm_object_utils(clkmgr_base_vseq)

  rand bit ip_clk_en;
  rand bit [NUM_TRANS-1:0] idle;

  // This selects scanmode according to scanmode_sel, which is randomized with weights.
  rand bit [$bits(lc_ctrl_pkg::lc_tx_t)-1:0] scanmode;
  typedef enum {SC_ON, SC_OFF, SC_OTHER}     scanmode_sel_e;
  rand scanmode_sel_e                        scanmode_sel;
  constraint scanmode_values {
    (scanmode_sel == SC_ON)    -> scanmode == lc_ctrl_pkg::On;
    (scanmode_sel == SC_OFF)   -> scanmode == lc_ctrl_pkg::Off;
    (scanmode_sel == SC_OTHER) -> !(scanmode inside {lc_ctrl_pkg::On, lc_ctrl_pkg::Off});
    scanmode_sel dist {SC_ON := 4, SC_OFF := 2, SC_OTHER := 2};
  }

  // various knobs to enable certain routines
  bit do_clkmgr_init = 1'b1;

  `uvm_object_new

  task pre_start();
    // These are independent: do them in parallel since pre_start consumes time.
    fork
      begin
        cfg.clkmgr_vif.init(.idle('1), .ip_clk_en(ip_clk_en), .scanmode(scanmode));
      end
      if (do_clkmgr_init) clkmgr_init();
      super.pre_start();
    join
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
  endtask

  virtual task dut_shutdown();
    // check for pending clkmgr operations and wait for them to complete
    // TODO
  endtask

  task start_aon_clk();
    // This makes it so the aon clock starts without waiting for its reset,
    // and we won't need to call apply_reset for it.
    #1ps;
    cfg.aon_clk_rst_vif.drive_rst_pin(1'b0);
  endtask

  virtual task apply_reset(string kind = "HARD");
    fork
      super.apply_reset(kind);
      if (kind == "HARD") fork
        cfg.main_clk_rst_vif.apply_reset();
        cfg.io_clk_rst_vif.apply_reset();
        cfg.usb_clk_rst_vif.apply_reset();
        // There is no reset for the aon clock: we just want it to start
        // ASAP, especially given its very low frequency.
        start_aon_clk();
      join
    join
  endtask

  // setup basic clkmgr features
  virtual task clkmgr_init();
    // Initialize input clock frequencies.
    cfg.main_clk_rst_vif.set_freq_mhz(100);
    cfg.io_clk_rst_vif.set_freq_mhz(96);
    cfg.usb_clk_rst_vif.set_freq_mhz(48);
    // The real clock rate for aon is 200kHz, but that can slow testing down.
    // Increasing its frequency improves DV efficiency without compromising quality.
    cfg.aon_clk_rst_vif.set_freq_mhz(7);
  endtask

  function void update_csrs_with_reset_values();
    cfg.clkmgr_vif.update_clk_enables(ral.clk_enables.get_reset());
    cfg.clkmgr_vif.update_clk_hints(ral.clk_hints.get_reset());
    cfg.clkmgr_vif.update_extclk_sel_regwen(ral.extclk_sel_regwen.get_reset());
    cfg.clkmgr_vif.update_extclk_sel(ral.extclk_sel.get_reset());
  endfunction

endclass : clkmgr_base_vseq
