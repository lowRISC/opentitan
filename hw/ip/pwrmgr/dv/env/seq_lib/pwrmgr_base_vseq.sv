// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwrmgr_base_vseq extends cip_base_vseq #(
    .RAL_T               (pwrmgr_reg_block),
    .CFG_T               (pwrmgr_env_cfg),
    .COV_T               (pwrmgr_env_cov),
    .VIRTUAL_SEQUENCER_T (pwrmgr_virtual_sequencer)
  );
  `uvm_object_utils(pwrmgr_base_vseq)

  // various knobs to enable certain routines
  bit do_pwrmgr_init = 1'b1;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    $display("pwrmgr dut_init");
    super.dut_init();
    if (do_pwrmgr_init) pwrmgr_init();
  endtask

  virtual task dut_shutdown();
    // check for pending pwrmgr operations and wait for them to complete
    // TODO
  endtask

  virtual task apply_reset(string kind = "HARD");
    fork
      super.apply_reset(kind);
      if (kind == "HARD") begin
        // A short slow clock reset should suffice.
        cfg.slow_clk_rst_vif.apply_reset(.pre_reset_dly_clks(0),
                                         .reset_width_clks(5));
      end
    join
  endtask

  // setup basic pwrmgr features
  virtual task pwrmgr_init();
    // The fast clock frequency is set by ral.
    // The real slow clock rate is 200kHz, but that slows testing down.
    // Increasing its frequency improves DV efficiency without compromising quality.
    cfg.slow_clk_rst_vif.set_freq_mhz(7);
  endtask

endclass : pwrmgr_base_vseq
