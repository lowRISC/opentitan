// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rram_ctrl_base_vseq extends cip_base_vseq #(
    .RAL_T               (rram_ctrl_core_reg_block),
    .CFG_T               (rram_ctrl_env_cfg),
    .COV_T               (rram_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T (rram_ctrl_virtual_sequencer)
  );
  `uvm_object_utils(rram_ctrl_base_vseq)

  rram_macro_prim_reg_block prim_ral;

  // Standard SV/UVM methods
  extern function new(string name="");

  // Class specific methods
  extern function void set_handles();

  extern virtual task apply_reset(string kind = "HARD");
  extern virtual task apply_resets_concurrently(int reset_duration_ps = 0);
  extern task pre_start();
  extern task dut_init(string reset_kind = "HARD");
  extern task rram_ctrl_init();

endclass : rram_ctrl_base_vseq

function rram_ctrl_base_vseq::new(string name="");
  super.new(name);
endfunction : new

function void rram_ctrl_base_vseq::set_handles();
  super.set_handles();
  `downcast(prim_ral, cfg.ral_models[cfg.prim_ral_name]);
endfunction : set_handles

// Apply reset to both the primary and OTP clock domains in parallel so that both clock
// generators (which each block on @(negedge rst_n) before starting) get their reset.
task rram_ctrl_base_vseq::apply_reset(string kind = "HARD");
  fork
    super.apply_reset(kind);
    cfg.otp_clk_rst_vif.apply_reset();
  join
endtask : apply_reset

// The base apply_resets_concurrently() only resets cfg.clk_rst_vifs, which excludes
// otp_clk_rst_vif. Reset it here too so both domains stay in sync during rand-reset stress.
task rram_ctrl_base_vseq::apply_resets_concurrently(int reset_duration_ps = 0);
  cfg.otp_clk_rst_vif.drive_rst_pin(0);
  super.apply_resets_concurrently(cfg.otp_clk_rst_vif.clk_period_ps);
  cfg.otp_clk_rst_vif.drive_rst_pin(1);
endtask : apply_resets_concurrently

// setup inputs for DUT
task rram_ctrl_base_vseq::pre_start();
  super.pre_start();
endtask : pre_start

// initializes the DUT
task rram_ctrl_base_vseq::dut_init(string reset_kind = "HARD");
  super.dut_init();
  rram_ctrl_init();
endtask : dut_init

// Brings the RRAM controller out of reset: waits for the phy to finish its own initialization,
// then triggers and waits for the controller's own INIT sequence (lc key derivation etc). Without
// this, ctrl_init_done_i (lcmgr_init_done & lcmgr_keys_valid) never asserts and the arbiter never
// grants software/host access to the block at all.
task rram_ctrl_base_vseq::rram_ctrl_init();
  uvm_reg_data_t reg_data;
  bit init_done;

  // poll phy_init_done
  do begin
    csr_rd(.ptr(ral.phy_status), .value(reg_data));
    init_done = get_field_val(ral.phy_status.init_done, reg_data);
    #1us;
  end while (init_done == 1'b0);

  // initialize controller
  csr_wr(.ptr(ral.init), .value('b1));

  // poll init_done
  do begin
    csr_rd(.ptr(ral.status), .value(reg_data));
    init_done = get_field_val(ral.status.init_done, reg_data);
    #1us;
  end while (init_done == 1'b0);
endtask : rram_ctrl_init
