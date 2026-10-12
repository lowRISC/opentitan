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

  // Apply reset to both the primary and OTP clock domains in parallel so that both clock
  // generators get their reset.
  extern virtual task apply_reset(string kind = "HARD");

  // The base apply_resets_concurrently() only resets cfg.clk_rst_vifs, which excludes
  // otp_clk_rst_vif. Reset it here too so both domains stay in sync during rand-reset stress.
  extern virtual task apply_resets_concurrently(int reset_duration_ps = 0);

  // Resets the DUT and brings the RRAM controller out of reset.
  extern task dut_init(string reset_kind = "HARD");

  // Initializes the RRAM controller. Starts its init sequence that reads the scrambling keys
  // from otp_ctrl. Without this initialization, no software/host access is granted.
  extern task rram_ctrl_init();

endclass : rram_ctrl_base_vseq

function rram_ctrl_base_vseq::new(string name="");
  super.new(name);
endfunction : new

function void rram_ctrl_base_vseq::set_handles();
  super.set_handles();
  `downcast(prim_ral, cfg.ral_models[cfg.prim_ral_name]);
endfunction : set_handles

task rram_ctrl_base_vseq::apply_reset(string kind = "HARD");
  fork
    super.apply_reset(kind);
    cfg.otp_clk_rst_vif.apply_reset();
  join
endtask : apply_reset

task rram_ctrl_base_vseq::apply_resets_concurrently(int reset_duration_ps = 0);
  cfg.otp_clk_rst_vif.drive_rst_pin(0);
  super.apply_resets_concurrently(cfg.otp_clk_rst_vif.clk_period_ps);
  cfg.otp_clk_rst_vif.drive_rst_pin(1);
endtask : apply_resets_concurrently

task rram_ctrl_base_vseq::dut_init(string reset_kind = "HARD");
  // Run super.dut_init() first so rram_ctrl_init() always starts from a DUT that has just
  // settled out of reset.
  super.dut_init(reset_kind);
  rram_ctrl_init();
endtask : dut_init

task rram_ctrl_base_vseq::rram_ctrl_init();
  // poll phy_init_done
  csr_spinwait(.ptr(ral.phy_status.init_done), .exp_data(1'b1));

  // initialize controller
  csr_wr(.ptr(ral.init), .value('b1));

  // poll init_done
  csr_spinwait(.ptr(ral.status.init_done), .exp_data(1'b1));
endtask : rram_ctrl_init
