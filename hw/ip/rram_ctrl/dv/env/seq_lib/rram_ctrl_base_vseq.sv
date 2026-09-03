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

  // Simple model for the OTP key seeds
  virtual task otp_model();
    logic [KeyWidth-1:0] otp_addr_key;
    logic [KeyWidth-1:0] otp_addr_rand_key;
    logic [KeyWidth-1:0] otp_data_key;
    logic [KeyWidth-1:0] otp_data_rand_key;

    `uvm_info(`gfn, "Starting OTP Model ...", UVM_LOW)

    // Create random keys
    otp_addr_key      = {$urandom, $urandom, $urandom, $urandom};
    otp_addr_rand_key = {$urandom, $urandom, $urandom, $urandom};
    otp_data_key      = {$urandom, $urandom, $urandom, $urandom};
    otp_data_rand_key = {$urandom, $urandom, $urandom, $urandom};

    // Initial Values
    cfg.otp_key_vif.otp_key_rsp.addr_ack   = 1'b0;
    cfg.otp_key_vif.otp_key_rsp.data_ack   = 1'b0;
    cfg.otp_key_vif.otp_key_rsp.seed_valid = 1'b0;
    cfg.otp_key_vif.otp_key_rsp.key        = '0;
    cfg.otp_key_vif.otp_key_rsp.rand_key   = '0;

    // Note 'some values' appear in both branches of this fork, this is OK because the
    // branches never run together by design.
    // The order is always 'addr' followed by 'data'.
    fork
      forever begin // addr
        @(posedge cfg.otp_clk_rst_vif.rst_n);
        @(posedge cfg.otp_key_vif.otp_key_req.addr_req);
        `uvm_info(`gfn, $sformatf("OTP Addr Key Applied to DUT : otp_addr_key : %0x",
          otp_addr_key), UVM_MEDIUM)
        `uvm_info(`gfn, $sformatf("OTP Addr Rand Key Applied to DUT : otp_addr_rand_key : %0x",
          otp_addr_rand_key), UVM_MEDIUM)
        cfg.otp_key_vif.otp_key_rsp.key = otp_addr_key;
        cfg.otp_key_vif.otp_key_rsp.rand_key = otp_addr_rand_key;
        cfg.otp_key_vif.otp_key_rsp.seed_valid = 1'b1;
        #1ns; // Positive Hold
        cfg.otp_key_vif.otp_key_rsp.addr_ack = 1'b1;
        @(negedge cfg.otp_key_vif.otp_key_req.addr_req);
        #1ns; // Positive Hold
        cfg.otp_key_vif.otp_key_rsp.addr_ack = 1'b0;
        cfg.otp_key_vif.otp_key_rsp.seed_valid = 1'b0;
      end
      forever begin // data
        @(posedge cfg.otp_clk_rst_vif.rst_n);
        @(posedge cfg.otp_key_vif.otp_key_req.data_req);
        cfg.otp_key_vif.otp_key_rsp.key = otp_data_key;
        cfg.otp_key_vif.otp_key_rsp.rand_key = otp_data_rand_key;
        `uvm_info(`gfn, $sformatf("OTP Data Key Applied to DUT : otp_data_key : %0x",
          otp_data_key), UVM_MEDIUM)
        `uvm_info(`gfn, $sformatf("OTP Data Rand Key Applied to DUT : otp_data_rand_key : %0x",
          otp_data_rand_key), UVM_MEDIUM)
        cfg.otp_key_vif.otp_key_rsp.seed_valid = 1'b1;
        #1ns; // Positive Hold
        cfg.otp_key_vif.otp_key_rsp.data_ack = 1'b1;
        @(negedge cfg.otp_key_vif.otp_key_req.data_req);
        #1ns; // Positive Hold
        cfg.otp_key_vif.otp_key_rsp.data_ack = 1'b0;
        cfg.otp_key_vif.otp_key_rsp.seed_valid = 1'b0;
      end
    join_none
  endtask : otp_model

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

  otp_model();  // Start OTP Model

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
