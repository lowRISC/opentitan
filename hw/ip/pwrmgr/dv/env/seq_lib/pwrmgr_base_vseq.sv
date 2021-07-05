// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwrmgr_base_vseq extends cip_base_vseq #(
  .RAL_T              (pwrmgr_reg_block),
  .CFG_T              (pwrmgr_env_cfg),
  .COV_T              (pwrmgr_env_cov),
  .VIRTUAL_SEQUENCER_T(pwrmgr_virtual_sequencer)
);
  `uvm_object_utils(pwrmgr_base_vseq)

  `uvm_object_new

  import pwrmgr_pkg::PowerDomains;

  localparam int ActiveTimeoutInNanoSeconds = 10_000;
  localparam int PropagationToSlowTimeoutInNanoSeconds = 15_000;

  rand int cycles_before_pwrok;
  rand int cycles_before_clks_ok;
  rand int cycles_between_clks_ok;
  rand int cycles_before_clk_status;
  rand int cycles_before_rst_lc_src;
  rand int cycles_before_rst_sys_src;
  rand int cycles_before_otp_done;
  rand int cycles_before_lc_done;
  rand int cycles_before_wakeup;
  rand int cycles_before_core_clk_en;
  rand int cycles_before_io_clk_en;
  rand int cycles_before_usb_clk_en;
  rand int cycles_before_main_pd_n;

  constraint cycles_before_pwrok_c {cycles_before_pwrok inside {[3 : 10]};}
  constraint cycles_before_clks_ok_c {cycles_before_clks_ok inside {[3 : 10]};}
  constraint cycles_between_clks_ok_c {cycles_between_clks_ok inside {[3 : 10]};}
  constraint cycles_before_clk_status_c {cycles_before_clk_status inside {[0 : 4]};}
  constraint cycles_before_rst_lc_src_base_c {cycles_before_rst_lc_src inside {[0 : 4]};}
  constraint cycles_before_rst_sys_src_base_c {cycles_before_rst_sys_src inside {[0 : 4]};}
  constraint cycles_before_otp_done_base_c {cycles_before_otp_done inside {[0 : 4]};}
  constraint cycles_before_lc_done_base_c {cycles_before_lc_done inside {[0 : 4]};}
  constraint cycles_before_wakeup_c {cycles_before_wakeup inside {[2 : 6]};}
  constraint cycles_before_core_clk_en_c {cycles_before_core_clk_en inside {[2 : 6]};}
  constraint cycles_before_io_clk_en_c {cycles_before_io_clk_en inside {[2 : 6]};}
  constraint cycles_before_usb_clk_en_c {cycles_before_usb_clk_en inside {[2 : 6]};}
  constraint cycles_before_main_pd_n_c {cycles_before_main_pd_n inside {[2 : 6]};}

  bit do_pwrmgr_init = 1'b1;

  task pre_start();
    if (do_pwrmgr_init) pwrmgr_init();
    cfg.slow_clk_rst_vif.wait_for_reset(.wait_negedge(0));
    `uvm_info(`gfn, "Starting responders", UVM_MEDIUM)
    slow_responder();
    fast_responder();
    super.pre_start();
  endtask

  task post_start();
    super.post_start();
    disable slow_responder;
    disable fast_responder;
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    `uvm_info(`gfn, "pwrmgr dut_init", UVM_MEDIUM)
    super.dut_init();
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
        cfg.slow_clk_rst_vif.apply_reset(.pre_reset_dly_clks(0), .reset_width_clks(5));
      end
    join
  endtask

  virtual task apply_resets_concurrently(int reset_duration_ps = 0);
    cfg.slow_clk_rst_vif.drive_rst_pin(0);
    super.apply_resets_concurrently(cfg.slow_clk_rst_vif.clk_period_ps);
    cfg.slow_clk_rst_vif.drive_rst_pin(1);
  endtask

  // setup basic pwrmgr features
  virtual task pwrmgr_init();
    // The fast clock frequency is set by ral.
    // The real slow clock rate is 200kHz, but that slows testing down.
    // Increasing its frequency improves DV efficiency without compromising quality.
    cfg.slow_clk_rst_vif.set_freq_mhz(7);
    `uvm_info(`gfn, $sformatf("slow clock freq=%fMHz, period=%0dns",
                              cfg.slow_clk_rst_vif.clk_freq_mhz,
                              cfg.slow_clk_rst_vif.clk_period_ps),
              UVM_MEDIUM)
  endtask

  // Generates expected responses for the slow fsm.
  // - Completes the clock handshake with the ast: when a clk_en output changes, after a few
  //   cycles the ast is expected to set the corresponding clk_val input to the same value.
  task slow_responder();
    fork
      forever @(edge cfg.pwrmgr_vif.slow_cb.pwr_ast_req.core_clk_en) begin
        cfg.slow_clk_rst_vif.wait_clks(cycles_before_core_clk_en);
        cfg.pwrmgr_vif.slow_cb.pwr_ast_rsp.core_clk_val <=
            cfg.pwrmgr_vif.slow_cb.pwr_ast_req.core_clk_en;
        `uvm_info(`gfn, $sformatf("Driving core_clk_val %b",
                                  cfg.pwrmgr_vif.slow_cb.pwr_ast_req.core_clk_en),
                  UVM_MEDIUM)
      end
      forever @(edge cfg.pwrmgr_vif.slow_cb.pwr_ast_req.io_clk_en) begin
        cfg.slow_clk_rst_vif.wait_clks(cycles_before_io_clk_en);
        cfg.pwrmgr_vif.slow_cb.pwr_ast_rsp.io_clk_val <=
            cfg.pwrmgr_vif.slow_cb.pwr_ast_req.io_clk_en;
        `uvm_info(`gfn, $sformatf("Driving io_clk_val %b",
                                  cfg.pwrmgr_vif.slow_cb.pwr_ast_req.io_clk_en),
                  UVM_MEDIUM)
      end
      forever @(edge cfg.pwrmgr_vif.slow_cb.pwr_ast_req.usb_clk_en) begin
        cfg.slow_clk_rst_vif.wait_clks(cycles_before_usb_clk_en);
        cfg.pwrmgr_vif.slow_cb.pwr_ast_rsp.usb_clk_val <=
            cfg.pwrmgr_vif.slow_cb.pwr_ast_req.usb_clk_en;
        `uvm_info(`gfn, $sformatf("Driving usb_clk_val %b",
                                  cfg.pwrmgr_vif.slow_cb.pwr_ast_req.usb_clk_en),
                  UVM_MEDIUM)
      end
      forever @(negedge cfg.pwrmgr_vif.slow_cb.pwr_ast_req.main_pd_n) begin
        cfg.slow_clk_rst_vif.wait_clks(cycles_before_main_pd_n);
        cfg.pwrmgr_vif.slow_cb.pwr_ast_rsp.main_pok <=
            cfg.pwrmgr_vif.slow_cb.pwr_ast_req.main_pd_n;
        `uvm_info(`gfn, $sformatf("Driving main_pok %b",
                                  cfg.pwrmgr_vif.slow_cb.pwr_ast_req.main_pd_n),
                  UVM_MEDIUM)
      end
    join_none
    `uvm_info(`gfn, "Done with slow_responder", UVM_MEDIUM)
  endtask

  // Generates expected responses for the fast fsm.
  // - Completes the reset handshake with the rstmgr for lc and sys resets: soon after a
  //   reset is requested the corresponding active low reset src must go low.
  // - Completes the handshake with the clkmgr: clk_status needs to track ip_clk_en.
  // - Completes handshake with lc and otp: *_done needs to track *_init.
  task fast_responder();
    fork
      forever @(edge cfg.pwrmgr_vif.fast_cb.pwr_rst_req.rst_lc_req) begin
        cfg.clk_rst_vif.wait_clks(cycles_before_rst_lc_src);
        cfg.pwrmgr_vif.fast_cb.pwr_rst_rsp.rst_lc_src_n <=
            ~cfg.pwrmgr_vif.fast_cb.pwr_rst_req.rst_lc_req;
        `uvm_info(`gfn,
                  $sformatf("Driving rst_lc_src_n %b",
                            ~cfg.pwrmgr_vif.fast_cb.pwr_rst_req.rst_lc_req),
                  UVM_MEDIUM)
      end
      forever @(edge cfg.pwrmgr_vif.fast_cb.pwr_rst_req.rst_sys_req) begin
        cfg.clk_rst_vif.wait_clks(cycles_before_rst_sys_src);
        cfg.pwrmgr_vif.fast_cb.pwr_rst_rsp.rst_sys_src_n <=
            ~cfg.pwrmgr_vif.fast_cb.pwr_rst_req.rst_sys_req;
        `uvm_info(`gfn,
                  $sformatf("Driving rst_sys_src_n %b",
                            ~cfg.pwrmgr_vif.fast_cb.pwr_rst_req.rst_sys_req),
                  UVM_MEDIUM)
      end
      forever @(edge cfg.pwrmgr_vif.fast_cb.pwr_clk_req.ip_clk_en) begin
        cfg.clk_rst_vif.wait_clks(cycles_before_clk_status);
        cfg.pwrmgr_vif.fast_cb.pwr_clk_rsp.clk_status <= cfg.pwrmgr_vif.fast_cb.pwr_clk_req.ip_clk_en;
        `uvm_info(`gfn,
                  $sformatf("Driving clk_status %b",
                            cfg.pwrmgr_vif.fast_cb.pwr_clk_req.ip_clk_en),
                  UVM_MEDIUM)
      end
      forever @(edge cfg.pwrmgr_vif.fast_cb.pwr_lc_req.lc_init) begin
        cfg.clk_rst_vif.wait_clks(cycles_before_lc_done);
        cfg.pwrmgr_vif.fast_cb.pwr_lc_rsp.lc_done <= cfg.pwrmgr_vif.fast_cb.pwr_lc_req.lc_init;
        `uvm_info(`gfn,
                  $sformatf("Driving lc_done %b",
                            cfg.pwrmgr_vif.fast_cb.pwr_lc_req.lc_init),
                  UVM_MEDIUM)
      end
      forever @(edge cfg.pwrmgr_vif.fast_cb.pwr_otp_req.otp_init) begin
        cfg.clk_rst_vif.wait_clks(cycles_before_otp_done);
        cfg.pwrmgr_vif.fast_cb.pwr_otp_rsp.otp_done <= cfg.pwrmgr_vif.fast_cb.pwr_otp_req.otp_init;
        `uvm_info(`gfn,
                  $sformatf("Driving otp_done %b",
                            cfg.pwrmgr_vif.fast_cb.pwr_otp_req.otp_init),
                  UVM_MEDIUM)
      end
    join_none
  endtask

  // This enables main_pok so the slow fsm can get started.
  task start_slow_fsm();
    cfg.slow_clk_rst_vif.wait_clks(cycles_before_pwrok);
    cfg.pwrmgr_vif.update_ast_main_pok(1'b1);
    `uvm_info(`gfn, "out of start_slow_fsm", UVM_MEDIUM)
  endtask

  // This enables the fast fsm to transition to low power after the transition is enabled by
  // software and cpu WFI.
  // FIXME Allow some units not being idle to defeat or postpone transition to low power.
  virtual task fast_to_low_power();
    cfg.pwrmgr_vif.update_otp_idle(1'b1);
    cfg.pwrmgr_vif.update_lc_idle(1'b1);
    cfg.pwrmgr_vif.update_flash_idle(1'b1);
  endtask

  // Waits for the fast fsm becoming active after SW initiated low power, indicated by reading 1
  // from the ctrl_cfg_regwen CSR.
  task wait_for_fast_fsm_active();
    csr_spinwait(.ptr(ral.ctrl_cfg_regwen), .exp_data(1'b1),
                 .timeout_ns(ActiveTimeoutInNanoSeconds));
    `uvm_info(`gfn, "pwrmgr fast fsm active", UVM_MEDIUM)
  endtask

  task wait_for_reset_cause(pwrmgr_pkg::reset_cause_e cause);
    wait(cfg.pwrmgr_vif.pwr_rst_req.reset_cause == cause);
    `uvm_info(`gfn, $sformatf("Observed reset cause_match 0x%x", cause), UVM_MEDIUM)
  endtask

  task wait_for_csr_to_propagate_to_slow_domain();
    csr_wr(.ptr(ral.cfg_cdc_sync), .value(1'b1));
    csr_spinwait(.ptr(ral.cfg_cdc_sync), .exp_data(1'b0),
                 .timeout_ns(PropagationToSlowTimeoutInNanoSeconds));
    `uvm_info(`gfn, "CSR updates made it to the slow domain", UVM_MEDIUM)
  endtask
endclass : pwrmgr_base_vseq
