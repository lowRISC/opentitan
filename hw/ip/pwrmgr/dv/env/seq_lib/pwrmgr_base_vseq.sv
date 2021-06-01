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

  localparam int ActiveTimeoutInNanoSeconds = 4_000;
  localparam int PropagationToSlowTimeoutInNanoSeconds = 15_000;

  rand int cycles_before_pwrok;
  rand int cycles_before_clks_ok;
  rand int cycles_between_clks_ok;
  rand int cycles_before_clk_status_on;
  rand int cycles_before_clk_status_off;
  rand int cycles_before_rst_lc_src;
  rand int cycles_before_otp_done;
  rand int cycles_before_lc_done;
  rand int cycles_before_wakeup;
  rand int cycles_before_core_clk_en;
  rand int cycles_before_io_clk_en;
  rand int cycles_before_usb_clk_en;
  rand int cycles_before_main_pd_n;

  constraint cycles_before_pwrok_c { cycles_before_pwrok inside {[3:10]}; }
  constraint cycles_before_clks_ok_c { cycles_before_clks_ok inside {[3:10]}; }
  constraint cycles_between_clks_ok_c { cycles_between_clks_ok inside {[3:10]}; }
  constraint cycles_before_clk_status_on_c { cycles_before_clk_status_on inside {[0:4]}; }
  constraint cycles_before_clk_status_off_c { cycles_before_clk_status_off inside {[0:4]}; }
  constraint cycles_before_rst_lc_src_base_c { cycles_before_rst_lc_src inside {[0:4]}; }
  constraint cycles_before_otp_done_base_c { cycles_before_otp_done inside {[0:4]}; }
  constraint cycles_before_lc_done_base_c { cycles_before_lc_done inside {[0:4]}; }
  constraint cycles_before_wakeup_c { cycles_before_wakeup inside {[2:6]}; }
  constraint cycles_before_core_clk_en_c { cycles_before_core_clk_en inside {[2:6]}; }
  constraint cycles_before_io_clk_en_c { cycles_before_io_clk_en inside {[2:6]}; }
  constraint cycles_before_usb_clk_en_c { cycles_before_usb_clk_en inside {[2:6]}; }
  constraint cycles_before_main_pd_n_c { cycles_before_main_pd_n inside {[2:6]}; }

  // This rstmgr response enables the fast fsm to proceed from a reset.
  task assert_rstmgr_resets();
    staged_update_rst_lc_src('0);
    staged_update_rst_sys_src('0);
  endtask

  task staged_update_rst_lc_src(logic [pwrmgr_pkg::PowerDomains-1:0] value);
    for (int i = 0; i < pwrmgr_pkg::PowerDomains; ++i) begin
      @cfg.clk_rst_vif.cb;
      cfg.pwrmgr_vif.update_rst_lc_src(i, value[i]);
    end
  endtask

  task staged_update_rst_sys_src(logic [pwrmgr_pkg::PowerDomains-1:0] value);
    for (int i = 0; i < pwrmgr_pkg::PowerDomains; ++i) begin
      @cfg.clk_rst_vif.cb;
      cfg.pwrmgr_vif.update_rst_sys_src(i, value[i]);
    end
  endtask

  // This sets input sequence to start the slow fsm till it requests the fast fsm
  // to wake up from low power. If the sequence is not followed the slow fsm just waits
  // so it is not useful to change it. The delays setting the inputs are randomized
  // for good measure.
  task start_slow_fsm();
    cfg.slow_clk_rst_vif.wait_clks(cycles_before_pwrok);
    cfg.pwrmgr_vif.update_ast_main_pok(1'b1);
    cfg.slow_clk_rst_vif.wait_clks(cycles_before_clks_ok);
    cfg.pwrmgr_vif.update_ast_core_clk_val(1'b1);
    cfg.slow_clk_rst_vif.wait_clks(cycles_between_clks_ok);
    cfg.pwrmgr_vif.update_ast_io_clk_val(1'b1);
    cfg.slow_clk_rst_vif.wait_clks(cycles_between_clks_ok);
    cfg.pwrmgr_vif.update_ast_usb_clk_val(1'b1);
  endtask

  task start_fast_from_low_power();
    cfg.clk_rst_vif.wait_clks(cycles_before_clk_status_on);
    cfg.pwrmgr_vif.update_clk_status(1'b1);
    cfg.clk_rst_vif.wait_clks(cycles_before_rst_lc_src);
    staged_update_rst_lc_src('1);
    cfg.clk_rst_vif.wait_clks(cycles_before_otp_done);
    cfg.pwrmgr_vif.update_otp_done(1'b1);
    cfg.clk_rst_vif.wait_clks(cycles_before_lc_done);
    cfg.pwrmgr_vif.update_lc_done(1'b1);
    // Soon after this clr_cfg_lock_o and wkup_o are asserted in fast fsm.
  endtask

  // This sends the fast fsm to low power after the transition is enabled by software
  // and cpu WFI.
  // FIXME Allow some units not being idle to defeat or postpone transition to low power.
  virtual task fast_to_low_power();
    cfg.pwrmgr_vif.update_otp_idle(1'b1);
    cfg.pwrmgr_vif.update_lc_idle(1'b1);
    cfg.pwrmgr_vif.update_flash_idle(1'b1);
    cfg.clk_rst_vif.wait_clks(cycles_before_clk_status_off);
    cfg.pwrmgr_vif.update_clk_status(1'b0);
  endtask

  // Orchestrates the ast turning clocks off as required by the slow fsm going to low power.
  task turn_clocks_off_for_slow_to_low_power();
    fork
      if (!ral.control.core_clk_en.get_mirrored_value()) begin
        wait (!cfg.pwrmgr_vif.pwr_ast_req.core_clk_en);
        cfg.clk_rst_vif.wait_clks(cycles_before_core_clk_en);
        cfg.pwrmgr_vif.update_ast_core_clk_val(1'b0);
      end
      if (!ral.control.io_clk_en.get_mirrored_value()) begin
        wait (!cfg.pwrmgr_vif.pwr_ast_req.io_clk_en);
        cfg.clk_rst_vif.wait_clks(cycles_before_io_clk_en);
        cfg.pwrmgr_vif.update_ast_io_clk_val(1'b0);
      end
      if (!ral.control.usb_clk_en_lp.get_mirrored_value()) begin
        wait (!cfg.pwrmgr_vif.pwr_ast_req.usb_clk_en);
        cfg.clk_rst_vif.wait_clks(cycles_before_usb_clk_en);
        cfg.pwrmgr_vif.update_ast_usb_clk_val(1'b0);
      end
      if (!ral.control.main_pd_n.get_mirrored_value()) begin
        wait (!cfg.pwrmgr_vif.pwr_ast_req.main_pd_n);
        cfg.slow_clk_rst_vif.wait_clks(cycles_before_main_pd_n);
        cfg.pwrmgr_vif.update_ast_main_pok(1'b0);
      end
    join
    `uvm_info(`gfn, "Requested clocks are turned off.", UVM_LOW)
  endtask

  // Waits for the fast fsm becoming active after SW initiated low power, indicated by reading 1
  // from the ctrl_cfg_regwen CSR.
  task wait_for_fast_fsm_active();
    csr_spinwait(.ptr(ral.ctrl_cfg_regwen), .exp_data(1'b1),
                 .timeout_ns(ActiveTimeoutInNanoSeconds));
    `uvm_info(`gfn, "pwrmgr fast fsm active", UVM_MEDIUM)
  endtask

  task wait_for_csr_to_propagate_to_slow_domain();
    csr_wr(.ptr(ral.cfg_cdc_sync), .value(1'b1));
    csr_spinwait(.ptr(ral.cfg_cdc_sync), .exp_data(1'b0),
                 .timeout_ns(PropagationToSlowTimeoutInNanoSeconds));
    `uvm_info(`gfn, "CSR updates made it to the slow domain", UVM_LOW)
  endtask

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
