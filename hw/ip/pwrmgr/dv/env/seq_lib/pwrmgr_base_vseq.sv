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
  localparam int FetchEnTimeoutNs = 40_000;

  localparam int MaxCyclesBeforeEnable = 6;


  // Random wakeups and resets.
  rand wakeups_t wakeups;
  rand resets_t resets;

  // Random delays.
  rand int cycles_before_pwrok;
  rand int cycles_before_clks_ok;
  rand int cycles_between_clks_ok;
  rand int cycles_before_io_status;
  rand int cycles_before_main_status;
  rand int cycles_before_usb_status;
  rand int cycles_before_rst_lc_src;
  rand int cycles_before_rst_sys_src;
  rand int cycles_before_otp_done;
  rand int cycles_before_lc_done;
  rand int cycles_before_wakeup;
  rand int cycles_before_core_clk_en;
  rand int cycles_before_io_clk_en;
  rand int cycles_before_usb_clk_en;
  rand int cycles_before_main_pok;

  // This tracks the local objection count from these responders. We do not use UVM
  // objections because uvm_objection::wait_for(UVM_ALL_DROPPED, this) seems to wait
  // for all objections to be dropped, not just those raised by this.
  local int objection_count = 0;

  constraint cycles_before_pwrok_c {cycles_before_pwrok inside {[3 : 10]};}
  constraint cycles_before_clks_ok_c {cycles_before_clks_ok inside {[3 : 10]};}
  constraint cycles_between_clks_ok_c {cycles_between_clks_ok inside {[3 : 10]};}
  constraint cycles_before_io_status_c {cycles_before_io_status inside {[0 : 4]};}
  constraint cycles_before_main_status_c {cycles_before_main_status inside {[0 : 4]};}
  constraint cycles_before_usb_status_c {cycles_before_usb_status inside {[0 : 4]};}
  constraint cycles_before_rst_lc_src_base_c {cycles_before_rst_lc_src inside {[0 : 4]};}
  constraint cycles_before_rst_sys_src_base_c {cycles_before_rst_sys_src inside {[0 : 4]};}
  constraint cycles_before_otp_done_base_c {cycles_before_otp_done inside {[0 : 4]};}
  constraint cycles_before_lc_done_base_c {cycles_before_lc_done inside {[0 : 4]};}
  constraint cycles_before_wakeup_c {cycles_before_wakeup inside {[2 : 6]};}
  constraint cycles_before_core_clk_en_c {
    cycles_before_core_clk_en inside {[0 : MaxCyclesBeforeEnable]};
  }
  constraint cycles_before_io_clk_en_c {
    cycles_before_io_clk_en inside {[0 : MaxCyclesBeforeEnable]};
  }
  constraint cycles_before_usb_clk_en_c {
    cycles_before_usb_clk_en inside {[0 : MaxCyclesBeforeEnable]};
  }
  constraint cycles_before_main_pok_c {cycles_before_main_pok inside {[2 : MaxCyclesBeforeEnable]};}

  bit do_pwrmgr_init = 1'b1;
  // This static variable is incremented in each pre_start and decremented in each post_start.
  // It is used to start and stop the responders when the parent sequence starts and ends.
  local static int sequence_depth = 0;

  task pre_start();
    if (do_pwrmgr_init) pwrmgr_init();
    cfg.slow_clk_rst_vif.wait_for_reset(.wait_negedge(0));
    if (sequence_depth == 0) begin
      `uvm_info(`gfn, "Starting responders", UVM_MEDIUM)
      slow_responder();
      fast_responder();
    end
    ++sequence_depth;
    super.pre_start();
  endtask

  task post_apply_reset(string reset_kind = "HARD");
    super.post_apply_reset(reset_kind);
    `uvm_info(`gfn, "waiting for fast active after applying reset", UVM_MEDIUM)
    wait_for_fast_fsm_active();
  endtask

  task post_start();
    super.post_start();
    --sequence_depth;
    if (sequence_depth == 0) begin
      wait(objection_count == 0);
      `uvm_info(`gfn, "all local objections are done", UVM_LOW)
      control_assertions(0);
      `uvm_info(`gfn, "Stopping responders", UVM_MEDIUM)
      disable slow_responder;
      disable fast_responder;
    end
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
    `uvm_info(`gfn, $sformatf(
              "slow clock freq=%fMHz, period=%0dns",
              cfg.slow_clk_rst_vif.clk_freq_mhz,
              cfg.slow_clk_rst_vif.clk_period_ps
              ), UVM_MEDIUM)
    control_assertions(0);
  endtask

  local function void raise_objection();
    ++objection_count;
  endfunction

  local function void drop_objection();
    --objection_count;
  endfunction

  // Generates expected responses for the slow fsm.
  // - Completes the clock handshake with the ast: when a clk_en output changes, after a few
  //   cycles the ast is expected to set the corresponding clk_val input to the same value.
  // - It is possible changes occur in fast succession, so the side-effect is pipelined.
  // Uses macros because VCS flags an error for assignments to automatic variables,
  // even if the variable is a ref to an interface variable.

  `define SLOW_DETECT(rsp_name, req, rsp_sr) \
      forever \
        @req begin \
          raise_objection(); \
          `uvm_info(`gfn, $sformatf("Will drive %0s to %b", rsp_name, req), UVM_MEDIUM) \
        end

  `define SLOW_SHIFT_SR(req, rsp_sr) \
      forever \
        @cfg.slow_clk_rst_vif.cb begin \
          rsp_sr = {rsp_sr[MaxCyclesBeforeEnable-1:0], req}; \
        end

  `define SLOW_ASSIGN(rsp_name, cycles, rsp_sr, rsp) \
      forever \
        @(rsp_sr[cycles]) begin \
          `uvm_info(`gfn, $sformatf( \
                    "Driving %0s to %b after %0d AON cycles.", rsp_name, rsp_sr[cycles], cycles \
                    ), UVM_MEDIUM) \
          rsp <= rsp_sr[cycles]; \
          drop_objection(); \
        end

  task slow_responder();
    logic [MaxCyclesBeforeEnable:0] core_clk_val_sr;
    logic [MaxCyclesBeforeEnable:0] io_clk_val_sr;
    logic [MaxCyclesBeforeEnable:0] usb_clk_val_sr;
    logic [MaxCyclesBeforeEnable:0] main_pd_val_sr;

    fork
      `SLOW_DETECT("core_clk_val", cfg.pwrmgr_vif.slow_cb.pwr_ast_req.core_clk_en, core_clk_val_sr)
      `SLOW_SHIFT_SR(cfg.pwrmgr_vif.slow_cb.pwr_ast_req.core_clk_en, core_clk_val_sr)
      `SLOW_ASSIGN("core_clk_val", cycles_before_core_clk_en, core_clk_val_sr,
                   cfg.pwrmgr_vif.slow_cb.pwr_ast_rsp.core_clk_val)
      `SLOW_DETECT("io_clk_val", cfg.pwrmgr_vif.slow_cb.pwr_ast_req.io_clk_en, io_clk_val_sr)
      `SLOW_SHIFT_SR(cfg.pwrmgr_vif.slow_cb.pwr_ast_req.io_clk_en, io_clk_val_sr)
      `SLOW_ASSIGN("io_clk_val", cycles_before_io_clk_en, io_clk_val_sr,
                   cfg.pwrmgr_vif.slow_cb.pwr_ast_rsp.io_clk_val)
      `SLOW_DETECT("usb_clk_val", cfg.pwrmgr_vif.slow_cb.pwr_ast_req.usb_clk_en, usb_clk_val_sr)
      `SLOW_SHIFT_SR(cfg.pwrmgr_vif.slow_cb.pwr_ast_req.usb_clk_en, usb_clk_val_sr)
      `SLOW_ASSIGN("usb_clk_val", cycles_before_usb_clk_en, usb_clk_val_sr,
                   cfg.pwrmgr_vif.slow_cb.pwr_ast_rsp.usb_clk_val)
      `SLOW_DETECT("main_pok", cfg.pwrmgr_vif.slow_cb.pwr_ast_req.main_pd_n, main_pd_val_sr)
      `SLOW_SHIFT_SR(cfg.pwrmgr_vif.slow_cb.pwr_ast_req.main_pd_n, main_pd_val_sr)
      `SLOW_ASSIGN("main_pok", cycles_before_main_pok, main_pd_val_sr,
                   cfg.pwrmgr_vif.slow_cb.pwr_ast_rsp.main_pok)
    join_none
  endtask
  `undef SLOW_RESPONSE

  // Generates expected responses for the fast fsm.
  // - Completes the reset handshake with the rstmgr for lc and sys resets: soon after a
  //   reset is requested the corresponding active low reset src must go low.
  // - Completes the handshake with the clkmgr for io, main, and usb clocks:
  //   each status input needs to track the corresponding ip_clk_en output.
  // - Completes handshake with lc and otp: *_done needs to track *_init.
  // Macros for the same reason as the slow responder.

  `define FAST_RESPONSE_ACTION(rsp_name, rsp, req, cycles) \
          `uvm_info(`gfn, $sformatf( \
                    "Will drive %0s to %b in %0d fast clock cycles", \
                    rsp_name, req, cycles), UVM_HIGH) \
          cfg.clk_rst_vif.wait_clks(cycles); \
          rsp <= req; \
          `uvm_info(`gfn, $sformatf("Driving %0s to %b", rsp_name, req), UVM_HIGH) \


  task fast_responder();
    fork

      forever
        @cfg.pwrmgr_vif.fast_cb.pwr_rst_req.rst_lc_req begin
          raise_objection();
          `FAST_RESPONSE_ACTION("rst_lc_src_n", cfg.pwrmgr_vif.fast_cb.pwr_rst_rsp.rst_lc_src_n,
                                ~cfg.pwrmgr_vif.fast_cb.pwr_rst_req.rst_lc_req,
                                cycles_before_rst_lc_src)
          // And clear all reset requests when rst_lc_req[1] goes low, because when
          // peripherals are reset they should drop their reset requests.
          if (cfg.pwrmgr_vif.fast_cb.pwr_rst_req.rst_lc_req[1] == 1'b0) begin
            cfg.pwrmgr_vif.update_resets('0);
            `uvm_info(`gfn, "Clearing resets", UVM_MEDIUM)
          end
          drop_objection();
        end
      forever
        @cfg.pwrmgr_vif.fast_cb.pwr_rst_req.rst_sys_req begin
          raise_objection();
          `FAST_RESPONSE_ACTION("rst_sys_src_n", cfg.pwrmgr_vif.fast_cb.pwr_rst_rsp.rst_sys_src_n,
                                ~cfg.pwrmgr_vif.fast_cb.pwr_rst_req.rst_sys_req,
                                cycles_before_rst_sys_src)
          drop_objection();
        end
      forever
        @cfg.pwrmgr_vif.fast_cb.pwr_clk_req.io_ip_clk_en begin
          raise_objection();
          `FAST_RESPONSE_ACTION("io_status", cfg.pwrmgr_vif.fast_cb.pwr_clk_rsp.io_status,
                                cfg.pwrmgr_vif.fast_cb.pwr_clk_req.io_ip_clk_en,
                                cycles_before_io_status)
          drop_objection();
        end
      forever
        @cfg.pwrmgr_vif.fast_cb.pwr_clk_req.main_ip_clk_en begin
          raise_objection();
          `FAST_RESPONSE_ACTION("main_status", cfg.pwrmgr_vif.fast_cb.pwr_clk_rsp.main_status,
                                cfg.pwrmgr_vif.fast_cb.pwr_clk_req.main_ip_clk_en,
                                cycles_before_main_status)
          drop_objection();
        end
      forever
        @cfg.pwrmgr_vif.fast_cb.pwr_clk_req.usb_ip_clk_en begin
          raise_objection();
          `FAST_RESPONSE_ACTION("usb_status", cfg.pwrmgr_vif.fast_cb.pwr_clk_rsp.usb_status,
                                cfg.pwrmgr_vif.fast_cb.pwr_clk_req.usb_ip_clk_en,
                                cycles_before_usb_status)
          drop_objection();
        end
      forever
        @cfg.pwrmgr_vif.fast_cb.pwr_lc_req.lc_init begin
          raise_objection();
          `FAST_RESPONSE_ACTION("lc_done", cfg.pwrmgr_vif.fast_cb.pwr_lc_rsp.lc_done,
                                cfg.pwrmgr_vif.fast_cb.pwr_lc_req.lc_init, cycles_before_lc_done)
          drop_objection();
        end
      forever
        @cfg.pwrmgr_vif.fast_cb.pwr_otp_req.otp_init begin
          raise_objection();
          `FAST_RESPONSE_ACTION("otp_done", cfg.pwrmgr_vif.fast_cb.pwr_otp_rsp.otp_done,
                                cfg.pwrmgr_vif.fast_cb.pwr_otp_req.otp_init, cycles_before_otp_done)
          drop_objection();
        end
    join_none
  endtask
  `undef FAST_RESPONSE_ACTION

  function void control_assertions(bit enable);
    `uvm_info(`gfn, $sformatf("%0sabling assertions", enable ? "En" : "Dis"), UVM_MEDIUM)
    cfg.pwrmgr_ast_sva_vif.disable_sva = !enable;
    cfg.pwrmgr_clock_enables_sva_vif.disable_sva = !enable;
    cfg.pwrmgr_rstmgr_sva_vif.disable_sva = !enable;
  endfunction

  // This enables the fast fsm to transition to low power after the transition is enabled by
  // software and cpu WFI.
  // FIXME Allow some units not being idle to defeat or postpone transition to low power.
  virtual task fast_to_low_power();
    `uvm_info(`gfn, "Setting nvms idle", UVM_MEDIUM)
    cfg.pwrmgr_vif.update_otp_idle(1'b1);
    cfg.pwrmgr_vif.update_lc_idle(1'b1);
    cfg.pwrmgr_vif.update_flash_idle(1'b1);
  endtask

  // Waits for the fast fsm becoming active after SW initiated low power, indicated by the
  // fetch_en output going high.
  task wait_for_fast_fsm_active();
    `uvm_info(`gfn, "starting wait for pwrmgr fast fsm active", UVM_MEDIUM)
    `DV_SPINWAIT(wait (cfg.pwrmgr_vif.fetch_en == lc_ctrl_pkg::On);,
                 "timeout waiting for the CPU to be active", FetchEnTimeoutNs)
    `uvm_info(`gfn, "pwrmgr fast fsm is active", UVM_MEDIUM)
  endtask

  task wait_for_reset_cause(pwrmgr_pkg::reset_cause_e cause);
    wait(cfg.pwrmgr_vif.pwr_rst_req.reset_cause == cause);
    `uvm_info(`gfn, $sformatf("Observed reset cause_match 0x%x", cause), UVM_MEDIUM)
  endtask

  task wait_for_reset_status_clear();
    csr_spinwait(.ptr(ral.reset_status[0]), .exp_data('0), .timeout_ns(ActiveTimeoutInNanoSeconds));
    `uvm_info(`gfn, "pwrmgr reset_status CSR cleared", UVM_MEDIUM)
  endtask

  task wait_for_csr_to_propagate_to_slow_domain();
    csr_wr(.ptr(ral.cfg_cdc_sync), .value(1'b1));
    csr_spinwait(.ptr(ral.cfg_cdc_sync), .exp_data(1'b0),
                 .timeout_ns(PropagationToSlowTimeoutInNanoSeconds));
    `uvm_info(`gfn, "CSR updates made it to the slow domain", UVM_MEDIUM)
  endtask
endclass : pwrmgr_base_vseq
