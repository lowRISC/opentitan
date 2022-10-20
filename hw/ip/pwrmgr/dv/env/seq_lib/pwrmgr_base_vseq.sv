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

  localparam int ActiveTimeoutInNanoSeconds = 10_000;
  localparam int PropagationToSlowTimeoutInNanoSeconds = 15_000;
  localparam int FetchEnTimeoutNs = 40_000;

  localparam int MaxCyclesBeforeEnable = 12;

  // Random wakeups and resets.
  rand wakeups_t wakeups;
  rand wakeups_t wakeups_en;
  rand resets_t  resets;
  rand resets_t  resets_en;
  rand bit       power_glitch_reset;
  rand bit       escalation_reset;

  rand bit       en_intr;

  constraint resets_en_c {
    solve resets, power_glitch_reset, escalation_reset before resets_en;
    |{resets_en & resets, power_glitch_reset, escalation_reset} == 1'b1;
  }

  rand bit               disable_wakeup_capture;

  // Random control enables.
  rand control_enables_t control_enables;

  // Random delays.
  rand int               cycles_before_pwrok;
  rand int               cycles_before_clks_ok;
  rand int               cycles_between_clks_ok;
  rand int               cycles_before_io_status;
  rand int               cycles_before_main_status;
  rand int               cycles_before_usb_status;
  rand int               cycles_before_rst_lc_src;
  rand int               cycles_before_rst_sys_src;
  rand int               cycles_before_otp_done;
  rand int               cycles_before_lc_done;
  rand int               cycles_before_wakeup;
  rand int               cycles_before_reset;
  rand int               cycles_before_core_clk_en;
  rand int               cycles_before_io_clk_en;
  rand int               cycles_before_usb_clk_en;
  rand int               cycles_before_main_pok;

  // This tracks the local objection count from these responders. We do not use UVM
  // objections because uvm_objection::wait_for(UVM_ALL_DROPPED, this) seems to wait
  // for all objections to be dropped, not just those raised by this.
  local int              objection_count            = 0;

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
  constraint cycles_before_reset_c {cycles_before_reset inside {[2 : 6]};}
  constraint cycles_before_core_clk_en_c {
    cycles_before_core_clk_en inside {[0 : MaxCyclesBeforeEnable]};
  }
  constraint cycles_before_io_clk_en_c {
    cycles_before_io_clk_en inside {[0 : MaxCyclesBeforeEnable - 3]};
  }
  constraint cycles_before_usb_clk_en_c {
    cycles_before_usb_clk_en inside {[0 : MaxCyclesBeforeEnable]};
  }
  constraint cycles_before_main_pok_c {cycles_before_main_pok inside {[2 : MaxCyclesBeforeEnable]};}

  // This is used to trigger a software reset, as per rstmgr's `reset_req` CSR.
  prim_mubi_pkg::mubi4_t sw_rst_from_rstmgr = prim_mubi_pkg::MuBi4False;

  bit do_pwrmgr_init = 1'b1;
  // This static variable is incremented in each pre_start and decremented in each post_start.
  // It is used to start and stop the responders when the parent sequence starts and ends.
  local static int sequence_depth = 0;
  pwrmgr_mubi_e mubi_mode;

  // This stops randomizing cycles counts that select from a pipeline, since
  // changes can lead to missing or unexpected transitions.
  task stop_randomizing_cycles();
    cycles_before_core_clk_en.rand_mode(0);
    cycles_before_io_clk_en.rand_mode(0);
    cycles_before_usb_clk_en.rand_mode(0);
    cycles_before_main_pok.rand_mode(0);
  endtask

  // Disable exclusions for CONTROL.USB_CLK_EN_ACTIVE and RESET_EN: they are meant for full-chip only.
  function void disable_unnecessary_exclusions();
    csr_excl_item csr_excl = ral.get_excl_item();
    `uvm_info(`gfn, "Dealing with exclusions", UVM_MEDIUM)
    csr_excl.enable_excl(.obj("pwrmgr_reg_block.control"), .enable(1'b0));
    csr_excl.enable_excl(.obj("pwrmgr_reg_block.reset_en"), .enable(1'b0));
    csr_excl.print_exclusions(UVM_MEDIUM);
  endfunction

  virtual task pre_start();
    cfg.pwrmgr_vif.lc_hw_debug_en = lc_ctrl_pkg::Off;
    cfg.pwrmgr_vif.lc_dft_en = lc_ctrl_pkg::Off;
    mubi_mode = PwrmgrMubiNone;
    `DV_GET_ENUM_PLUSARG(pwrmgr_mubi_e, mubi_mode, pwrmgr_mubi_mode)
    `uvm_info(`gfn, $sformatf("pwrmgr mubi mode : %s", mubi_mode.name()), UVM_MEDIUM)

    if (do_pwrmgr_init) pwrmgr_init();
    disable_unnecessary_exclusions();
    cfg.slow_clk_rst_vif.wait_for_reset(.wait_negedge(0));
    stop_randomizing_cycles();
    fork
      // Toggle rst_main_n to make sure the slow fsm resets correctly, and wait some cycles
      // so testing doesn't start until the side-effects are cleared.
      begin
        cfg.pwrmgr_vif.glitch_power_reset();
        cfg.slow_clk_rst_vif.wait_clks(7);
      end
      begin
        if (sequence_depth == 0) begin
          `uvm_info(`gfn, "Starting responders", UVM_MEDIUM)
          slow_responder();
          fast_responder();
        end
        ++sequence_depth;
        super.pre_start();
      end
    join
  endtask : pre_start

  task post_apply_reset(string reset_kind = "HARD");
    super.post_apply_reset(reset_kind);
    if (reset_kind == "HARD") begin
      // Undo any pending resets.
      cfg.pwrmgr_vif.rst_main_n = 1'b1;
      cfg.pwrmgr_vif.update_resets(0);
    end

    `uvm_info(`gfn, "waiting for fast active after applying reset", UVM_MEDIUM)

    // There is tb lock up case
    // when reset come while rom_ctrl = {false, false}.
    // So we need rom_ctrl driver runs in parallel with
    // wait_for_fast_fsm_active
    fork
      wait_for_fast_fsm_active();
      init_rom_response();
    join
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
      cfg.esc_clk_rst_vif.apply_reset();
      cfg.lc_clk_rst_vif.apply_reset();
      // Escalation resets are cleared when reset goes active.
      clear_escalation_reset();
      cfg.aon_clk_rst_vif.apply_reset();
    join
  endtask

  virtual task apply_resets_concurrently(int reset_duration_ps = 0);
    cfg.slow_clk_rst_vif.drive_rst_pin(0);
    cfg.esc_clk_rst_vif.drive_rst_pin(0);
    cfg.lc_clk_rst_vif.drive_rst_pin(0);
    cfg.aon_clk_rst_vif.drive_rst_pin(0);
    super.apply_resets_concurrently(cfg.slow_clk_rst_vif.clk_period_ps);
    cfg.aon_clk_rst_vif.drive_rst_pin(1);
    cfg.esc_clk_rst_vif.drive_rst_pin(1);
    cfg.lc_clk_rst_vif.drive_rst_pin(1);
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
    cfg.esc_clk_rst_vif.set_freq_mhz(cfg.clk_rst_vif.clk_freq_mhz);
    cfg.lc_clk_rst_vif.set_freq_mhz(cfg.clk_rst_vif.clk_freq_mhz);
    cfg.aon_clk_rst_vif.set_freq_mhz(cfg.clk_rst_vif.clk_freq_mhz);
    set_ndmreset_req('0);
    control_assertions(0);
  endtask

  virtual task setup_interrupt(bit enable);
    csr_wr(.ptr(ral.intr_enable.wakeup), .value(enable));
    `uvm_info(`gfn, $sformatf("Wakeup interrupt is %0sabled", enable ? "en" : "dis"), UVM_MEDIUM)
  endtask

  // May check intr_state.wakeup CSR against expected, and regardless, it checks that the
  // interrupt output matches intr_state && intr_enable. The first check is disabled if
  // check_expected is off, which is used when a reset and an interrupt come in close
  // temporal proximity.
  virtual task check_and_clear_interrupt(bit expected, bit check_expected = 1'b1);
    bit enable;
    `uvm_info(`gfn, "Checking and clearing interrupt", UVM_MEDIUM)
    if (check_expected) begin
      csr_rd_check(.ptr(ral.intr_state.wakeup), .compare_value(expected),
                   .err_msg("interrupt mismatch"));
    end else begin
      csr_rd(.ptr(ral.intr_state.wakeup), .value(expected));
    end
    csr_rd(.ptr(ral.intr_enable.wakeup), .value(enable));
    `DV_CHECK_EQ(cfg.pwrmgr_vif.intr_wakeup, expected && enable)
    csr_wr(.ptr(ral.intr_state.wakeup), .value(1'b1));
  endtask

  local function void raise_objection(string label);
    ++objection_count;
    `uvm_info(`gfn, $sformatf("Raising objection to %0d for %0s", objection_count, label), UVM_HIGH)
  endfunction

  local function void drop_objection(string label);
    --objection_count;
    `uvm_info(`gfn, $sformatf("Dropping objection to %0d for %0s", objection_count, label),
              UVM_HIGH)
  endfunction

  virtual function void set_ndmreset_req(logic value);
    cfg.pwrmgr_vif.cpu_i.ndmreset_req = value;
  endfunction

  // Generates expected responses for the slow fsm.
  // - Completes the clock handshake with the ast: when a clk_en output changes, after a few
  //   cycles the ast is expected to set the corresponding clk_val input to the same value.
  // - It is possible changes occur in fast succession, so the side-effect is pipelined.
  // Uses macros because VCS flags an error for assignments to automatic variables,
  // even if the variable is a ref to an interface variable.

  `define SLOW_DETECT(rsp_name_, req_) \
      forever \
        @req_ begin \
          raise_objection(rsp_name_); \
          `uvm_info(`gfn, $sformatf( \
                    "slow_responder: Will drive %0s to %b", rsp_name_, req_), UVM_MEDIUM) \
        end

  `define SLOW_SHIFT_SR(req_, rsp_sr_) \
      forever \
        @cfg.slow_clk_rst_vif.cb begin \
          rsp_sr_ = {rsp_sr_[MaxCyclesBeforeEnable-1:0], req_}; \
        end

  `define SLOW_ASSIGN(rsp_name_, cycles_, rsp_sr_, rsp_) \
      forever \
        @(rsp_sr_[cycles_]) begin \
          `uvm_info(`gfn, $sformatf( \
                    "slow_responder: Driving %0s to %b after %0d AON cycles.", \
                    rsp_name_, \
                    rsp_sr_[cycles_], \
                    cycles_ \
                    ), UVM_MEDIUM) \
          rsp_ <= rsp_sr_[cycles_]; \
          drop_objection(rsp_name_); \
        end

  task slow_responder();
    logic [MaxCyclesBeforeEnable:0] core_clk_val_sr;
    logic [MaxCyclesBeforeEnable:0] io_clk_val_sr;
    logic [MaxCyclesBeforeEnable:0] usb_clk_val_sr;
    logic [MaxCyclesBeforeEnable:0] main_pd_val_sr;
    fork
      `SLOW_DETECT("core_clk_val", cfg.pwrmgr_vif.slow_cb.pwr_ast_req.core_clk_en)
      `SLOW_SHIFT_SR(cfg.pwrmgr_vif.slow_cb.pwr_ast_req.core_clk_en, core_clk_val_sr)
      `SLOW_ASSIGN("core_clk_val", cycles_before_core_clk_en, core_clk_val_sr,
                   cfg.pwrmgr_vif.slow_cb.pwr_ast_rsp.core_clk_val)

      `SLOW_DETECT("io_clk_val", cfg.pwrmgr_vif.slow_cb.pwr_ast_req.io_clk_en)
      `SLOW_SHIFT_SR(cfg.pwrmgr_vif.slow_cb.pwr_ast_req.io_clk_en, io_clk_val_sr)
      forever
        @(io_clk_val_sr[cycles_before_io_clk_en]) begin
          logic new_value = io_clk_val_sr[cycles_before_io_clk_en];
          `uvm_info(`gfn, $sformatf(
                    "slow_responder: Driving %0s to %b after %0d AON cycles.",
                    "io_clk_val",
                    new_value,
                    cycles_before_io_clk_en
                    ), UVM_MEDIUM)
          if (new_value == 1) cfg.clk_rst_vif.start_clk();
          else cfg.clk_rst_vif.stop_clk();
          repeat (2) @cfg.slow_clk_rst_vif.cb;
          cfg.pwrmgr_vif.slow_cb.pwr_ast_rsp.io_clk_val <= new_value;
          drop_objection("io_clk_val");
        end

      `SLOW_DETECT("usb_clk_val", cfg.pwrmgr_vif.slow_cb.pwr_ast_req.usb_clk_en)
      `SLOW_SHIFT_SR(cfg.pwrmgr_vif.slow_cb.pwr_ast_req.usb_clk_en, usb_clk_val_sr)
      `SLOW_ASSIGN("usb_clk_val", cycles_before_usb_clk_en, usb_clk_val_sr,
                   cfg.pwrmgr_vif.slow_cb.pwr_ast_rsp.usb_clk_val)

      `SLOW_DETECT("main_pok", cfg.pwrmgr_vif.slow_cb.pwr_ast_req.main_pd_n)
      `SLOW_SHIFT_SR(cfg.pwrmgr_vif.slow_cb.pwr_ast_req.main_pd_n, main_pd_val_sr)
      `SLOW_ASSIGN("main_pok", cycles_before_main_pok, main_pd_val_sr,
                   cfg.pwrmgr_vif.slow_cb.pwr_ast_rsp.main_pok)
    join_none
  endtask : slow_responder
  `undef SLOW_DETECT
  `undef SLOW_SHIFT_SR
  `undef SLOW_ASSIGN

  // Generates expected responses for the fast fsm.
  // - Completes the reset handshake with the rstmgr for lc and sys resets: soon after a
  //   reset is requested the corresponding active low reset src must go low.
  // - Completes the handshake with the clkmgr for io, main, and usb clocks:
  //   each status input needs to track the corresponding ip_clk_en output.
  // - Completes handshake with lc and otp: *_done needs to track *_init.
  // Macros for the same reason as the slow responder.

  `define FAST_RESPONSE_ACTION(rsp_name, rsp, req, cycles) \
          `uvm_info(`gfn, $sformatf( \
                    "fast_responder: Will drive %0s to %b in %0d fast clock cycles", \
                    rsp_name, req, cycles), UVM_HIGH) \
          cfg.clk_rst_vif.wait_clks(cycles); \
          rsp <= req; \
          `uvm_info(`gfn, $sformatf("fast_responder: Driving %0s to %b", rsp_name, req), UVM_HIGH) \


  task fast_responder();
    fork
      forever
        @cfg.pwrmgr_vif.fast_cb.pwr_rst_req.rst_lc_req begin
          raise_objection("rst_lc_src_n");
          `FAST_RESPONSE_ACTION("rst_lc_src_n", cfg.pwrmgr_vif.fast_cb.pwr_rst_rsp.rst_lc_src_n,
                                ~cfg.pwrmgr_vif.fast_cb.pwr_rst_req.rst_lc_req,
                                cycles_before_rst_lc_src)
          // And clear all reset requests when rst_lc_req[1] goes low, because when
          // peripherals are reset they should drop their reset requests.
          if (cfg.pwrmgr_vif.fast_cb.pwr_rst_req.rst_lc_req[1] == 1'b0) begin
            cfg.esc_clk_rst_vif.drive_rst_pin(1);
            cfg.lc_clk_rst_vif.drive_rst_pin(1);
            repeat (2) cfg.esc_clk_rst_vif.wait_clks(2);
            cfg.pwrmgr_vif.update_resets('0);
            cfg.pwrmgr_vif.update_sw_rst_req(prim_mubi_pkg::MuBi4False);
            `uvm_info(`gfn, "Clearing resets", UVM_MEDIUM)
          end else begin
            cfg.esc_clk_rst_vif.drive_rst_pin(0);
            cfg.lc_clk_rst_vif.drive_rst_pin(0);
            clear_escalation_reset();
          end
          drop_objection("rst_lc_src_n");
        end
      forever
        @cfg.pwrmgr_vif.fast_cb.pwr_rst_req.rst_sys_req begin
          raise_objection("rst_sys_src_n");
          `FAST_RESPONSE_ACTION("rst_sys_src_n", cfg.pwrmgr_vif.fast_cb.pwr_rst_rsp.rst_sys_src_n,
                                ~cfg.pwrmgr_vif.fast_cb.pwr_rst_req.rst_sys_req,
                                cycles_before_rst_sys_src)
          drop_objection("rst_sys_src_n");
        end

      forever
        @cfg.pwrmgr_vif.fast_cb.pwr_clk_req.io_ip_clk_en begin
          logic new_value = cfg.pwrmgr_vif.fast_cb.pwr_clk_req.io_ip_clk_en;
          raise_objection("io_status");
          `uvm_info(`gfn, $sformatf(
                    "fast_responder: Will drive %0s to %b in %0d fast clock cycles",
                    "io_status",
                    new_value,
                    cycles_before_io_status
                    ), UVM_HIGH)
          cfg.clk_rst_vif.wait_clks(cycles_before_io_status);
          if (new_value) cfg.esc_clk_rst_vif.start_clk();
          else cfg.esc_clk_rst_vif.stop_clk();
          cfg.clk_rst_vif.wait_clks(2);
          cfg.pwrmgr_vif.fast_cb.pwr_clk_rsp.io_status <= new_value;
          `uvm_info(`gfn, $sformatf(
                    "fast_responder: Driving %0s to %b",
                    "io_status",
                    cfg.pwrmgr_vif.fast_cb.pwr_clk_req.io_ip_clk_en
                    ), UVM_HIGH)
          drop_objection("io_status");
        end

      forever
        @cfg.pwrmgr_vif.fast_cb.pwr_clk_req.main_ip_clk_en begin
          raise_objection("main_status");
          `FAST_RESPONSE_ACTION("main_status", cfg.pwrmgr_vif.fast_cb.pwr_clk_rsp.main_status,
                                cfg.pwrmgr_vif.fast_cb.pwr_clk_req.main_ip_clk_en,
                                cycles_before_main_status)
          drop_objection("main_status");
        end
      forever
        @cfg.pwrmgr_vif.fast_cb.pwr_clk_req.usb_ip_clk_en begin
          raise_objection("usb_status");
          `FAST_RESPONSE_ACTION("usb_status", cfg.pwrmgr_vif.fast_cb.pwr_clk_rsp.usb_status,
                                cfg.pwrmgr_vif.fast_cb.pwr_clk_req.usb_ip_clk_en,
                                cycles_before_usb_status)
          drop_objection("usb_status");
        end
      forever
        @cfg.pwrmgr_vif.fast_cb.pwr_lc_req.lc_init begin
          raise_objection("lc_done");
          `FAST_RESPONSE_ACTION("lc_done", cfg.pwrmgr_vif.fast_cb.pwr_lc_rsp.lc_done,
                                cfg.pwrmgr_vif.fast_cb.pwr_lc_req.lc_init, cycles_before_lc_done)
          drop_objection("lc_done");
        end
      forever
        @cfg.pwrmgr_vif.fast_cb.pwr_otp_req.otp_init begin
          raise_objection("otp_done");
          `FAST_RESPONSE_ACTION("otp_done", cfg.pwrmgr_vif.fast_cb.pwr_otp_rsp.otp_done,
                                cfg.pwrmgr_vif.fast_cb.pwr_otp_req.otp_init, cycles_before_otp_done)
          drop_objection("otp_done");
        end
    join_none
  endtask : fast_responder
  `undef FAST_RESPONSE_ACTION

  function void control_assertions(bit enable);
    `uvm_info(`gfn, $sformatf("%0sabling assertions", enable ? "En" : "Dis"), UVM_MEDIUM)
    cfg.pwrmgr_ast_sva_vif.disable_sva = !enable;
    cfg.pwrmgr_clock_enables_sva_vif.disable_sva = !enable;
    cfg.pwrmgr_rstmgr_sva_vif.disable_sva = !enable;
  endfunction

  local task wait_for_fall_through();
    wait(!cfg.pwrmgr_vif.pwr_cpu.core_sleeping);
    exp_wakeup_fall_through = 1'b1;
    exp_intr = 1'b1;
    `uvm_info(`gfn, "wait_for_fall_through succeeds", UVM_MEDIUM)
  endtask

  local task wait_for_abort();
    wait(!cfg.pwrmgr_vif.pwr_flash.flash_idle || !cfg.pwrmgr_vif.pwr_otp_rsp.otp_idle ||
          !cfg.pwrmgr_vif.pwr_lc_rsp.lc_idle);
    exp_wakeup_abort = 1'b1;
    exp_intr = 1'b1;
    `uvm_info(`gfn, "wait_for_abort succeeds", UVM_MEDIUM)
  endtask

  local task wait_for_low_power_transition();
    wait_for_reset_cause(pwrmgr_pkg::LowPwrEntry);
    exp_wakeup_reasons = wakeups & wakeups_en;
    exp_intr = 1'b1;
    `uvm_info(`gfn, "Setting expected interrupt", UVM_MEDIUM)
  endtask

  task process_low_power_hint();
    // Timeout if the low power transition waits too long for WFI.
    `DV_SPINWAIT(wait(cfg.pwrmgr_vif.pwr_cpu.core_sleeping);,
                 "timeout waiting for core_sleeping",
                 100_000)
    `uvm_info(`gfn, "In process_low_power_hint pre forks", UVM_MEDIUM)
    fork
      begin : isolation_fork
        fork
          wait_for_fall_through();
          wait_for_abort();
          wait_for_low_power_transition();
        join_any
        disable fork;
      end
    join
    // At this point we know the low power transition went through or was aborted.
    // If it went through, determine if the transition to active state is for a reset, and
    // cancel the expected interrupt.
    if (exp_wakeup_reasons) begin
      wait(cfg.pwrmgr_vif.slow_state == pwrmgr_pkg::SlowPwrStateMainPowerOn);
      if (cfg.pwrmgr_vif.pwrup_cause == pwrmgr_pkg::Reset) begin
        `uvm_info(`gfn, "Cancelling expected interrupt", UVM_MEDIUM)
        exp_intr = 1'b0;
      end
    end
  endtask

  // Updates control CSR.
  task update_control_csr();
    ral.control.core_clk_en.set(control_enables.core_clk_en);
    ral.control.io_clk_en.set(control_enables.io_clk_en);
    ral.control.usb_clk_en_lp.set(control_enables.usb_clk_en_lp);
    ral.control.usb_clk_en_active.set(control_enables.usb_clk_en_active);
    ral.control.main_pd_n.set(control_enables.main_pd_n);
    ral.control.low_power_hint.set(low_power_hint);
    // Disable assertions when main power is down.
    control_assertions(control_enables.main_pd_n);
    `uvm_info(`gfn, $sformatf(
              "Setting control CSR to 0x%x, enables=%p, low_power_hint=%b",
              ral.control.get(),
              control_enables,
              low_power_hint
              ), UVM_MEDIUM)
    csr_update(.csr(ral.control));

    // Predict the effect of the potential low power transition.
    fork
      if (low_power_hint) process_low_power_hint();
    join_none
  endtask : update_control_csr

  // This enables the fast fsm to transition to low power when all nvms are idle after the
  // transition is enabled by software and cpu WFI. When not all are idle the transition is
  // aborted.
  virtual task set_nvms_idle(logic flash_idle = 1'b1, logic lc_idle = 1'b1, logic otp_idle = 1'b1);
    `uvm_info(`gfn, $sformatf(
              "Setting nvms idle: flash=%b, lc=%b, otp=%b", flash_idle, lc_idle, otp_idle),
              UVM_MEDIUM)
    cfg.pwrmgr_vif.update_flash_idle(flash_idle);
    cfg.pwrmgr_vif.update_lc_idle(lc_idle);
    cfg.pwrmgr_vif.update_otp_idle(otp_idle);
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

  virtual task wait_for_csr_to_propagate_to_slow_domain();
    csr_wr(.ptr(ral.cfg_cdc_sync), .value(1'b1));
    csr_spinwait(.ptr(ral.cfg_cdc_sync), .exp_data(1'b0),
                 .timeout_ns(PropagationToSlowTimeoutInNanoSeconds));
    `uvm_info(`gfn, "CSR updates made it to the slow domain", UVM_MEDIUM)
  endtask

  // Checks the reset_status CSR matches expectations.
  task check_reset_status(resets_t expected_resets);
    csr_rd_check(.ptr(ral.reset_status[0]), .compare_value(expected_resets),
                 .err_msg("reset_status"));
  endtask

  task fast_check_reset_status(resets_t expected_resets);
    logic [pwrmgr_reg_pkg::NumRstReqs-1:0] init_reset_status;
    `uvm_info(`gfn, "init reset status", UVM_HIGH);
    init_reset_status = cfg.pwrmgr_vif.reset_status;

    if (expected_resets != init_reset_status) begin
      `DV_SPINWAIT(wait(cfg.pwrmgr_vif.reset_status != init_reset_status);,
                   $sformatf("reset_status wait timeout exp:%x  init:%x",
                             expected_resets, init_reset_status),
                   15_000)
    end
    `DV_CHECK_EQ(cfg.pwrmgr_vif.reset_status, expected_resets)
  endtask

  // Checks the wake_status CSR matches expectations.
  task check_wake_status(wakeups_t expected_wakeups);
    csr_rd_check(.ptr(ral.wake_status[0]), .compare_value(expected_wakeups),
                 .err_msg("wake_status"));
  endtask

  task fast_check_wake_status(wakeups_t expected_wakeups);
    logic [pwrmgr_reg_pkg::NumWkups-1:0] init_wakeup_status;
    `uvm_info(`gfn, "init wakeup", UVM_HIGH);
    init_wakeup_status = cfg.pwrmgr_vif.wakeup_status;

    if (expected_wakeups != init_wakeup_status) begin
      `DV_SPINWAIT(wait(cfg.pwrmgr_vif.wakeup_status != init_wakeup_status);,
                   $sformatf("wakeup_status wait timeout exp:%x init:%x",
                             expected_wakeups, init_wakeup_status), 15_000)
    end
    `DV_CHECK_EQ(cfg.pwrmgr_vif.wakeup_status, expected_wakeups)
  endtask

  task fast_check_wake_info(wakeups_t reasons, wakeups_t prior_reasons = '0, bit fall_through,
                            bit prior_fall_through = '0, bit abort, bit prior_abort = '0);
    pwrmgr_reg_pkg::pwrmgr_hw2reg_wake_info_reg_t initial_value, exp_value;
    initial_value = cfg.pwrmgr_vif.wake_info;

    if (disable_wakeup_capture) begin
      exp_value.reasons = prior_reasons;
      exp_value.fall_through = prior_fall_through;
      exp_value.abort = prior_abort;
    end else begin
      exp_value.reasons = (reasons | prior_reasons);
      exp_value.fall_through = (fall_through | prior_fall_through);
      exp_value.abort = (abort | prior_abort);
    end
    if (exp_value != initial_value) begin
      `DV_SPINWAIT(wait(cfg.pwrmgr_vif.wake_info != initial_value);,
                   $sformatf("wake info wait timeout  exp:%p  init:%p",
                             exp_value, initial_value), 15_000)
    end
  endtask : fast_check_wake_info

  // Checks the wake_info CSR matches expectations depending on capture disable.
  // The per-field "prior_" arguments support cases where the wake_info register was not
  // cleared and may contain residual values.
  task check_wake_info(wakeups_t reasons, wakeups_t prior_reasons = '0, bit fall_through,
                       bit prior_fall_through = '0, bit abort, bit prior_abort = '0);
    if (disable_wakeup_capture) begin
      csr_rd_check(.ptr(ral.wake_info.reasons), .compare_value(prior_reasons),
                   .err_msg("With capture disabled"));
      csr_rd_check(.ptr(ral.wake_info.fall_through), .compare_value(prior_fall_through),
                   .err_msg("With capture disabled"));
      csr_rd_check(.ptr(ral.wake_info.abort), .compare_value(prior_abort),
                   .err_msg("With capture disabled"));
    end else begin
      csr_rd_check(.ptr(ral.wake_info.reasons), .compare_value(reasons | prior_reasons),
                   .err_msg("With capture enabled"));
      csr_rd_check(.ptr(ral.wake_info.fall_through),
                   .compare_value(fall_through | prior_fall_through),
                   .err_msg("With capture enabled"));
      csr_rd_check(.ptr(ral.wake_info.abort), .compare_value(abort | prior_abort),
                   .err_msg("With capture enabled"));
    end
  endtask : check_wake_info

  task clear_wake_info();
    // To clear wake_info, capture must be disabled.
    csr_wr(.ptr(ral.wake_info_capture_dis), .value(1'b1));
    csr_wr(.ptr(ral.wake_info), .value('1));
  endtask

  function void send_escalation_reset();
    `uvm_info(`gfn, "Sending escalation reset", UVM_MEDIUM)
    cfg.m_esc_agent_cfg.vif.sender_cb.esc_tx_int <= 2'b10;
  endfunction

  function void clear_escalation_reset();
    `uvm_info(`gfn, "Clearing escalation reset", UVM_MEDIUM)
    cfg.m_esc_agent_cfg.vif.sender_cb.esc_tx_int <= 2'b01;
  endfunction

  // bad_bits = {done, good}
  task add_rom_rsp_noise();
    bit [MUBI4W*2-1:0] bad_bits;
    int delay;

    repeat (10) begin
      delay = $urandom_range(5, 10);
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(bad_bits,
                                         bad_bits[MUBI4W*2-1:MUBI4W] != prim_mubi_pkg::MuBi4True;
                                         bad_bits[MUBI4W*2-1:MUBI4W] != prim_mubi_pkg::MuBi4False;
                                         bad_bits[MUBI4W-1:0] != prim_mubi_pkg::MuBi4False;
                                         bad_bits[MUBI4W-1:0] != prim_mubi_pkg::MuBi4True;)
      cfg.pwrmgr_vif.rom_ctrl = bad_bits;
      #(delay * 10ns);
    end
  endtask : add_rom_rsp_noise

  // Drive rom_ctrl at post reset stage
  virtual task init_rom_response();
    if (cfg.pwrmgr_vif.fast_state == pwrmgr_pkg::FastPwrStateActive ||
        cfg.pwrmgr_vif.fast_state == pwrmgr_pkg::FastPwrStateAckPwrUp ||
        cfg.pwrmgr_vif.fast_state == pwrmgr_pkg::FastPwrStateStrap    ||
        cfg.pwrmgr_vif.fast_state == pwrmgr_pkg::FastPwrStateRomCheck) begin
      cfg.pwrmgr_vif.rom_ctrl.done = prim_mubi_pkg::MuBi4True;
      cfg.pwrmgr_vif.rom_ctrl.good = prim_mubi_pkg::MuBi4True;
    end else begin
      cfg.pwrmgr_vif.rom_ctrl.done = prim_mubi_pkg::MuBi4False;
      cfg.pwrmgr_vif.rom_ctrl.good = prim_mubi_pkg::MuBi4False;
      @(cfg.pwrmgr_vif.fast_state == pwrmgr_pkg::FastPwrStateAckPwrUp);
      cfg.pwrmgr_vif.rom_ctrl.good = prim_mubi_pkg::MuBi4True;
      @(cfg.pwrmgr_vif.fast_state == pwrmgr_pkg::FastPwrStateRomCheck);
      cfg.aon_clk_rst_vif.wait_clks(10);
      cfg.pwrmgr_vif.rom_ctrl.good = prim_mubi_pkg::MuBi4False;
      cfg.aon_clk_rst_vif.wait_clks(5);
      cfg.pwrmgr_vif.rom_ctrl.good = prim_mubi_pkg::MuBi4True;
      cfg.aon_clk_rst_vif.wait_clks(5);
      cfg.pwrmgr_vif.rom_ctrl.done = prim_mubi_pkg::MuBi4True;
    end
  endtask

endclass : pwrmgr_base_vseq
