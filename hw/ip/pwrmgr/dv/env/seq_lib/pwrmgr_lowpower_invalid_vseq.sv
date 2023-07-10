// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// The test to create transition to invalid state from any lowpower transitions.
class pwrmgr_lowpower_invalid_vseq extends pwrmgr_base_vseq;

  `uvm_object_utils(pwrmgr_lowpower_invalid_vseq)
  `uvm_object_new

  // Create enum to map rtl local sparse state
  // to continuous dv state.
  typedef enum bit [3:0] {
    DVWaitDisClks      = 0,
    DVWaitFallThrough  = 1,
    DVWaitNvmIdleChk   = 2,
    DVWaitLowPowerPrep = 3,
    DVWaitReqPwrDn     = 4,
    DVWaitLowPower     = 5,
    DVWaitEnableClocks = 6,
    DVWaitReleaseLcRst = 7,
    DVWaitOtpInit      = 8,
    DVWaitLcInit       = 9,
    DVWaitAckPwrUp     = 10,
    DVWaitRomCheck     = 11,
    DVWaitStrap        = 12,
    DVWaitActive       = 13,
    DVWaitInvalid      = 14
  } reset_index_e;

  constraint wakeups_c {wakeups != 0;}
  constraint wakeup_en_c {
    solve wakeups before wakeups_en;
    |(wakeups_en & wakeups) == 1'b1;
  }

  task body();
    reset_index_e reset_index;
    resets_t enabled_resets;
    string path = "tb.dut.u_fsm.fsm_invalid_i";
    int    num_of_target_states = 4;

    // Spurious interrupt check can be executed by
    // residue of lowpower task. Since we cannot kill csr op
    // by disable fork, we have to disable spurious interrup check.
    cfg.invalid_st_test = 1;

    wait_for_fast_fsm_active();
    `uvm_info(`gfn, "At body start", UVM_MEDIUM)
    check_wake_status('0);
    reset_index = DVWaitFallThrough;

    for (int i = 0; i < num_of_target_states; ++i) begin
      `uvm_info(`gfn, $sformatf("Starting new round%0d %s", i, reset_index.name), UVM_MEDIUM)
      `DV_CHECK_RANDOMIZE_FATAL(this)
      setup_interrupt(.enable(en_intr));
      fork
        start_lowpower_transition();
        begin
          int wait_time_ns = 10000;
          `DV_SPINWAIT(wait(cfg.pwrmgr_vif.fast_state == dv2rtl_st(reset_index));, $sformatf(
                       "Timed out waiting for state %s", reset_index.name), wait_time_ns)

          @cfg.clk_rst_vif.cbn;
          `DV_CHECK(uvm_hdl_force(path, 1))
          `uvm_info(`gfn, "Injected invalid slow state", UVM_MEDIUM)
          @cfg.clk_rst_vif.cb;
        end
      join_any
      @cfg.clk_rst_vif.cb;
      `DV_CHECK(uvm_hdl_release(path))
      `DV_CHECK(cfg.pwrmgr_vif.fast_state, pwrmgr_pkg::FastPwrStateInvalid)

      repeat (10) @cfg.clk_rst_vif.cb;

      apply_reset();
      reset_index=reset_index.next();
      wait_for_fast_fsm_active();
    end  // for (int i = 0; i < 4; ++i)
  endtask

  task start_lowpower_transition();
    wakeups_t enabled_wakeups = wakeups_en & wakeups;
    `DV_CHECK(enabled_wakeups, $sformatf(
              "Some wakeup must be enabled: wkups=%b, wkup_en=%b", wakeups, wakeups_en))
    `uvm_info(`gfn, $sformatf("Enabled wakeups=0x%x", enabled_wakeups), UVM_MEDIUM)
    csr_wr(.ptr(ral.wakeup_en[0]), .value(wakeups_en));
    low_power_hint = 1;
    update_control_csr();

    wait_for_csr_to_propagate_to_slow_domain();
    `uvm_info(`gfn, $sformatf("Enabled wakeups=0x%x", enabled_wakeups), UVM_MEDIUM)

    // Initiate low power transition.
    cfg.pwrmgr_vif.update_cpu_sleeping(1'b1);
    set_nvms_idle();

    `DV_WAIT(cfg.pwrmgr_vif.fast_state != pwrmgr_pkg::FastPwrStateActive)

    if (ral.control.main_pd_n.get_mirrored_value() == 1'b0) begin
      wait_for_reset_cause(pwrmgr_pkg::LowPwrEntry);
    end

    // Now bring it back.
    cfg.clk_rst_vif.wait_clks(cycles_before_wakeup);
    cfg.pwrmgr_vif.update_wakeups(wakeups);

    wait(cfg.pwrmgr_vif.pwr_clk_req.main_ip_clk_en == 1'b1);

    // wakeups should be registered.
    cfg.pwrmgr_vif.update_wakeups('1);

    wait_for_fast_fsm_active();
    `uvm_info(`gfn, "Back from wakeup", UVM_MEDIUM)
  endtask : start_lowpower_transition

  function pwrmgr_pkg::fast_pwr_state_e dv2rtl_st(reset_index_e idx);
    case (idx)
      DVWaitDisClks: return pwrmgr_pkg::FastPwrStateDisClks;
      DVWaitFallThrough: return pwrmgr_pkg::FastPwrStateFallThrough;
      DVWaitNvmIdleChk: return pwrmgr_pkg::FastPwrStateNvmIdleChk;
      DVWaitLowPowerPrep: return pwrmgr_pkg::FastPwrStateLowPowerPrep;
      DVWaitReqPwrDn: return pwrmgr_pkg::FastPwrStateReqPwrDn;
      DVWaitLowPower: return pwrmgr_pkg::FastPwrStateLowPower;
      DVWaitEnableClocks: return pwrmgr_pkg::FastPwrStateEnableClocks;
      DVWaitReleaseLcRst: return pwrmgr_pkg::FastPwrStateReleaseLcRst;
      DVWaitOtpInit: return pwrmgr_pkg::FastPwrStateOtpInit;
      DVWaitLcInit: return pwrmgr_pkg::FastPwrStateLcInit;
      DVWaitAckPwrUp: return pwrmgr_pkg::FastPwrStateAckPwrUp;
      DVWaitRomCheck: return pwrmgr_pkg::FastPwrStateRomCheckDone;
      DVWaitStrap: return pwrmgr_pkg::FastPwrStateStrap;
      DVWaitActive: return pwrmgr_pkg::FastPwrStateActive;
      DVWaitInvalid: return pwrmgr_pkg::FastPwrStateInvalid;
      default: begin
        `uvm_error("dv2rma_st", $sformatf("unknown index:%0d", idx))
      end
    endcase
  endfunction : dv2rtl_st

endclass : pwrmgr_lowpower_invalid_vseq
