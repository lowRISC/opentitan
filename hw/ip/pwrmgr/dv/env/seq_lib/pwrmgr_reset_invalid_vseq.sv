// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// The test to create transition to invalid state from any reset transitions.
class pwrmgr_reset_invalid_vseq extends pwrmgr_base_vseq;

  `uvm_object_utils(pwrmgr_reset_invalid_vseq)
  `uvm_object_new

  // Create enum to map rtl local sparse state
  // to continuous dv state.
  typedef enum bit [3:0] {
    DVWaitDisClks      = 0,
    DVWaitNvmShutDown  = 1,
    DVWaitResetPrep    = 2,
    DVWaitLowPower     = 3,
    DVWaitEnableClocks = 4,
    DVWaitReleaseLcRst = 5,
    DVWaitOtpInit      = 6,
    DVWaitLcInit       = 7,
    DVWaitAckPwrUp     = 8,
    DVWaitRomCheck     = 9,
    DVWaitStrap        = 10,
    DVWaitActive       = 11,
    DVWaitInvalid      = 12
  } reset_index_e;

  constraint wakeups_c {wakeups == 0;}
  constraint wakeups_en_c {wakeups_en == 0;}

  function void post_randomize();
    sw_rst_from_rstmgr = get_rand_mubi4_val(.t_weight(8), .f_weight(4), .other_weight(4));
    super.post_randomize();
  endfunction

  task body();
    reset_index_e reset_index;
    resets_t enabled_resets;
    string path = "tb.dut.u_fsm.fsm_invalid_i";
    int    num_of_target_states = 11;

    wait_for_fast_fsm_active();
    check_reset_status('0);
    $assertoff(0, "tb.dut.u_cdc.u_clr_reqack.SyncReqAckHoldReq");

    for (int i = 0; i < num_of_target_states; ++i) begin
      `uvm_info(`gfn, $sformatf("Starting new round %0d", i), UVM_MEDIUM)
      `DV_CHECK_RANDOMIZE_FATAL(this)
      setup_interrupt(.enable(en_intr));

      fork
        create_any_reset_event();
        begin
          int wait_time_ns = 20000;
          `DV_SPINWAIT(wait(cfg.pwrmgr_vif.fast_state == dv2rtl_st(reset_index));, $sformatf(
                       "Timed out waiting for state %s", reset_index.name), wait_time_ns)

          @cfg.clk_rst_vif.cbn;
          `uvm_info(`gfn, $sformatf("Will cause invalid state forcing %s = 1", path), UVM_MEDIUM)
          `DV_CHECK(uvm_hdl_force(path, 1))
          @cfg.clk_rst_vif.cb;
        end
      join
      @cfg.clk_rst_vif.cb;
      `DV_CHECK(uvm_hdl_release(path))
      `DV_CHECK(cfg.pwrmgr_vif.fast_state, pwrmgr_pkg::FastPwrStateInvalid)
      `uvm_info(`gfn, "All good, resetting for next round", UVM_MEDIUM)
      repeat (10) @cfg.clk_rst_vif.cb;
      apply_reset();
      reset_index=reset_index.next();
      wait_for_fast_fsm_active();
    end
  endtask

  task create_any_reset_event();
    resets_t enabled_resets = resets_t'(resets_en & resets);
    `uvm_info(`gfn, $sformatf(
              "Enabled resets=0x%x, power_reset=%b, escalation=%b, sw_reset=%b, ndm_reset=%b",
              enabled_resets,
              power_glitch_reset,
              escalation_reset,
              sw_rst_from_rstmgr == prim_mubi_pkg::MuBi4True,
              ndm_reset
              ), UVM_MEDIUM)

    `uvm_info(`gfn, "Trying to write to reset_en CSR", UVM_MEDIUM)
    csr_wr(.ptr(ral.reset_en[0]), .value(resets_en));
    // This is necessary to propagate reset_en.
    wait_for_csr_to_propagate_to_slow_domain();

    // Trigger resets. The glitch is sent prior to the externals since if it is delayed
    // it will cause a separate reset after the externals, which complicates the checks.
    if (power_glitch_reset) send_power_glitch();
    cfg.clk_rst_vif.wait_clks(cycles_before_reset);

    if (cycles_before_reset == 0) enabled_resets = 0;

    `uvm_info(`gfn, $sformatf("Sending resets=0x%x", resets), UVM_MEDIUM)
    cfg.pwrmgr_vif.update_resets(resets);
    `uvm_info(`gfn, $sformatf("Sending sw reset from rstmgr=%b", sw_rst_from_rstmgr), UVM_MEDIUM)
    if (escalation_reset) send_escalation_reset();
    if (ndm_reset) send_ndm_reset();
    cfg.pwrmgr_vif.update_sw_rst_req(sw_rst_from_rstmgr);

  endtask : create_any_reset_event

  function pwrmgr_pkg::fast_pwr_state_e dv2rtl_st(reset_index_e idx);
    case (idx)
      DVWaitDisClks: return pwrmgr_pkg::FastPwrStateDisClks;
      DVWaitNvmShutDown: return pwrmgr_pkg::FastPwrStateNvmShutDown;
      DVWaitResetPrep: return pwrmgr_pkg::FastPwrStateResetPrep;
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

endclass : pwrmgr_reset_invalid_vseq
