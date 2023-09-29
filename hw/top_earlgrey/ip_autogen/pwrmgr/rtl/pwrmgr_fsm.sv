// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Power Manager Fast FSM
//

`include "prim_assert.sv"

module pwrmgr_fsm import pwrmgr_pkg::*; import pwrmgr_reg_pkg::*;(
  input clk_i,
  input rst_ni,
  input clk_slow_i,
  input rst_slow_ni,

  // interface with slow_fsm
  input req_pwrup_i,
  input pwrup_cause_e pwrup_cause_i,
  output logic ack_pwrup_o,
  output logic req_pwrdn_o,
  input ack_pwrdn_i,
  input low_power_entry_i,
  input main_pd_ni,
  input [TotalResetWidth-1:0] reset_reqs_i,
  input fsm_invalid_i,
  output logic clr_slow_req_o,
  input usb_ip_clk_en_i,
  output logic usb_ip_clk_status_o,

  // consumed in pwrmgr
  output logic wkup_o,        // generate wake interrupt
  output logic fall_through_o,
  output logic abort_o,
  output logic clr_hint_o,
  output logic clr_cfg_lock_o,

  // rstmgr
  output pwr_rst_req_t pwr_rst_o,
  input pwr_rst_rsp_t pwr_rst_i,

  // clkmgr
  output pwr_clk_req_t ips_clk_en_o,
  input pwr_clk_rsp_t clk_en_status_i,

  // otp
  output logic otp_init_o,
  input otp_done_i,
  input otp_idle_i,

  // lc
  output logic lc_init_o,
  input lc_done_i,
  input lc_idle_i,
  input lc_ctrl_pkg::lc_tx_t lc_dft_en_i,
  input lc_ctrl_pkg::lc_tx_t lc_hw_debug_en_i,

  // flash
  input flash_idle_i,

  // rom_ctrl
  input prim_mubi_pkg::mubi4_t rom_ctrl_done_i,
  input prim_mubi_pkg::mubi4_t rom_ctrl_good_i,

  // pinmux
  output logic strap_o,
  output logic low_power_o,

  // processing elements
  output lc_ctrl_pkg::lc_tx_t fetch_en_o
);

  import prim_mubi_pkg::mubi4_t;
  import prim_mubi_pkg::mubi4_test_true_strict;
  import prim_mubi_pkg::mubi4_or_hi;
  import prim_mubi_pkg::mubi4_and_hi;
  import lc_ctrl_pkg::lc_tx_and_hi;
  import lc_ctrl_pkg::lc_tx_test_true_strict;

  // The code below always assumes the always on domain is index 0
  `ASSERT_INIT(AlwaysOnIndex_A, ALWAYS_ON_DOMAIN == 0)

  // when there are multiple on domains, the latter 1 should become another parameter
  localparam int OffDomainSelStart = ALWAYS_ON_DOMAIN + 1;

  // all powered down domains have resets asserted
  logic pd_n_rsts_asserted;

  // all domains have resets asserted
  logic all_rsts_asserted;

  // resets are valid
  logic reset_valid;

  // reset hint to rstmgr
  reset_cause_e reset_cause_q, reset_cause_d;

  // reset request
  logic reset_req;
  logic direct_rst_req;
  logic ndmreset_req;
  logic hw_rst_req;
  logic sw_rst_req;

  // strap sample should only happen on cold boot or when the
  // the system goes through a reset cycle
  logic strap_sampled;

  // disable processing element fetching
  lc_ctrl_pkg::lc_tx_t fetch_en_q, fetch_en_d;

  fast_pwr_state_e state_d, state_q;
  logic reset_ongoing_q, reset_ongoing_d;
  logic req_pwrdn_q, req_pwrdn_d;
  logic ack_pwrup_q, ack_pwrup_d;
  logic ip_clk_en_q, ip_clk_en_d;
  logic [PowerDomains-1:0] rst_lc_req_q, rst_sys_req_q;
  logic [PowerDomains-1:0] rst_lc_req_d, rst_sys_req_d;
  logic otp_init;
  logic lc_init;
  logic low_power_q, low_power_d;

  assign pd_n_rsts_asserted = pwr_rst_i.rst_lc_src_n[PowerDomains-1:OffDomainSelStart] == '0 &
                              pwr_rst_i.rst_sys_src_n[PowerDomains-1:OffDomainSelStart] == '0;

  logic lc_rsts_valid;
  assign lc_rsts_valid = ((rst_lc_req_q & ~pwr_rst_i.rst_lc_src_n) |
                          (~rst_lc_req_q & pwr_rst_i.rst_lc_src_n)) == {PowerDomains{1'b1}};
  logic sys_rsts_valid;
  assign sys_rsts_valid = ((rst_sys_req_q & ~pwr_rst_i.rst_sys_src_n) |
                           (~rst_sys_req_q & pwr_rst_i.rst_sys_src_n)) == {PowerDomains{1'b1}};

  assign all_rsts_asserted = lc_rsts_valid & sys_rsts_valid;

  // Any reset request was asserted.
  assign reset_req = |reset_reqs_i;

  // Any peripheral triggererd hardware reset request.
  assign hw_rst_req = |reset_reqs_i[NumRstReqs-1:0];

  // Direct reset request that bypass checks.
  assign direct_rst_req = reset_reqs_i[ResetEscIdx] |
                          reset_reqs_i[ResetMainPwrIdx];

  // Ndm reset request.
  assign ndmreset_req = reset_reqs_i[ResetNdmIdx];

  // Software triggered reset request.
  assign sw_rst_req = reset_reqs_i[ResetSwReqIdx];

  // when in low power path, resets are controlled by domain power down
  // when in reset path, all resets must be asserted
  // when the reset cause is something else, it is invalid
  assign reset_valid = reset_cause_q == LowPwrEntry ? main_pd_ni | pd_n_rsts_asserted :
                       reset_cause_q == HwReq       ? all_rsts_asserted : 1'b0;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ack_pwrup_q <= 1'b0;
      req_pwrdn_q <= 1'b0;
      reset_ongoing_q <= 1'b0;
      ip_clk_en_q <= 1'b0;
      rst_lc_req_q <= {PowerDomains{1'b1}};
      rst_sys_req_q <= {PowerDomains{1'b1}};
      reset_cause_q <= ResetUndefined;
      low_power_q <= 1'b1;
    end else begin
      ack_pwrup_q <= ack_pwrup_d;
      req_pwrdn_q <= req_pwrdn_d;
      reset_ongoing_q <= reset_ongoing_d;
      ip_clk_en_q <= ip_clk_en_d;
      rst_lc_req_q <= rst_lc_req_d;
      rst_sys_req_q <= rst_sys_req_d;
      reset_cause_q <= reset_cause_d;
      low_power_q <= low_power_d;
    end
  end

  // SEC_CM: FSM.SPARSE
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, fast_pwr_state_e, FastPwrStateLowPower)

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      strap_sampled <= 1'b0;
    end else if (&rst_sys_req_q) begin
      strap_sampled <= 1'b0;
    end else if (strap_o) begin
      strap_sampled <= 1'b1;
    end
  end

  prim_lc_sender u_fetch_en (
    .clk_i,
    .rst_ni,
    .lc_en_i(fetch_en_d),
    .lc_en_o(fetch_en_q)
  );
  assign fetch_en_o = fetch_en_q;

  // Life cycle broadcast may take time to propagate through the system.
  // The sync below simulates that behavior using the slowest clock in the
  // system.
  logic slow_lc_done;
  logic lc_done;

  prim_flop_2sync #(
    .Width(1)
  ) u_slow_sync_lc_done (
    .clk_i(clk_slow_i),
    .rst_ni(rst_slow_ni),
    .d_i(lc_done_i),
    .q_o(slow_lc_done)
  );

  prim_flop_2sync #(
    .Width(1)
  ) u_sync_lc_done (
    .clk_i,
    .rst_ni,
    .d_i(slow_lc_done),
    .q_o(lc_done)
  );


  logic clks_enabled;
  logic clks_disabled;

  // clocks all enabled computed as follows:
  // if enable is high, meaning clock is requested to turn on, the status must
  // also be 1.
  // if enable is low, meaning clock is not requested to turn on, the status is
  // don't care.
  // the bit-wise OR of both conditions must be all true.
  assign clks_enabled = ip_clk_en_q &&
                        &((ips_clk_en_o & clk_en_status_i) | ~ips_clk_en_o);

  // clocks all disabled is the opposite:
  // if enable is low the status must also be low.
  // if enable is high, the status is don't care.
  // the bit-wise OR of both conditions must be all true.
  assign clks_disabled = ~ip_clk_en_q &&
                         &((~ips_clk_en_o & ~clk_en_status_i) | ips_clk_en_o);


  // rom integrity checks are disabled during TEST / RMA states
  // During TEST / RMA states, both dft_en and hw_debug_en are On.
  // During DEV / PROD states, either both signals are Off, or only
  // hw_debug_en is On

  mubi4_t rom_intg_chk_dis;
  assign rom_intg_chk_dis = lc_tx_test_true_strict(lc_tx_and_hi(lc_dft_en_i, lc_hw_debug_en_i)) ?
                            prim_mubi_pkg::MuBi4True :
                            prim_mubi_pkg::MuBi4False;

  mubi4_t rom_intg_chk_done;
  mubi4_t rom_intg_chk_good;
  assign rom_intg_chk_done = mubi4_or_hi(mubi4_and_hi(rom_intg_chk_dis, rom_ctrl_done_i),
                                         rom_ctrl_done_i);
  assign rom_intg_chk_good = mubi4_or_hi(rom_intg_chk_dis, rom_ctrl_good_i);

  always_comb begin
    otp_init = 1'b0;
    lc_init = 1'b0;
    wkup_o = 1'b0;
    fall_through_o = 1'b0;
    abort_o = 1'b0;
    clr_hint_o = 1'b0;
    clr_cfg_lock_o = 1'b0;
    strap_o = 1'b0;
    clr_slow_req_o = 1'b0;

    state_d = state_q;
    ack_pwrup_d = ack_pwrup_q;
    req_pwrdn_d = req_pwrdn_q;
    reset_ongoing_d = reset_ongoing_q;
    ip_clk_en_d = ip_clk_en_q;
    rst_lc_req_d = rst_lc_req_q;
    rst_sys_req_d = rst_sys_req_q;
    reset_cause_d = reset_cause_q;
    low_power_d = low_power_q;
    fetch_en_d = fetch_en_q;

    unique case(state_q)

      FastPwrStateLowPower: begin
        if (req_pwrup_i || reset_ongoing_q) begin
          state_d = FastPwrStateEnableClocks;
        end
      end

      FastPwrStateEnableClocks: begin
        ip_clk_en_d = 1'b1;
        if (clks_enabled) begin
          state_d = FastPwrStateReleaseLcRst;
        end
      end

      FastPwrStateReleaseLcRst: begin
        rst_lc_req_d = '0;  // release rst_lc_n for all power domains
        rst_sys_req_d = '0; // release rst_sys_n for all power domains
        // once all resets are released continue to otp initilization
        if (&pwr_rst_i.rst_lc_src_n) begin
          state_d = FastPwrStateOtpInit;
        end
      end

      FastPwrStateOtpInit: begin
        otp_init = 1'b1;

        if (otp_done_i) begin
          state_d = FastPwrStateLcInit;
        end
      end

      FastPwrStateLcInit: begin
        lc_init = 1'b1;

        if (lc_done) begin
          state_d = FastPwrStateAckPwrUp;

        end
      end

      FastPwrStateAckPwrUp: begin
        // only ack the slow_fsm if we actually transitioned through it
        ack_pwrup_d = !reset_ongoing_q;

        // wait for request power up to drop relative to ack
        if (!req_pwrup_i || reset_ongoing_q) begin
          ack_pwrup_d = 1'b0;
          clr_cfg_lock_o = 1'b1;
          // generate a wakeup interrupt if we intended to go to low power
          // and we were woken from low power with a wakeup and not reset
          wkup_o = (pwrup_cause_i == Wake) & (reset_cause_q == LowPwrEntry);
          // This constitutes the end of a reset cycle
          reset_ongoing_d = 1'b0;
          state_d = FastPwrStateStrap;
        end
      end

      FastPwrStateStrap: begin
        strap_o = ~strap_sampled;
        state_d =  FastPwrStateRomCheckDone;
      end

      FastPwrStateRomCheckDone: begin
        // zero outgoing low power indication
        low_power_d = '0;
        reset_cause_d = ResetNone;

        // When done is observed, advance to good check
        if (mubi4_test_true_strict(rom_intg_chk_done)) begin
          state_d = FastPwrStateRomCheckGood;
        end
      end

      FastPwrStateRomCheckGood: begin
        if (mubi4_test_true_strict(rom_intg_chk_good)) begin
          state_d = FastPwrStateActive;
        end
      end

      FastPwrStateActive: begin
        // only in active state, allow processor to execute
        fetch_en_d = lc_ctrl_pkg::On;

        // when handling reset request or low power entry of any
        // kind, stop processor from fetching
        if (reset_req || low_power_entry_i) begin
          fetch_en_d = lc_ctrl_pkg::Off;
          reset_cause_d = ResetUndefined;
          state_d = FastPwrStateDisClks;
        end
      end

      FastPwrStateDisClks: begin
        ip_clk_en_d = 1'b0;

        if (clks_disabled) begin
          state_d = reset_req ? FastPwrStateNvmShutDown : FastPwrStateFallThrough;
          low_power_d = ~reset_req;
        end else begin
          // escalation was received, skip all handshaking and directly reset
          state_d = direct_rst_req ? FastPwrStateNvmShutDown : state_q;
          low_power_d = ~reset_req;
        end
      end

      // Low Power Path
      FastPwrStateFallThrough: begin
        clr_hint_o = 1'b1;

        // The processor was interrupted after it asserted WFI and is executing again
        if (!low_power_entry_i) begin
          ip_clk_en_d = 1'b1;
          wkup_o = 1'b1;
          fall_through_o = 1'b1;
          state_d = FastPwrStateRomCheckDone;
        end else begin
          state_d = FastPwrStateNvmIdleChk;
        end
      end

      FastPwrStateNvmIdleChk: begin

        if (otp_idle_i && lc_idle_i && flash_idle_i) begin
          state_d = FastPwrStateLowPowerPrep;
        end else begin
          ip_clk_en_d = 1'b1;
          wkup_o = 1'b1;
          abort_o = 1'b1;
          state_d = FastPwrStateRomCheckDone;
        end
      end

      FastPwrStateLowPowerPrep: begin
        // reset cause is set only if main power domain will be turned off
        reset_cause_d = LowPwrEntry;

        // reset non-always-on domains if requested
        // this includes the clock manager, which implies pwr/rst managers must
        // be fed directly from the source
        for (int i = OffDomainSelStart; i < PowerDomains; i++) begin
          rst_lc_req_d[i] = ~main_pd_ni;
          rst_sys_req_d[i] = ~main_pd_ni;
        end

        if (reset_valid) begin
          state_d = FastPwrStateReqPwrDn;
        end
      end

      FastPwrStateReqPwrDn: begin
        req_pwrdn_d = 1'b1;

        if (ack_pwrdn_i) begin
          req_pwrdn_d = 1'b0;
          state_d = FastPwrStateLowPower;
        end
      end

      // Reset Path
      FastPwrStateNvmShutDown: begin
        clr_hint_o = 1'b1;
        reset_ongoing_d = 1'b1;
        state_d = FastPwrStateResetPrep;
      end

      FastPwrStateResetPrep: begin
        reset_cause_d = HwReq;
        rst_lc_req_d = {PowerDomains{1'b1}};
        rst_sys_req_d = {PowerDomains{(hw_rst_req |
                                       direct_rst_req |
                                       sw_rst_req) |
                                      (ndmreset_req &
                                       lc_ctrl_pkg::lc_tx_test_false_loose(lc_hw_debug_en_i))}};


        state_d = FastPwrStateResetWait;
      end

      FastPwrStateResetWait: begin
        rst_lc_req_d = {PowerDomains{1'b1}};
        clr_slow_req_o = reset_reqs_i[ResetMainPwrIdx];
        // The main power reset request is checked here specifically because it is
        // the only reset request in the system that operates on the POR domain.
        // This has to be the case since it would otherwise not be able to monitor
        // the non-always-on domains.
        //
        // As a result of this, the normal reset process does not automatically
        // wipe out the reset request, so we specifically clear it and wait for it to be
        // cleared before proceeding.  This also implies if the system is under a persistent
        // glitch, or if someone just turned off the power before pwrmgr turns it off itself,
        // we will stay stuck here and perpetually hold the system in reset.
        if (reset_valid && !reset_reqs_i[ResetMainPwrIdx]) begin
          state_d = FastPwrStateLowPower;
        end
      end


      // Terminal state, kill everything
      // SEC_CM: FSM.TERMINAL
      default: begin
        rst_lc_req_d = {PowerDomains{1'b1}};
        rst_sys_req_d = {PowerDomains{1'b1}};
        ip_clk_en_d = 1'b0;
      end
    endcase // unique case (state_q)

    if (fsm_invalid_i) begin
      // the slow fsm is completely out of sync, transition to terminal state
      state_d = FastPwrStateInvalid;
    end


  end // always_comb

  assign ack_pwrup_o = ack_pwrup_q;
  assign req_pwrdn_o = req_pwrdn_q;
  assign low_power_o = low_power_q;

  assign pwr_rst_o.rst_lc_req = rst_lc_req_q;
  assign pwr_rst_o.rst_sys_req = rst_sys_req_q;
  assign pwr_rst_o.reset_cause = reset_cause_q;
  assign pwr_rst_o.rstreqs = reset_reqs_i[HwResetWidth-1:0];

  // main and io clocks are only turned on/off as part of normal
  // power sequence
  assign ips_clk_en_o.main_ip_clk_en = ip_clk_en_q;
  assign ips_clk_en_o.io_ip_clk_en = ip_clk_en_q;
  prim_flop #(
    .Width(1),
    .ResetValue(1'b0)
  ) u_usb_ip_clk_en (
    .clk_i,
    .rst_ni,
    .d_i(ip_clk_en_d & usb_ip_clk_en_i),
    .q_o(ips_clk_en_o.usb_ip_clk_en)
  );
  assign usb_ip_clk_status_o = clk_en_status_i.usb_status;

  prim_flop #(
    .Width(1),
    .ResetValue(1'b0)
  ) u_reg_otp_init (
    .clk_i,
    .rst_ni,
    .d_i(otp_init),
    .q_o(otp_init_o)
  );

  prim_flop #(
    .Width(1),
    .ResetValue(1'b0)
  ) u_reg_lc_init (
    .clk_i,
    .rst_ni,
    .d_i(lc_init),
    .q_o(lc_init_o)
  );


endmodule
