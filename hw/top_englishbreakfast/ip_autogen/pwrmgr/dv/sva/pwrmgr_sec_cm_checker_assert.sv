// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This has a number of assertions to check security countermeasures. They are
// individually described in their comments.
module pwrmgr_sec_cm_checker_assert
  import pwrmgr_reg_pkg::*;
(
  input clk_i,
  input rst_ni,
  input clk_lc_i,
  input rst_lc_ni,
  input clk_esc_i,
  input rst_esc_ni,
  input rst_main_ni,
  input clk_slow_i,
  input rst_slow_ni,
  input logic io_clk_en,
  input pwrmgr_pkg::pwr_rst_req_t pwr_rst_o,
  input slow_fsm_invalid,
  input fast_fsm_invalid,
  input prim_mubi_pkg::mubi4_t rom_intg_chk_dis,
  input prim_mubi_pkg::mubi4_t rom_intg_chk_done,
  input prim_mubi_pkg::mubi4_t rom_intg_chk_good,
  input pwrmgr_pkg::fast_pwr_state_e fast_state,
  input lc_ctrl_pkg::lc_tx_t lc_dft_en_i,
  input lc_ctrl_pkg::lc_tx_t lc_hw_debug_en_i,
  input esc_timeout,
  input slow_esc_rst_req,
  input slow_mp_rst_req,
  input main_pd_ni,
  input prim_mubi_pkg::mubi4_t rom_ctrl_done_i,
  input prim_mubi_pkg::mubi4_t rom_ctrl_good_i
);

  bit disable_sva;
  bit reset_or_disable;
  bit esc_reset_or_disable;
  bit slow_reset_or_disable;

  always_comb reset_or_disable = !rst_ni || disable_sva;
  always_comb esc_reset_or_disable = !rst_esc_ni || disable_sva;
  always_comb slow_reset_or_disable = !rst_slow_ni || disable_sva;

  // rom_intg_chk_dis only allows two states.
  // Note that lc_dft_en_i and lc_hw_debug_en_i are already synchronized to clk_i at this
  // hierarchy level.
  // Check that rom integrity checks are disabled when lc_dft_en_i and lc_hw_debug_en_i are active.
  `ASSERT(RomIntgChkDisTrue_A,
          rom_intg_chk_dis == prim_mubi_pkg::MuBi4True |->
          (lc_dft_en_i == lc_ctrl_pkg::On &&
           lc_hw_debug_en_i == lc_ctrl_pkg::On),
          clk_i,
          reset_or_disable)

  // Check that rom integrity checks are enabled when either lc_dft_en_i or lc_hw_debug_en_i are
  // inactive.
  `ASSERT(RomIntgChkDisFalse_A,
          rom_intg_chk_dis == prim_mubi_pkg::MuBi4False |->
          (lc_dft_en_i !== lc_ctrl_pkg::On ||
           lc_hw_debug_en_i !== lc_ctrl_pkg::On),
          clk_i,
          reset_or_disable)

  // For any assertions involving state transitions, also allow cases where the fsm
  // transitions to an invalid state, since we inject invalid encodings at random.

  // Check that unless rom_intg_chk_done is mubi true the fast state machine will
  // stay in FastPwrStateRomCheckDone or transition to Invalid.
  `ASSERT(RomBlockCheckGoodState_A,
          rom_intg_chk_done != prim_mubi_pkg::MuBi4True &&
          fast_state == pwrmgr_pkg::FastPwrStateRomCheckDone |=>
          fast_state == pwrmgr_pkg::FastPwrStateRomCheckDone ||
          fast_state == pwrmgr_pkg::FastPwrStateInvalid,
          clk_i,
          reset_or_disable)

  // Check that when rom_intg_chk_done is mubi true the fast state machine will transition
  // from FastPwrStateRomCheckDone to either FastPwrStateRomCheckGood or Invalid.
  `ASSERT(RomAllowCheckGoodState_A,
          rom_intg_chk_done == prim_mubi_pkg::MuBi4True &&
          fast_state == pwrmgr_pkg::FastPwrStateRomCheckDone |=>
          fast_state == pwrmgr_pkg::FastPwrStateRomCheckGood ||
          fast_state == pwrmgr_pkg::FastPwrStateInvalid,
          clk_i,
          reset_or_disable)

  // Check that unless rom_intg_chk_good is mubi true or rom_intg_chk_dis is mubi true
  // the fast state machine will stay in FastPwrStateRomCheckGood.
  `ASSERT(RomBlockActiveState_A,
          rom_intg_chk_good != prim_mubi_pkg::MuBi4True &&
          rom_intg_chk_dis != prim_mubi_pkg::MuBi4True &&
          fast_state == pwrmgr_pkg::FastPwrStateRomCheckGood |=>
          fast_state == pwrmgr_pkg::FastPwrStateRomCheckGood ||
          fast_state == pwrmgr_pkg::FastPwrStateInvalid,
          clk_i,
          reset_or_disable)

  // Check that when one of rom_intg_chk_good or rom_intg_chk_dis is mubi true the fast
  // state machine will transition from FastPwrStateRomCheckGood to FastPwrStateActive
  // or Invalid.
  `ASSERT(RomAllowActiveState_A,
          (rom_intg_chk_good == prim_mubi_pkg::MuBi4True ||
           rom_intg_chk_dis == prim_mubi_pkg::MuBi4True) &&
          fast_state == pwrmgr_pkg::FastPwrStateRomCheckGood |=>
          fast_state == pwrmgr_pkg::FastPwrStateActive ||
          fast_state == pwrmgr_pkg::FastPwrStateInvalid,
          clk_i,
          reset_or_disable)

  // For testpoints sec_cm_esc_rx_clk_bkgn_chk, sec_cm_esc_rx_clk_local_esc.
  // If the escalation clock (clk_esc_i) stops for too many cycles and is not
  // disabled, an escalation timeout should be requested until rst_lc_ni goes
  // active.
  // The bound of cycles is 128 cycles for the counter, 8 cycles maximum for the
  // counter to engage, and 2 cycles for a synchronizer. Use negedge of clk_i
  // to sample clk_esc_i as 1 when active, and 0 when inactive.
  `ASSERT(EscClkStopEscTimeout_A, !clk_esc_i && io_clk_en [* (128 + 8 + 2)] |=>
          esc_timeout || !rst_lc_ni, !clk_i, reset_or_disable)

  // For testpoints sec_cm_esc_rx_clk_bkgn_chk, sec_cm_esc_rx_clk_local_esc.
  // Escalation timeout should not be requested when rst_nc_ni is active.
  `ASSERT(EscTimeoutStoppedByClReset_A,
          !rst_lc_ni |-> !esc_timeout, clk_i, reset_or_disable)

  // For testpoints sec_cm_esc_rx_clk_bkgn_chk, sec_cm_esc_rx_clk_local_esc.
  // If escalation timeout is detected a reset request will be generated.
  `ASSERT(EscTimeoutTriggersReset_A, esc_timeout |=> ##[1:3] slow_esc_rst_req,
          clk_slow_i, !rst_slow_ni || disable_sva)

  // pwr_rst_o.rstreqs checker
  // For testpoints sec_cm_esc_rx_clk_bkgn_chk, sec_cm_esc_rx_clk_local_esc.
  // If a slow clock domain escalation reset is requested, rstreqs[ResetEscIdx]
  // should be asserted after some cycles unless rst_lc_n becomes active.
  `ASSERT(RstreqChkEsctimeout_A,
          $rose(
              slow_esc_rst_req
          ) ##1 slow_esc_rst_req |-> ##[0:10] pwr_rst_o.rstreqs[ResetEscIdx] || !rst_lc_ni,
          clk_i, reset_or_disable)

  // For testpoint sec_cm_fsm_terminal.
  // If slow_fsm or fast_fsm is invalid, both pwr_rst_o.rst_lc_req and
  // pwr_rst_o.rst_sys_req should be set.
  `ASSERT(RstreqChkFsmterm_A,
          $rose(slow_fsm_invalid) || $rose(fast_fsm_invalid)
          |-> ##[0:10] $rose(pwr_rst_o.rst_lc_req & pwr_rst_o.rst_sys_req),
          clk_i, reset_or_disable)

  // For testpoint sec_cm_ctrl_flow_global_esc.
  // If a slow clock domain escalation reset request is set, the output escalation
  // reset pwr_rst_o.rstreqs[ResetEscIdx] should be asserted after some cycles.
  `ASSERT(RstreqChkGlbesc_A,
          $rose(slow_esc_rst_req) ##1 slow_esc_rst_req |->
          ##[0:10] (pwr_rst_o.rstreqs[ResetEscIdx] | !rst_esc_ni),
          clk_i, reset_or_disable)

  // For testpoint sec_cm_main_pd_rst_local_esc.
  // If power is up and rst_main_ni goes low, pwr_rst_o.rstreqs[ResetMainPwrIdx]
  // should be asserted.
  `ASSERT(RstreqChkMainpd_A,
          slow_mp_rst_req |-> ##[0:5] pwr_rst_o.rstreqs[ResetMainPwrIdx], clk_i,
          reset_or_disable)

endmodule : pwrmgr_sec_cm_checker_assert
