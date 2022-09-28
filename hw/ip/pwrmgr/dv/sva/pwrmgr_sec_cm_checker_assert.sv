// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// add description here TBD
module pwrmgr_sec_cm_checker_assert (
  input clk_i,
  input rst_ni,
  input clk_lc_i,
  input rst_lc_ni,
  input clk_esc_i,
  input rst_esc_ni,
  input rst_main_ni,
  input clk_slow_i,
  input rst_slow_ni,
  input pwrmgr_pkg::pwr_rst_req_t pwr_rst_o,
  input slow_fsm_invalid,
  input pwrmgr_pkg::fast_pwr_state_e fast_state,
  input prim_mubi_pkg::mubi4_t rom_intg_chk_dis,
  input prim_mubi_pkg::mubi4_t rom_intg_chk_ok,
  input lc_ctrl_pkg::lc_tx_t lc_dft_en_i,
  input lc_ctrl_pkg::lc_tx_t lc_hw_debug_en_i,
  input slow_esc_rst_req,
  input slow_mp_rst_req,
  input main_pd_ni,
  input prim_mubi_pkg::mubi4_t rom_ctrl_done_i,
  input prim_mubi_pkg::mubi4_t rom_ctrl_good_i
);

  bit   disable_sva;
  bit   reset_or_disable;
  bit   esc_reset_or_disable;
  bit   slow_reset_or_disable;

  always_comb reset_or_disable = !rst_ni || disable_sva;
  always_comb esc_reset_or_disable = !rst_esc_ni || disable_sva;
  always_comb slow_reset_or_disable = !rst_slow_ni || disable_sva;

  function automatic bit fsm_state_is_valid(pwrmgr_pkg::fast_pwr_state_e state);
    pwrmgr_pkg::fast_pwr_state_e legal_st = legal_st.first();

    do begin
      if (state == legal_st) return 1'b1;
      legal_st = legal_st.next();
    end
    while (legal_st != legal_st.first());
    return 1'b0;
  endfunction

`define ASYNC_ASSERT(_name, _prop, _sigs, _rst) \
  _name: assert property (@(_sigs) disable iff ((_rst) !== '0) (_prop)) \
         else begin\
           `ASSERT_ERROR(_name)\
         end

  // Assuming lc_dft_en_i and lc_hw_debug_en_i are asynchronous
  // rom_intg_chk_dis only allows two states.
  `ASYNC_ASSERT(RomIntgChkDisTrue_A,
                rom_intg_chk_dis == prim_mubi_pkg::MuBi4True |->
                (lc_dft_en_i == lc_ctrl_pkg::On && lc_hw_debug_en_i == lc_ctrl_pkg::On),
                (rom_intg_chk_dis | lc_dft_en_i | lc_hw_debug_en_i), reset_or_disable)

  `ASYNC_ASSERT(RomIntgChkDisFalse_A,
                rom_intg_chk_dis == prim_mubi_pkg::MuBi4False |->
                (lc_dft_en_i != lc_ctrl_pkg::On || lc_hw_debug_en_i != lc_ctrl_pkg::On),
                (rom_intg_chk_dis | lc_dft_en_i | lc_hw_debug_en_i), reset_or_disable)

  // check rom_intg_chk_ok
  // rom_ctrl_i go through cdc. So use synchronous assertion.
  // rom_intg_chk_ok can be any values.
  `ASYNC_ASSERT(RomIntgChkOkTrue_A,
                rom_intg_chk_ok == prim_mubi_pkg::MuBi4True |->
                (rom_intg_chk_dis == prim_mubi_pkg::MuBi4True &&
                 rom_ctrl_done_i == prim_mubi_pkg::MuBi4True) ||
                (rom_ctrl_done_i == prim_mubi_pkg::MuBi4True &&
                 rom_ctrl_good_i == prim_mubi_pkg::MuBi4True),
                (rom_intg_chk_ok | rom_intg_chk_dis | rom_ctrl_done_i | rom_ctrl_good_i),
                reset_or_disable)

  `ASYNC_ASSERT(RomIntgChkOkFalse_A,
                rom_intg_chk_ok != prim_mubi_pkg::MuBi4True |->
                (rom_intg_chk_dis == prim_mubi_pkg::MuBi4False ||
                 rom_ctrl_done_i != prim_mubi_pkg::MuBi4True) &&
                (rom_ctrl_done_i != prim_mubi_pkg::MuBi4True ||
                 rom_ctrl_good_i != prim_mubi_pkg::MuBi4True),
                (rom_intg_chk_ok | rom_intg_chk_dis | rom_ctrl_done_i | rom_ctrl_good_i),
                reset_or_disable)

`undef ASYNC_ASSERT

  // pwr_rst_o.rstreqs checker
  // sec_cm_esc_rx_clk_bkgn_chk, sec_cm_esc_rx_clk_local_esc
  // if esc_timeout, rstreqs[ResetEscIdx] should be asserted
  `ASSERT(RstreqChkEsctimeout_A,
          $rose(slow_esc_rst_req) ##1 slow_esc_rst_req |->
          ##[0:2] pwr_rst_o.rstreqs[pwrmgr_pkg::ResetEscIdx],
          clk_i, reset_or_disable)

// sec_cm_fsm_terminal
// if slow_fsm or fast_fsm is invalid,
// both pwr_rst_o.rst_lc_req and pwr_rst_o.rst_sys_req should be set
  bit fsm_is_valid;
  always_comb fsm_is_valid = fsm_state_is_valid(fast_state);

  `ASSERT(RstreqChkFsmterm_A,
          $rose(slow_fsm_invalid) || !fsm_is_valid
          |=> ##[1:10] $rose(pwr_rst_o.rst_lc_req & pwr_rst_o.rst_sys_req),
          clk_i, reset_or_disable)

// sec_cm_ctrl_flow_global_esc
// if esc_rst_req is set, pwr_rst_o.rstreqs[ResetEscIdx] should be asserted.
  `ASSERT(RstreqChkGlbesc_A,
          $rose(slow_esc_rst_req) ##1 slow_esc_rst_req |->
          ##[0:2] (pwr_rst_o.rstreqs[pwrmgr_pkg::ResetEscIdx] | !rst_esc_ni),
          clk_i, reset_or_disable)

// sec_cm_main_pd_rst_local_esc
// if power is up and rst_main_ni goes low, pwr_rst_o.rstreqs[ResetMainPwrIdx] should be asserted
  `ASSERT(RstreqChkMainpd_A,
          slow_mp_rst_req |->
          ##[0:5] pwr_rst_o.rstreqs[pwrmgr_pkg::ResetMainPwrIdx],
          clk_i, reset_or_disable)

endmodule // pwrmgr_sec_cm_checker_assert
