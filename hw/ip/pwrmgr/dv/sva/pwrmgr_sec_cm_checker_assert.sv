// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// add description here TBD
module pwrmgr_sec_cm_checker_assert (
  input clk_i,
  input rst_ni,
  input prim_mubi_pkg::mubi4_t rom_intg_chk_dis,
  input prim_mubi_pkg::mubi4_t rom_intg_chk_ok,
  input lc_ctrl_pkg::lc_tx_t lc_dft_en_i,
  input lc_ctrl_pkg::lc_tx_t lc_hw_debug_en_i,
  input prim_mubi_pkg::mubi4_t rom_ctrl_done_i,
  input prim_mubi_pkg::mubi4_t rom_ctrl_good_i
);

  bit   disable_sva;
  bit   reset_or_disable;

  always_comb reset_or_disable = !rst_ni || disable_sva;

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
                rom_intg_chk_dis or lc_dft_en_i or lc_hw_debug_en_i, reset_or_disable)

  `ASYNC_ASSERT(RomIntgChkDisFalse_A,
                rom_intg_chk_dis == prim_mubi_pkg::MuBi4False |->
                (lc_dft_en_i != lc_ctrl_pkg::On || lc_hw_debug_en_i != lc_ctrl_pkg::On),
                rom_intg_chk_dis or lc_dft_en_i or lc_hw_debug_en_i, reset_or_disable)

  // check rom_intg_chk_ok
  // rom_ctrl_i go through cdc. So use synchronous assertion.
  // rom_intg_chk_ok can be any values.
  `ASYNC_ASSERT(RomIntgChkOkTrue_A,
                rom_intg_chk_ok == prim_mubi_pkg::MuBi4True |->
                (rom_intg_chk_dis == prim_mubi_pkg::MuBi4True &&
                 rom_ctrl_done_i == prim_mubi_pkg::MuBi4True) ||
                (rom_ctrl_done_i == prim_mubi_pkg::MuBi4True &&
                 rom_ctrl_good_i == prim_mubi_pkg::MuBi4True),
                rom_intg_chk_ok or rom_intg_chk_dis or rom_ctrl_done_i or rom_ctrl_good_i,
                reset_or_disable)

  `ASYNC_ASSERT(RomIntgChkOkFalse_A,
                rom_intg_chk_ok != prim_mubi_pkg::MuBi4True |->
                (rom_intg_chk_dis == prim_mubi_pkg::MuBi4False ||
                 rom_ctrl_done_i != prim_mubi_pkg::MuBi4True) &&
                (rom_ctrl_done_i != prim_mubi_pkg::MuBi4True ||
                 rom_ctrl_good_i != prim_mubi_pkg::MuBi4True),
                rom_intg_chk_ok or rom_intg_chk_dis or rom_ctrl_done_i or rom_ctrl_good_i,
                reset_or_disable)

`undef ASYNC_ASSERT
endmodule // pwrmgr_sec_cm_checker_assert
