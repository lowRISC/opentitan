// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// add description here TBD
module pwrmgr_sec_cm_checker_assert (
  input clk_i,
  input rst_ni,
  input prim_mubi_pkg::mubi4_t rom_intg_chk_dis,
  input lc_ctrl_pkg::lc_tx_t lc_dft_en_i,
  input lc_ctrl_pkg::lc_tx_t lc_hw_debug_en_i
);

  bit   disable_sva;
  bit   reset_or_disable;

  always_comb reset_or_disable = !rst_ni || disable_sva;


  // Assuming lc_dft_en_i and lc_hw_debug_en_i are asynchronous
  `ASSERT(RomIntgChkDisTrue_A,
          rom_intg_chk_dis == prim_mubi_pkg::MuBi4True |=>
          (lc_dft_en_i == lc_ctrl_pkg::On && lc_hw_debug_en_i == lc_ctrl_pkg::On),
          rom_intg_chk_dis, reset_or_disable)

  `ASSERT(RomIntgChkDisFalse_A,
          rom_intg_chk_dis == prim_mubi_pkg::MuBi4False |=>
          (lc_dft_en_i != lc_ctrl_pkg::On || lc_hw_debug_en_i != lc_ctrl_pkg::On),
          rom_intg_chk_dis, reset_or_disable)
endmodule // pwrmgr_sec_cm_checker_assert
