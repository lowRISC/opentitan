// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Implements functional coverage for rom_ctrl

interface rom_ctrl_cov_if (
    input logic                       clk_i,
    input kmac_pkg::app_rsp_t         kmac_data_i,
    input kmac_pkg::app_req_t         kmac_data_o,
    input logic                       exp_digest_de,
    input tlul_pkg::tl_h2d_t          rom_tl_i,
    input tlul_pkg::tl_d2h_t          rom_tl_o,
    input tlul_pkg::tl_h2d_t          regs_tl_i,
    input rom_ctrl_pkg::pwrmgr_data_t pwrmgr_data_o
);

  `include "dv_fcov_macros.svh"
  import uvm_pkg::*;
  import dv_utils_pkg::*;

  bit en_full_cov = 1'b1;
  bit en_intg_cov = 1'b1;
  /////////////////////////////////////
  // KMAC APP interface cover points //
  /////////////////////////////////////

  covergroup rom_ctrl_kmac_cg @(posedge clk_i);
    option.name         = "rom_ctrl_kmac_cg";
    option.comment      = "KMAC interface behaviors";
    option.per_instance = 1;

    // Cover some basic stalling behavior on the kmac ready input
    cp_kmac_ready: coverpoint kmac_data_i.ready iff (kmac_data_o.valid) {
      bins zero_delay_5 = (1'b1[*5]);
      bins stall_1      = (1'b1 => 1'b0 => 1'b1);
      bins stall_long   = (1'b0[*5:10] => 1'b1);
      bins stall_repeat = (1'b0[*1:10] => 1'b1 => 1'b0[*1:10]);
    }

    // Cover the different delays on the kmac done signal
    cp_kmac_done: coverpoint {kmac_data_i.done, exp_digest_de} {
      bins kmac_first = {2'b11}; // kmac responds while still reading digest
      bins rom_first  = (2'b00 => 2'b10); // kmac responds after digest read
      bins same_cycle = (2'b01 => 2'b10); // kmac responds as digest read completes
    }

  endgroup
  `DV_FCOV_INSTANTIATE_CG(rom_ctrl_kmac_cg, en_full_cov)

  /////////////////////////////////////
  // ROM TLUL interface cover points //
  /////////////////////////////////////

  covergroup rom_ctrl_tlul_cg @(posedge clk_i);
    option.name         = "rom_ctrl_tlul_cg";
    option.comment      = "TLUL interface behaviors";
    option.per_instance = 1;

    // Cover rom requests around the time of check completion
    cp_rom_req_check: coverpoint {rom_tl_i.a_valid, pwrmgr_data_o.done} {
      bins req_before_done  = ({1'b1, prim_mubi_pkg::MuBi4False} =>
                               {1'b1, prim_mubi_pkg::MuBi4True});
      bins req_and_done     = ({1'b0, prim_mubi_pkg::MuBi4False} =>
                               {1'b1, prim_mubi_pkg::MuBi4True});
      bins req_after_done   = ({1'b0, prim_mubi_pkg::MuBi4True} =>
                               {1'b1, prim_mubi_pkg::MuBi4True});
    }

    // Cover csr requests around the time of check completion
    cp_regs_req_check: coverpoint {regs_tl_i.a_valid, pwrmgr_data_o.done} {
      bins req_before_done  = ({1'b1, prim_mubi_pkg::MuBi4False} =>
                               {1'b1, prim_mubi_pkg::MuBi4True});
      bins req_and_done     = ({1'b0, prim_mubi_pkg::MuBi4False} =>
                               {1'b1, prim_mubi_pkg::MuBi4True});
      bins req_after_done   = ({1'b0, prim_mubi_pkg::MuBi4True} =>
                               {1'b1, prim_mubi_pkg::MuBi4True});
    }

  endgroup
  `DV_FCOV_INSTANTIATE_CG(rom_ctrl_tlul_cg, en_full_cov)

  ////////////////////////////
  // ROM check cover points //
  ////////////////////////////

  covergroup rom_ctrl_check_cg @(posedge clk_i);
    option.name         = "rom_ctrl_check_cg";
    option.comment      = "ROM check coverpoints";
    option.per_instance = 1;

    // Cover the check pass and fail case
    cp_rom_check_condition: coverpoint pwrmgr_data_o.good
      iff (pwrmgr_data_o.done == prim_mubi_pkg::MuBi4True) {
      bins check_pass = {prim_mubi_pkg::MuBi4True};
      bins check_fail = {prim_mubi_pkg::MuBi4False};
    }

  endgroup
  `DV_FCOV_INSTANTIATE_CG(rom_ctrl_check_cg, en_full_cov)

endinterface
