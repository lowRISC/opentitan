// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

interface core_ibex_pmp_fcov_if import ibex_pkg::*; #(
    parameter bit          PMPEnable      = 1'b0,
    // Granularity of NAPOT access,
    // 0 = No restriction, 1 = 8 byte, 2 = 16 byte, 3 = 32 byte, etc.
    parameter int unsigned PMPGranularity = 0,
    // Number of implemented regions
    parameter int unsigned PMPNumRegions  = 4
) (
  input clk_i,
  input rst_ni,

  input ibex_pkg::pmp_cfg_t  csr_pmp_cfg     [PMPNumRegions],
  input logic                pmp_req_err     [3],
  input pmp_mseccfg_t        csr_pmp_mseccfg,

  input logic data_req_out,

  input logic lsu_req_done
);
  `include "dv_fcov_macros.svh"
  import uvm_pkg::*;

  // Enum to give more readable coverage results for privilege bits. 4 bits are from the pmpcfg CSF
  // (L, X, W, R) and the 5th is the MML bit. Setting the MML bit changes the meaning of the other
  // 4 bits
  // TODO: Better MML names?
  typedef enum logic [4:0] {
    PMP_PRIV_NONE     = 5'b00000,
    PMP_PRIV_R        = 5'b00001,
    PMP_PRIV_W        = 5'b00010,
    PMP_PRIV_WR       = 5'b00011,
    PMP_PRIV_X        = 5'b00100,
    PMP_PRIV_XR       = 5'b00101,
    PMP_PRIV_XW       = 5'b00110,
    PMP_PRIV_XWR      = 5'b00111,
    PMP_PRIV_L        = 5'b01000,
    PMP_PRIV_LR       = 5'b01001,
    PMP_PRIV_LW       = 5'b01010,
    PMP_PRIV_LWR      = 5'b01011,
    PMP_PRIV_LX       = 5'b01100,
    PMP_PRIV_LXR      = 5'b01101,
    PMP_PRIV_LXW      = 5'b01110,
    PMP_PRIV_LXWR     = 5'b01111,
    PMP_PRIV_MML_NONE = 5'b10000,
    PMP_PRIV_MML_R    = 5'b10001,
    PMP_PRIV_MML_W    = 5'b10010,
    PMP_PRIV_MML_WR   = 5'b10011,
    PMP_PRIV_MML_X    = 5'b10100,
    PMP_PRIV_MML_XR   = 5'b10101,
    PMP_PRIV_MML_XW   = 5'b10110,
    PMP_PRIV_MML_XWR  = 5'b10111,
    PMP_PRIV_MML_L    = 5'b11000,
    PMP_PRIV_MML_LR   = 5'b11001,
    PMP_PRIV_MML_LW   = 5'b11010,
    PMP_PRIV_MML_LWR  = 5'b11011,
    PMP_PRIV_MML_LX   = 5'b11100,
    PMP_PRIV_MML_LXR  = 5'b11101,
    PMP_PRIV_MML_LXW  = 5'b11110,
    PMP_PRIV_MML_LXWR = 5'b11111
  } pmp_priv_bits_e;

  // Break out PMP signals into individually named signals for direct use in `cross` as it cannot
  // deal with hierarchical references or unpacked arrays.
  logic pmp_iside_req_err;
  logic pmp_iside2_req_err;
  logic pmp_dside_req_err;

  assign pmp_iside_req_err  = pmp_req_err[PMP_I];
  assign pmp_iside2_req_err = pmp_req_err[PMP_I2];
  assign pmp_dside_req_err  = pmp_req_err[PMP_D];

  bit en_pmp_fcov;

  initial begin
    if (PMPEnable) begin
      void'($value$plusargs("enable_ibex_fcov=%d", en_pmp_fcov));
    end else begin
      en_pmp_fcov = 1'b0;
    end
  end

  if (PMPEnable) begin : g_pmp_cgs
    for (genvar i_region = 0; i_region < PMPNumRegions; i_region += 1) begin : g_pmp_region_fcov
      pmp_priv_bits_e pmp_region_priv_bits;

      assign pmp_region_priv_bits = pmp_priv_bits_e'({csr_pmp_mseccfg.mml,
                                                      csr_pmp_cfg[i_region].lock,
                                                      csr_pmp_cfg[i_region].exec,
                                                      csr_pmp_cfg[i_region].write,
                                                      csr_pmp_cfg[i_region].read});

      covergroup pmp_region_cg @(posedge clk_i);
        cp_region_mode : coverpoint csr_pmp_cfg[i_region].mode;

        cp_region_priv_bits : coverpoint pmp_region_priv_bits {
          wildcard ignore_bins ignore = {5'b1????};
          wildcard illegal_bins illegal = {5'b0??10};
        }

        cp_priv_lvl_iside : coverpoint g_pmp.pmp_priv_lvl[PMP_I] {
          illegal_bins illegal = {PRIV_LVL_H, PRIV_LVL_S};
        }

        cp_req_type_iside : coverpoint g_pmp.pmp_req_type[PMP_I] {
          illegal_bins illegal = {PMP_ACC_WRITE, PMP_ACC_READ};
        }

        cp_priv_lvl_iside2 : coverpoint g_pmp.pmp_priv_lvl[PMP_I2] {
          illegal_bins illegal = {PRIV_LVL_H, PRIV_LVL_S};
        }

        cp_req_type_iside2 : coverpoint g_pmp.pmp_req_type[PMP_I2] {
          illegal_bins illegal = {PMP_ACC_WRITE, PMP_ACC_READ};
        }

        cp_priv_lvl_dside : coverpoint g_pmp.pmp_priv_lvl[PMP_D] {
          illegal_bins illegal = {PRIV_LVL_H, PRIV_LVL_S};
        }

        cp_req_type_dside : coverpoint g_pmp.pmp_req_type[PMP_D] {
          illegal_bins illegal = {PMP_ACC_EXEC};
        }

        pmp_iside_mode_cross : cross cp_region_mode, pmp_iside_req_err
          iff (g_pmp_fcov_signals.g_pmp_region_fcov[i_region].fcov_pmp_region_ichan_access);

        pmp_iside2_mode_cross : cross cp_region_mode, pmp_iside2_req_err
          iff (g_pmp_fcov_signals.g_pmp_region_fcov[i_region].fcov_pmp_region_ichan2_access);

        pmp_dside_mode_cross : cross cp_region_mode, pmp_dside_req_err
          iff (g_pmp_fcov_signals.g_pmp_region_fcov[i_region].fcov_pmp_region_dchan_access);

        // TODO: Coverage for accesses that don't match any regions

        pmp_iside_priv_bits_cross :
          cross cp_region_priv_bits, cp_req_type_iside, cp_priv_lvl_iside, pmp_iside_req_err
            iff (g_pmp_fcov_signals.g_pmp_region_fcov[i_region].fcov_pmp_region_ichan_access &&
                 g_pmp_fcov_signals.fcov_pmp_region_ichan_priority[i_region]                 &&
                 csr_pmp_cfg[i_region].mode != PMP_MODE_OFF) {

          // Will never see a succesful exec access when execute is disallowed
          illegal_bins illegal_allow_exec = (binsof(cp_region_priv_bits) intersect {5'b00000,
            5'b00001, 5'b00010, 5'b00011, 5'b01000, 5'b01001, 5'b01010, 5'b01011} &&
            binsof(cp_req_type_iside) intersect {PMP_ACC_EXEC} &&
            binsof(pmp_iside_req_err) intersect {0}) with (cp_priv_lvl_iside == PRIV_LVL_U ||
                                                           (cp_region_priv_bits & 5'b01000));

          // Will never see an exec access denied when executed is allowed
          illegal_bins illegal_deny_exec = binsof(cp_region_priv_bits) intersect {5'b00100, 5'b00101,
            5'b00110, 5'b00111, 5'b01100, 5'b01101, 5'b01110, 5'b01111} &&
            binsof(cp_req_type_iside) intersect {PMP_ACC_EXEC} &&
            binsof(pmp_iside_req_err) intersect {1};
        }

        pmp_iside2_priv_bits_cross :
          cross cp_region_priv_bits, cp_req_type_iside2, cp_priv_lvl_iside2, pmp_iside2_req_err
            iff (g_pmp_fcov_signals.g_pmp_region_fcov[i_region].fcov_pmp_region_ichan2_access &&
                 g_pmp_fcov_signals.fcov_pmp_region_ichan2_priority[i_region]                 &&
                 csr_pmp_cfg[i_region].mode != PMP_MODE_OFF) {

          // Will never see a succesful exec access when execute is disallowed
          illegal_bins illegal_allow_exec = (binsof(cp_region_priv_bits) intersect {5'b00000,
            5'b00001, 5'b00010, 5'b00011, 5'b01000, 5'b01001, 5'b01010, 5'b01011} &&
            binsof(cp_req_type_iside2) intersect {PMP_ACC_EXEC} &&
            binsof(pmp_iside2_req_err) intersect {0}) with (cp_priv_lvl_iside2 == PRIV_LVL_U ||
                                                           (cp_region_priv_bits & 5'b01000));

          // Will never see an exec access denied when execute is allowed
          illegal_bins illegal_deny_exec = binsof(cp_region_priv_bits) intersect {5'b00100, 5'b00101,
            5'b00110, 5'b00111, 5'b01100, 5'b01101, 5'b01110, 5'b01111} &&
            binsof(cp_req_type_iside2) intersect {PMP_ACC_EXEC} &&
            binsof(pmp_iside2_req_err) intersect {1};
        }

        pmp_dside_priv_bits_cross :
          cross cp_region_priv_bits, cp_req_type_dside, cp_priv_lvl_dside, pmp_dside_req_err
            iff (g_pmp_fcov_signals.g_pmp_region_fcov[i_region].fcov_pmp_region_dchan_access &&
                 g_pmp_fcov_signals.fcov_pmp_region_dchan_priority[i_region]                 &&
                 csr_pmp_cfg[i_region].mode != PMP_MODE_OFF) {

          // Will never see a succesful read access when read is disallowed
          illegal_bins illegal_allow_read = (binsof(cp_region_priv_bits) intersect {5'b00000,
            5'b00010, 5'b00100, 5'b00110, 5'b01000, 5'b01010, 5'b01100, 5'b01110} &&
            binsof(cp_req_type_dside) intersect {PMP_ACC_READ} &&
            binsof(pmp_dside_req_err) intersect {0}) with (cp_priv_lvl_dside == PRIV_LVL_U ||
                                                           (cp_region_priv_bits & 5'b01000));

          // Will never see a read access denied when read is allowed
          illegal_bins illegal_deny_read = binsof(cp_region_priv_bits) intersect {5'b00001, 5'b00011,
            5'b00101, 5'b00111, 5'b01001, 5'b01011, 5'b01101, 5'b01111} &&
            binsof(cp_req_type_dside) intersect {PMP_ACC_READ} &&
            binsof(pmp_dside_req_err) intersect {1};

          // Will never see a succesful write access when write is disallowed
          illegal_bins illegal_allow_write = (binsof(cp_region_priv_bits) intersect {5'b00000,
            5'b00001, 5'b00100, 5'b00101, 5'b01000, 5'b01001, 5'b01100, 5'b01101} &&
            binsof(cp_req_type_dside) intersect {PMP_ACC_WRITE} &&
            binsof(pmp_dside_req_err) intersect {0}) with (cp_priv_lvl_dside == PRIV_LVL_U ||
                                                           (cp_region_priv_bits & 5'b01000));

          // Will never see a write access denied when write is allowed
          illegal_bins illegal_deny_write = binsof(cp_region_priv_bits) intersect {5'b00010, 5'b00011,
            5'b00110, 5'b00111, 5'b01010, 5'b01011, 5'b01110, 5'b01111} &&
            binsof(cp_req_type_dside) intersect {PMP_ACC_WRITE} &&
            binsof(pmp_dside_req_err) intersect {1};
        }
      endgroup

      `DV_FCOV_INSTANTIATE_CG(pmp_region_cg, en_pmp_fcov)
    end

    covergroup pmp_top_cg @(posedge clk_i);
      cp_pmp_iside_region_override :
        coverpoint g_pmp.pmp_i.g_access_check[PMP_I].fcov_pmp_region_override
          iff (if_stage_i.if_id_pipe_reg_we);

      cp_pmp_iside2_region_override :
        coverpoint g_pmp.pmp_i.g_access_check[PMP_I2].fcov_pmp_region_override
          iff (if_stage_i.if_id_pipe_reg_we);

      cp_pmp_dside_region_override :
        coverpoint g_pmp.pmp_i.g_access_check[PMP_D].fcov_pmp_region_override iff (data_req_out);
    endgroup

    `DV_FCOV_INSTANTIATE_CG(pmp_top_cg, en_pmp_fcov)
  end

endinterface
