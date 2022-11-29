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
  input logic[33:0]          csr_pmp_addr    [PMPNumRegions],
  input logic                pmp_req_err     [3],
  input pmp_mseccfg_t        csr_pmp_mseccfg,

  input logic data_req_out,

  input fcov_csr_write
);
  localparam int unsigned PMPNumChan = 3;

  `include "dv_fcov_macros.svh"
  import uvm_pkg::*;

  // Enum to give more readable coverage results for privilege bits. 4 bits are from the pmpcfg CSF
  // (L, X, W, R) and the 5th is the MML bit. Setting the MML bit changes the meaning of the other
  // 4 bits
  typedef enum logic [4:0] {
    NONE        = 5'b00000,
    R           = 5'b00001,
    W           = 5'b00010,
    WR          = 5'b00011,
    X           = 5'b00100,
    XR          = 5'b00101,
    XW          = 5'b00110,
    XWR         = 5'b00111,
    L           = 5'b01000,
    LR          = 5'b01001,
    LW          = 5'b01010,
    LWR         = 5'b01011,
    LX          = 5'b01100,
    LXR         = 5'b01101,
    LXW         = 5'b01110,
    LXWR        = 5'b01111,
    MML_NONE    = 5'b10000,
    MML_RU      = 5'b10001,
    MML_WRM_RU  = 5'b10010,
    MML_WRU     = 5'b10011,
    MML_XU      = 5'b10100,
    MML_XRU     = 5'b10101,
    MML_WRM_WRU = 5'b10110,
    MML_XWRU    = 5'b10111,
    MML_L       = 5'b11000,
    MML_RM      = 5'b11001,
    MML_XM_XU   = 5'b11010,
    MML_WRM     = 5'b11011,
    MML_XM      = 5'b11100,
    MML_XRM     = 5'b11101,
    MML_XRM_XU  = 5'b11110,
    MML_RM_RU   = 5'b11111
  } pmp_priv_bits_e;

  // Break out PMP signals into individually named signals for direct use in `cross` as it cannot
  // deal with hierarchical references or unpacked arrays.
  logic pmp_iside_req_err;
  logic pmp_iside2_req_err;
  logic pmp_dside_req_err;

  assign pmp_iside_req_err  = pmp_req_err[PMP_I];
  assign pmp_iside2_req_err = pmp_req_err[PMP_I2];
  assign pmp_dside_req_err  = pmp_req_err[PMP_D];

  logic [PMPNumRegions-1:0] current_priv_perm_check;
  bit en_pmp_fcov;

  logic csr_wdata_mseccfg_rlb;
  logic csr_wdata_mseccfg_mmwp;
  logic csr_wdata_mseccfg_mml;

  assign csr_wdata_mseccfg_rlb = cs_registers_i.csr_wdata_int[CSR_MSECCFG_RLB_BIT];
  assign csr_wdata_mseccfg_mmwp = cs_registers_i.csr_wdata_int[CSR_MSECCFG_MMWP_BIT];
  assign csr_wdata_mseccfg_mml = cs_registers_i.csr_wdata_int[CSR_MSECCFG_MML_BIT];

  initial begin
    if (PMPEnable) begin
      void'($value$plusargs("enable_ibex_fcov=%d", en_pmp_fcov));
    end else begin
      en_pmp_fcov = 1'b0;
    end
  end

  if (PMPEnable) begin : g_pmp_cgs
    logic [PMPNumRegions-1:0] pmp_iside_match;
    logic [PMPNumRegions-1:0] pmp_iside2_match;
    logic [PMPNumRegions-1:0] pmp_dside_match;
    logic [PMPNumRegions-1:0] pmp_dside_match_last;

    logic pmp_iside_nomatch;
    logic pmp_iside2_nomatch;
    logic pmp_dside_nomatch;

    logic pmp_iside_boundary_cross;
    logic pmp_dside_boundary_cross;

    logic misaligned_pmp_err_last;

    logic [31:0] pmp_addr_napot_valid [PMPNumRegions];

    assign pmp_iside_match      = g_pmp.pmp_i.region_match_all[PMP_I];
    assign pmp_iside2_match     = g_pmp.pmp_i.region_match_all[PMP_I2];
    assign pmp_dside_match      = g_pmp.pmp_i.region_match_all[PMP_D];

    assign pmp_iside_nomatch  = ~|pmp_iside_match;
    assign pmp_iside2_nomatch = ~|pmp_iside2_match;
    assign pmp_dside_nomatch  = ~|pmp_dside_match;

    // Store the Data Channel PMP match info from the first request to calculate boundary cross
    always @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        pmp_dside_match_last    <= '0;
        misaligned_pmp_err_last <= 1'b0;
      end else if (load_store_unit_i.fcov_ls_first_req) begin
        pmp_dside_match_last    <= pmp_dside_match;
        misaligned_pmp_err_last <= load_store_unit_i.data_pmp_err_i;
      end
    end

    assign pmp_iside_boundary_cross = |(pmp_iside_match ^ pmp_iside2_match);
    assign pmp_dside_boundary_cross = |(pmp_dside_match ^ pmp_dside_match_last) &
                                      load_store_unit_i.fcov_ls_second_req;

    for (genvar i_region = 0; i_region < PMPNumRegions; i_region += 1) begin : g_pmp_region_fcov
      pmp_priv_bits_e pmp_region_priv_bits;
      pmp_priv_bits_e pmp_region_priv_bits_wr;

      assign pmp_region_priv_bits = pmp_priv_bits_e'({csr_pmp_mseccfg.mml,
                                                      csr_pmp_cfg[i_region].lock,
                                                      csr_pmp_cfg[i_region].exec,
                                                      csr_pmp_cfg[i_region].write,
                                                      csr_pmp_cfg[i_region].read});
      assign pmp_region_priv_bits_wr =
          pmp_priv_bits_e'({csr_pmp_mseccfg.mml,
                            cs_registers_i.g_pmp_registers.pmp_cfg_wdata[i_region].lock,
                            cs_registers_i.g_pmp_registers.pmp_cfg_wdata[i_region].exec,
                            cs_registers_i.g_pmp_registers.pmp_cfg_wdata[i_region].write,
                            cs_registers_i.g_pmp_registers.pmp_cfg_wdata[i_region].read});

      // Do the permission check for Data channel with the privilege level from Instruction channels.
      // This way we can check the effect of mstatus.mprv changing privilege levels for LSU related
      // operations.
      assign current_priv_perm_check[i_region] =
        g_pmp.pmp_i.perm_check_wrapper(csr_pmp_mseccfg.mml,
                                       csr_pmp_cfg[i_region],
                                       g_pmp.pmp_i.pmp_req_type_i[PMP_D],
                                       cs_registers_i.priv_mode_id_o,
                                       g_pmp.pmp_i.region_basic_perm_check[PMP_D][i_region]);

      // Each cycle this assignment creates either the value 0 if the mode is not NAPOT or 1 bit is
      // set based on how large the NAPOT region is. The size of the NAPOT region is essentially
      // encoded by how many consecutive ones there are after the last 0. This encoding is
      // specified in the "Physical Memory Protection" section of the RISC-V privileged spec.
      for (genvar i = 0; i < 32; i += 1) begin : g_pmp_napot_region_fcov
        assign pmp_addr_napot_valid[i_region][i] = csr_pmp_cfg[i_region].mode == PMP_MODE_NAPOT &&
          (csr_pmp_addr[i_region][i+2:2] == {1'b0, {i{1'b1}}});
      end

      covergroup pmp_region_cg @(posedge clk_i);
        option.per_instance = 1;
        option.name = "pmp_region_cg";

        // This coverpoint converts pmp_add_napot_valid into 32 bins. The onehot call makes sure
        // that when the entry is not in NAPOT mode, then no bin is selected. The clog2 call
        // converts the value 0...010...0 to the index of the one bit that is set.
        cp_napot_addr_modes: coverpoint $clog2(pmp_addr_napot_valid[i_region])
          iff ($onehot(pmp_addr_napot_valid[i_region])) {
          bins napot_addr[] = { [0:31] };
        }

        cp_warl_check_pmpcfg : coverpoint
          g_pmp_fcov_signals.g_pmp_region_fcov[i_region].fcov_warl_check_pmpcfg;

        cp_region_mode : coverpoint csr_pmp_cfg[i_region].mode;

        cp_region_priv_bits : coverpoint pmp_region_priv_bits {
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

        // Wildcards in crosses are not supported by VCS. As a workaround we are using `with`
        // keyword and basic logic expressions to constraint the condition as appropriate.
        pmp_iside_mode_cross : cross cp_region_mode, pmp_iside_req_err
          iff (g_pmp_fcov_signals.g_pmp_region_fcov[i_region].fcov_pmp_region_ichan_access) {
            illegal_bins illegal_off_mode_match = binsof(cp_region_mode) intersect {PMP_MODE_OFF};
          }

        pmp_iside2_mode_cross : cross cp_region_mode, pmp_iside2_req_err
          iff (g_pmp_fcov_signals.g_pmp_region_fcov[i_region].fcov_pmp_region_ichan2_access) {
            illegal_bins illegal_off_mode_match = binsof(cp_region_mode) intersect {PMP_MODE_OFF};
          }

        pmp_dside_mode_cross : cross cp_region_mode, pmp_dside_req_err
          iff (g_pmp_fcov_signals.g_pmp_region_fcov[i_region].fcov_pmp_region_dchan_access) {
            illegal_bins illegal_off_mode_match = binsof(cp_region_mode) intersect {PMP_MODE_OFF};
          }

        pmp_iside_priv_bits_cross :
          cross cp_region_priv_bits, cp_req_type_iside, cp_priv_lvl_iside, pmp_iside_req_err
            iff (g_pmp_fcov_signals.g_pmp_region_fcov[i_region].fcov_pmp_region_ichan_access &&
                 g_pmp_fcov_signals.fcov_pmp_region_ichan_priority[i_region]                 &&
                 csr_pmp_cfg[i_region].mode != PMP_MODE_OFF) {

            // Will never see a succesful exec access when execute is disallowed
            illegal_bins illegal_allow_exec =
              // Ensuring MML is low and we are not in a X allowed configuration
              (binsof(cp_region_priv_bits) intersect {NONE, R, W, WR, L, LR, LW, LWR} &&
               binsof(cp_req_type_iside) intersect {PMP_ACC_EXEC} &&
               binsof(pmp_iside_req_err) intersect {0}) with (cp_priv_lvl_iside == PRIV_LVL_U ||
                                                              (|(cp_region_priv_bits & 5'b01000)));
            illegal_bins illegal_machine_allow_exec =
              // Ensuring MML is high and we are not in a X allowed configuration in Machine Mode
              (binsof(cp_region_priv_bits) intersect {MML_NONE, MML_RU, MML_WRM_RU, MML_WRU, MML_XU,
                                                   MML_XRU, MML_WRM_WRU, MML_XWRU, MML_L, MML_RM,
                                                   MML_WRM, MML_RM_RU} &&
               binsof(cp_priv_lvl_iside) intersect {PRIV_LVL_M} &&
               binsof(cp_req_type_iside) intersect {PMP_ACC_EXEC} &&
               binsof(pmp_iside_req_err) intersect {0});
            illegal_bins illegal_user_allow_exec =
              // Ensuring MML is high and we are not in a X allowed configuration in User Mode
              (binsof(cp_region_priv_bits) intersect {MML_NONE, MML_RU, MML_WRM_RU, MML_WRU,
                                                      MML_WRM_WRU, MML_L, MML_RM, MML_WRM,
                                                      MML_XM, MML_XRM, MML_RM_RU} &&
               binsof(cp_priv_lvl_iside) intersect {PRIV_LVL_U} &&
               binsof(cp_req_type_iside) intersect {PMP_ACC_EXEC} &&
               binsof(pmp_iside_req_err) intersect {0});
            // Will never see an exec access denied when executed is allowed
            illegal_bins illegal_deny_exec =
              // Ensuring MML is low and we are in a X allowed configuration
              (binsof(cp_req_type_iside) intersect {PMP_ACC_EXEC} &&
               binsof(cp_region_priv_bits) intersect {X, XW, XR, XWR, LX, LXW, LXR, LXWR} &&
               binsof(pmp_iside_req_err) intersect {1});
            illegal_bins illegal_machine_deny_exec =
              // Ensuring MML is high and we are in a X allowed configuration in Machine Mode
              (binsof(cp_region_priv_bits) intersect {NONE, MML_XM_XU, MML_XRM_XU, MML_XRM,
                                                      MML_XM} &&
               binsof(cp_priv_lvl_iside) intersect {PRIV_LVL_M} &&
               binsof(cp_req_type_iside) intersect {PMP_ACC_EXEC} &&
               binsof(pmp_iside_req_err) intersect {1});
            illegal_bins illegal_user_deny_exec =
              // Ensuring MML is high and we are in a X allowed configuration in User Mode
              (binsof(cp_region_priv_bits) intersect {MML_XM_XU, MML_XRM_XU, MML_XRU, MML_XU,
                                                      MML_XWRU} &&
               binsof(cp_priv_lvl_iside) intersect {PRIV_LVL_U} &&
               binsof(cp_req_type_iside) intersect {PMP_ACC_EXEC} &&
               binsof(pmp_iside_req_err) intersect {1});
        }

        pmp_iside2_priv_bits_cross :
          cross cp_region_priv_bits, cp_req_type_iside2, cp_priv_lvl_iside2, pmp_iside2_req_err
            iff (g_pmp_fcov_signals.g_pmp_region_fcov[i_region].fcov_pmp_region_ichan2_access &&
                 g_pmp_fcov_signals.fcov_pmp_region_ichan2_priority[i_region]                 &&
                 csr_pmp_cfg[i_region].mode != PMP_MODE_OFF) {

          // Will never see a succesful exec access when execute is disallowed
          illegal_bins illegal_allow_exec =
            // Ensuring MML is low and we are not in a X allowed configuration
            (binsof(cp_region_priv_bits) intersect {NONE, R, W, WR, L, LR, LW, LWR} &&
             binsof(cp_req_type_iside2) intersect {PMP_ACC_EXEC} &&
             binsof(pmp_iside2_req_err) intersect {0}) with (cp_priv_lvl_iside2 == PRIV_LVL_U ||
                                                             (cp_region_priv_bits & 5'b01000));
          illegal_bins illegal_machine_allow_exec =
            // Ensuring MML is high and we are not in a X allowed configuration in Machine Mode
            (binsof(cp_region_priv_bits) intersect {MML_NONE, MML_RU, MML_WRM_RU, MML_WRU, MML_XU,
                                                 MML_XRU, MML_WRM_WRU, MML_XWRU, MML_L, MML_RM,
                                                 MML_WRM, MML_RM_RU} &&
             binsof(cp_priv_lvl_iside2) intersect {PRIV_LVL_M} &&
             binsof(cp_req_type_iside2) intersect {PMP_ACC_EXEC} &&
             binsof(pmp_iside2_req_err) intersect {0});
          illegal_bins illegal_user_allow_exec =
            // Ensuring MML is high and we are not in a X allowed configuration in User Mode
            (binsof(cp_region_priv_bits) intersect {MML_NONE, MML_RU, MML_WRM_RU, MML_WRU,
                                                    MML_WRM_WRU, MML_L, MML_RM, MML_WRM,
                                                    MML_XM, MML_XRM, MML_RM_RU} &&
             binsof(cp_priv_lvl_iside2) intersect {PRIV_LVL_U} &&
             binsof(cp_req_type_iside2) intersect {PMP_ACC_EXEC} &&
             binsof(pmp_iside2_req_err) intersect {0});

          // Will never see an exec access denied when execute is allowed
          illegal_bins illegal_deny_exec =
            // Ensuring MML is low and we are in a X allowed configuration
            (binsof(cp_region_priv_bits) intersect {X, XW, XR, XWR, LX, LXW, LXR, LXWR} &&
             binsof(cp_req_type_iside2) intersect {PMP_ACC_EXEC} &&
             binsof(pmp_iside2_req_err) intersect {1});
          illegal_bins illegal_machine_deny_exec =
            // Ensuring MML is high and we are in a X allowed configuration in Machine Mode
            (binsof(cp_region_priv_bits) intersect {NONE, MML_XM_XU, MML_XRM_XU, MML_XRM, MML_XM} &&
             binsof(cp_priv_lvl_iside2) intersect {PRIV_LVL_M} &&
             binsof(cp_req_type_iside2) intersect {PMP_ACC_EXEC} &&
             binsof(pmp_iside2_req_err) intersect {1});
          illegal_bins illegal_user_deny_exec =
            // Ensuring MML is high and we are in a X allowed configuration in User Mode
            (binsof(cp_region_priv_bits) intersect {MML_XM_XU, MML_XRM_XU, MML_XRU, MML_XU,
                                                      MML_XWRU} &&
             binsof(cp_priv_lvl_iside2) intersect {PRIV_LVL_U} &&
             binsof(cp_req_type_iside2) intersect {PMP_ACC_EXEC} &&
             binsof(pmp_iside2_req_err) intersect {1});
        }

        pmp_dside_priv_bits_cross :
          cross cp_region_priv_bits, cp_req_type_dside, cp_priv_lvl_dside, pmp_dside_req_err
            iff (g_pmp_fcov_signals.g_pmp_region_fcov[i_region].fcov_pmp_region_dchan_access &&
                 g_pmp_fcov_signals.fcov_pmp_region_dchan_priority[i_region]                 &&
                 csr_pmp_cfg[i_region].mode != PMP_MODE_OFF) {

          // Will never see a succesful read access when read is disallowed
          illegal_bins illegal_allow_read =
            // Ensuring MML is low and we are not in a R allowed configuration
            (binsof(cp_region_priv_bits) intersect {NONE, W, X, XW, L, LW, LX, LXW} &&
             binsof(cp_req_type_dside) intersect {PMP_ACC_READ} &&
             binsof(pmp_dside_req_err) intersect {0})
            with (cp_priv_lvl_dside == PRIV_LVL_U || (cp_region_priv_bits & 5'b01000));
          illegal_bins illegal_machine_allow_read =
            // Ensuring MML is high and we are not in a R allowed configuration in Machine Mode
            (binsof(cp_region_priv_bits) intersect {MML_NONE, MML_RU, MML_WRU, MML_XU, MML_XRU,
                                                    MML_XWRU, MML_L, MML_XM_XU, MML_XM} &&
             binsof(cp_priv_lvl_dside) intersect {PRIV_LVL_M} &&
             binsof(cp_req_type_dside) intersect {PMP_ACC_READ} &&
             binsof(pmp_dside_req_err) intersect {0});
          illegal_bins illegal_user_allow_read =
            // Ensuring MML is high and we are not in a R allowed configuration in User Mode
            (binsof(cp_region_priv_bits) intersect {MML_NONE, MML_XU, MML_L, MML_RM, MML_XM_XU,
                                                    MML_WRM, MML_XM, MML_XRM, MML_XRM_XU} &&
             binsof(cp_priv_lvl_dside) intersect {PRIV_LVL_U} &&
             binsof(cp_req_type_dside) intersect {PMP_ACC_READ} &&
             binsof(pmp_dside_req_err) intersect {0});

          // Will never see a read access denied when read is allowed
          illegal_bins illegal_deny_read =
            // Ensuring MML is low and we are in a R allowed configuration
            (binsof(cp_region_priv_bits) intersect {R, WR, XR, XWR, LR, LWR, LXR, LXWR} &&
             binsof(cp_req_type_dside) intersect {PMP_ACC_READ} &&
             binsof(pmp_dside_req_err) intersect {1});
          illegal_bins illegal_machine_deny_read =
            // Ensuring MML is high and we are in a R allowed configuration in Machine Mode
            (binsof(cp_region_priv_bits) intersect {MML_WRM_RU, MML_WRM_WRU, MML_RM_RU, MML_RM,
                                                    MML_WRM, MML_XRM, MML_XRM_XU, NONE} &&
             binsof(cp_priv_lvl_dside) intersect {PRIV_LVL_M} &&
             binsof(cp_req_type_dside) intersect {PMP_ACC_READ} &&
             binsof(pmp_dside_req_err) intersect {1});
          illegal_bins illegal_user_deny_read =
            // Ensuring MML is high and we are not in a R allowed configuration in User Mode
            (binsof(cp_region_priv_bits) intersect {MML_WRM_RU, MML_WRM_WRU, MML_RM_RU, MML_RU,
                                                    MML_WRU, MML_XRU, MML_XWRU} &&
             binsof(cp_priv_lvl_dside) intersect {PRIV_LVL_U} &&
             binsof(cp_req_type_dside) intersect {PMP_ACC_READ} &&
             binsof(pmp_dside_req_err) intersect {1});

          // Will never see a succesful write access when write is disallowed
          illegal_bins illegal_allow_write =
            // Ensuring MML is low and we are not in a W allowed configuration
            (binsof(cp_region_priv_bits) intersect {NONE, R, X, XR, L, LR, LX, LXR} &&
             binsof(cp_req_type_dside) intersect {PMP_ACC_WRITE} &&
             binsof(pmp_dside_req_err) intersect {0})
            with (cp_priv_lvl_dside == PRIV_LVL_U || (cp_region_priv_bits & 5'b01000));
          illegal_bins illegal_machine_allow_write =
            // Ensuring MML is high and we are not in a W allowed configuration in Machine Mode
            (binsof(cp_region_priv_bits) intersect {MML_NONE, MML_RU, MML_WRU, MML_XU, MML_XRU,
                                                    MML_XWRU, MML_L, MML_RM, MML_XM_XU, MML_XM,
                                                    MML_XRM, MML_XRM_XU, MML_RM_RU} &&
             binsof(cp_priv_lvl_dside) intersect {PRIV_LVL_M} &&
             binsof(cp_req_type_dside) intersect {PMP_ACC_WRITE} &&
             binsof(pmp_dside_req_err) intersect {0});
          illegal_bins illegal_user_allow_write =
            // Ensuring MML is high and we are not in a W allowed configuration in User Mode
            (binsof(cp_region_priv_bits) intersect {MML_NONE, MML_RU, MML_WRM_RU, MML_XU, MML_XRU,
                                                    MML_L, MML_RM, MML_XM_XU, MML_WRM, MML_XM,
                                                    MML_XRM, MML_XRM_XU, MML_RM_RU} &&
             binsof(cp_priv_lvl_dside) intersect {PRIV_LVL_U} &&
             binsof(cp_req_type_dside) intersect {PMP_ACC_WRITE} &&
             binsof(pmp_dside_req_err) intersect {0});

          // Will never see a write access denied when write is allowed
          illegal_bins illegal_deny_write =
            // Ensuring MML is low and we are in a W allowed configuration
            (binsof(cp_region_priv_bits) intersect {W, WR, XW, XWR, LW, LWR, LXW, LXWR} &&
             binsof(cp_req_type_dside) intersect {PMP_ACC_WRITE} &&
             binsof(pmp_dside_req_err) intersect {1});
          illegal_bins illegal_machine_deny_write =
            // Ensuring MML is high and we are in a W allowed configuration in Machine Mode
            (binsof(cp_region_priv_bits) intersect {MML_WRM_WRU, MML_WRM_RU, MML_WRM, NONE} &&
             binsof(cp_priv_lvl_dside) intersect {PRIV_LVL_M} &&
             binsof(cp_req_type_dside) intersect {PMP_ACC_WRITE} &&
             binsof(pmp_dside_req_err) intersect {1});
            // Ensuring MML is high and we are in a W allowed configuration in User Mode
          illegal_bins illegal_user_deny_write =
            (binsof(cp_region_priv_bits) intersect {MML_WRM_WRU, MML_WRU, MML_XWRU} &&
             binsof(cp_priv_lvl_dside) intersect {PRIV_LVL_U} &&
             binsof(cp_req_type_dside) intersect {PMP_ACC_WRITE} &&
             binsof(pmp_dside_req_err) intersect {1});
        }

        `DV_FCOV_EXPR_SEEN(edit_locked_pmpcfg,
          fcov_csr_write &&
          csr_pmp_cfg[i_region].lock &&
          cs_registers_i.g_pmp_registers.g_pmp_csrs[i_region].u_pmp_cfg_csr.wr_en_i &&
          csr_pmp_mseccfg.rlb)

        `DV_FCOV_EXPR_SEEN(edit_locked_pmpaddr,
          fcov_csr_write &&
          csr_pmp_cfg[i_region].lock &&
          cs_registers_i.g_pmp_registers.g_pmp_csrs[i_region].u_pmp_addr_csr.wr_en_i &&
          csr_pmp_mseccfg.rlb)

        // Only sample this cross when we attempt to write to a PMP config that doesn't currently
        // allow execution with MML enabled
        pmp_wr_exec_region :
          cross pmp_region_priv_bits, pmp_region_priv_bits_wr, csr_pmp_mseccfg.rlb iff
            (fcov_csr_write &&
             csr_pmp_mseccfg.mml &&
             cs_registers_i.csr_we_int &&
             cs_registers_i.csr_addr == (CSR_OFF_PMP_CFG + (i_region[11:0] >> 2)) &&
             ((!pmp_region_priv_bits[2] && pmp_region_priv_bits != MML_XM_XU) ||
              pmp_region_priv_bits inside {MML_WRM_WRU, MML_RM_RU})) {

          // Only interested in MML configuration
          ignore_bins non_mml_in = binsof(pmp_region_priv_bits) with (!pmp_region_priv_bits[4]);

          ignore_bins non_mml_out =
            binsof(pmp_region_priv_bits_wr) with (!pmp_region_priv_bits_wr[4]);

          // Only interested in starting configs that weren't executable so ignore executable
          // regions
          ignore_bins from_exec_bins = binsof(pmp_region_priv_bits) intersect {MML_XU, MML_XRU,
            MML_XWRU, MML_XM_XU, MML_XM, MML_XRM, MML_XRM_XU};

          // Only interested in writes that give executable regions so ignore non executable regions
          ignore_bins to_non_exec_bins = binsof(pmp_region_priv_bits_wr) intersect {MML_NONE,
            MML_RU, MML_WRM_RU, MML_WRU, MML_WRM_WRU, MML_L, MML_RM, MML_WRM, MML_RM_RU};
        }
      endgroup

      `DV_FCOV_INSTANTIATE_CG(pmp_region_cg, en_pmp_fcov)
    end

    // Current Priv means the privilege level of Instruction channels and Ibex in general. Note that
    // the privilege level of PMP data channel can be set something different than this using MSTATUS.MPRV
    // and MSTATUS.MPP.
    logic pmp_current_priv_req_err;
    assign pmp_current_priv_req_err =
      g_pmp.pmp_i.access_fault_check(csr_pmp_mseccfg.mmwp,
                                     csr_pmp_mseccfg.mml,
                                     g_pmp.pmp_i.pmp_req_type_i[PMP_D],
                                     g_pmp.pmp_i.region_match_all[PMP_D],
                                     cs_registers_i.priv_mode_id_o,
                                     current_priv_perm_check);

    covergroup pmp_top_cg @(posedge clk_i);
      option.per_instance = 1;
      option.name = "pmp_top_cg";

      cp_rlb : coverpoint csr_pmp_mseccfg.rlb{
        bins on  = {1'b1};
        bins off = {1'b0};
      }

      cp_mmwp : coverpoint csr_pmp_mseccfg.mmwp{
        bins on  = {1'b1};
        bins off = {1'b0};
      }

      cp_mml : coverpoint csr_pmp_mseccfg.mml{
        bins on  = {1'b1};
        bins off = {1'b0};
      }

      cp_wdata_rlb: coverpoint csr_wdata_mseccfg_rlb{
        bins on  = {1'b1};
        bins off = {1'b0};
      }

      cp_wdata_mmwp: coverpoint csr_wdata_mseccfg_mmwp{
        bins on  = {1'b1};
        bins off = {1'b0};
      }

      cp_wdata_mml: coverpoint csr_wdata_mseccfg_mml{
        bins on  = {1'b1};
        bins off = {1'b0};
      }

      //////// Redundant coverpoints for nomatch crosses ///////////
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
      //////////////////////////////////////////////////////////////

      rlb_csr_cross : cross cp_rlb, cp_wdata_rlb
        iff (fcov_csr_write && cs_registers_i.csr_addr_i == CSR_MSECCFG) {
          // Trying to enable RLB when RLB is disabled and locked regions present will result
          // with an ignored write
          bins sticky = binsof(cp_rlb) intersect {0} && binsof(cp_wdata_rlb) intersect {1}
            iff (cs_registers_i.g_pmp_registers.any_pmp_entry_locked);
      }

      mmwp_csr_cross : cross cp_mmwp, cp_wdata_mmwp
        iff (fcov_csr_write && cs_registers_i.csr_addr_i == CSR_MSECCFG) {
          bins sticky = binsof(cp_wdata_mmwp) intersect {0} && binsof(cp_mmwp) intersect {1};
      }

      mml_sticky_cross : cross cp_mml, cp_wdata_mml
        iff (fcov_csr_write && cs_registers_i.csr_addr_i == CSR_MSECCFG) {
          bins sticky = binsof(cp_wdata_mml) intersect {0} && binsof(cp_mml) intersect {1};
      }

      pmp_iside_nomatch_cross :
        cross cp_req_type_iside, cp_priv_lvl_iside, pmp_iside_req_err, cp_mmwp, cp_mml
          iff (pmp_iside_nomatch) {
          // Will never see a succesful exec access when execute is disallowed
          illegal_bins illegal_user_allow_exec =
            // In User mode - no match case, we should always deny
            (binsof(cp_priv_lvl_iside) intersect {PRIV_LVL_U} &&
             binsof(cp_req_type_iside) intersect {PMP_ACC_EXEC} &&
             binsof(pmp_iside_req_err) intersect {0});
          illegal_bins illegal_machine_allow_exec =
            // In Machine mode - no match case, we should deny always except MML=0 & MMWP=0
            (binsof(cp_priv_lvl_iside) intersect {PRIV_LVL_M} &&
             binsof(cp_req_type_iside) intersect {PMP_ACC_EXEC} &&
             (binsof(cp_mmwp) intersect {1} ||
              binsof(cp_mml) intersect {1}) &&
             binsof(pmp_iside_req_err) intersect {0});
          // Will never see an exec access denied when executed is ignored
          illegal_bins illegal_deny_exec =
            // Ignore Exec in MML=0, MMWP=0 and in Machine mode
            (binsof(cp_priv_lvl_iside) intersect {PRIV_LVL_M} &&
             binsof(cp_req_type_iside) intersect {PMP_ACC_EXEC} &&
             binsof(cp_mmwp) intersect {0} &&
             binsof(cp_mml) intersect {0} &&
             binsof(pmp_iside_req_err) intersect {1});
      }

      pmp_iside2_nomatch_cross :
        cross cp_req_type_iside2, cp_priv_lvl_iside2, pmp_iside2_req_err, cp_mmwp, cp_mml
          iff (pmp_iside2_nomatch) {
          // Will never see a succesful exec access when execute is disallowed
          illegal_bins illegal_user_allow_exec =
            // In User mode - no match case, we should always deny
            (binsof(cp_priv_lvl_iside2) intersect {PRIV_LVL_U} &&
             binsof(cp_req_type_iside2) intersect {PMP_ACC_EXEC} &&
             binsof(pmp_iside2_req_err) intersect {0});
          illegal_bins illegal_machine_allow_exec =
            // In Machine mode - no match case, we should deny always except MML=0 & MMWP=0
            (binsof(cp_priv_lvl_iside2) intersect {PRIV_LVL_M} &&
             binsof(cp_req_type_iside2) intersect {PMP_ACC_EXEC} &&
             (binsof(cp_mmwp) intersect {1} ||
              binsof(cp_mml) intersect {1}) &&
             binsof(pmp_iside2_req_err) intersect {0});
          // Will never see an exec access denied when executed is ignored
          illegal_bins illegal_deny_exec =
            // Ignore Exec in MML=0, MMWP=0 and in Machine mode
            (binsof(cp_priv_lvl_iside2) intersect {PRIV_LVL_M} &&
             binsof(cp_req_type_iside2) intersect {PMP_ACC_EXEC} &&
             binsof(cp_mmwp) intersect {0} &&
             binsof(cp_mml) intersect {0} &&
             binsof(pmp_iside2_req_err) intersect {1});
      }

      pmp_dside_nomatch_cross :
        cross cp_req_type_dside, cp_priv_lvl_dside, pmp_dside_req_err, cp_mmwp, cp_mml
          iff (pmp_dside_nomatch) {

          // Will never see a succesful write/read access when it should be denied
          illegal_bins illegal_machine_allow_wr =
            // Deny WR when MMWP = 1 in Machine mode
            (binsof(cp_priv_lvl_dside) intersect {PRIV_LVL_M} &&
             binsof(cp_req_type_dside) intersect {PMP_ACC_READ, PMP_ACC_WRITE} &&
             binsof(cp_mmwp) intersect {1} &&
             binsof(pmp_dside_req_err) intersect {0});
          illegal_bins illegal_user_allow_wr =
            // Deny WR everytime in User mode
            (binsof(cp_priv_lvl_dside) intersect {PRIV_LVL_U} &&
             binsof(cp_req_type_dside) intersect {PMP_ACC_READ, PMP_ACC_WRITE} &&
             binsof(pmp_dside_req_err) intersect {0});

          // Will never see a write/read access denied when write/read is ignored
          illegal_bins illegal_deny_wr =
            // Ignore WR when MMWP = 0 in Machine mode
            (binsof(cp_priv_lvl_dside) intersect {PRIV_LVL_M} &&
             binsof(cp_req_type_dside) intersect {PMP_ACC_READ, PMP_ACC_WRITE} &&
             binsof(cp_mmwp) intersect {0} &&
             binsof(pmp_dside_req_err) intersect {1});
      }

      cp_pmp_iside_region_override :
        coverpoint g_pmp.pmp_i.g_access_check[PMP_I].fcov_pmp_region_override
          iff (if_stage_i.if_id_pipe_reg_we);

      cp_pmp_iside2_region_override :
        coverpoint g_pmp.pmp_i.g_access_check[PMP_I2].fcov_pmp_region_override
          iff (if_stage_i.if_id_pipe_reg_we);

      cp_pmp_dside_region_override :
        coverpoint g_pmp.pmp_i.g_access_check[PMP_D].fcov_pmp_region_override iff (data_req_out);

      cp_mprv: coverpoint cs_registers_i.mstatus_q.mprv;

      mprv_effect_cross: cross cs_registers_i.mstatus_q.mpp,
                               cs_registers_i.priv_mode_id_o, pmp_current_priv_req_err,
                               pmp_dside_req_err iff
                                 (id_stage_i.instr_rdata_i[6:0] inside
                                    {ibex_pkg::OPCODE_LOAD, ibex_pkg::OPCODE_STORE} &&
                                  cs_registers_i.mstatus_q.mprv){
        ignore_bins SamePriv =
          (binsof(cs_registers_i.mstatus_q.mpp) intersect {PRIV_LVL_M} &&
           binsof(cs_registers_i.priv_mode_id_o) intersect {PRIV_LVL_M}) ||
          (binsof(cs_registers_i.mstatus_q.mpp) intersect {PRIV_LVL_U} &&
           binsof(cs_registers_i.priv_mode_id_o) intersect {PRIV_LVL_U});

        ignore_bins SameErr =
          (binsof(pmp_current_priv_req_err) intersect {0} &&
           binsof(pmp_dside_req_err) intersect {0}) ||
          (binsof(pmp_current_priv_req_err) intersect {1} &&
           binsof(pmp_dside_req_err) intersect {1});

        // Ibex does not support H or S mode.
        ignore_bins unsupported_priv_lvl =
          binsof(cs_registers_i.mstatus_q.mpp) intersect {PRIV_LVL_H, PRIV_LVL_S} ||
          binsof(cs_registers_i.priv_mode_id_o) intersect {PRIV_LVL_H, PRIV_LVL_S};

        // Cannot have mprv set in U mode (as it is cleared when executing an `mret` which takes the
        // hart into U mode).
        illegal_bins no_mrpv_in_umode =
          binsof(cs_registers_i.priv_mode_id_o) intersect {PRIV_LVL_U};
      }

      pmp_instr_edge_cross: cross if_stage_i.instr_is_compressed_out,
                                  pmp_iside_req_err, pmp_iside2_req_err
                              iff (pmp_iside_boundary_cross) {
        // Compressed instruction cannot see an error over the boundary as it only ever does
        // a single 16-bit fetch.
        illegal_bins no_iside2_err_on_compressed =
          binsof(if_stage_i.instr_is_compressed_out) intersect {1'b1} &&
          binsof(pmp_iside2_req_err) intersect {1'b1};
      }

      misaligned_lsu_access_cross: cross misaligned_pmp_err_last,
                                         load_store_unit_i.fcov_ls_mis_pmp_err_2
                                   iff (pmp_dside_boundary_cross);
    endgroup

    `DV_FCOV_INSTANTIATE_CG(pmp_top_cg, en_pmp_fcov)
  end

endinterface
