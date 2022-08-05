// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "dv_fcov_macros.svh"

module ibex_pmp #(
  // Granularity of NAPOT access,
  // 0 = No restriction, 1 = 8 byte, 2 = 16 byte, 3 = 32 byte, etc.
  parameter int unsigned PMPGranularity = 0,
  // Number of access channels (e.g. i-side + d-side)
  parameter int unsigned PMPNumChan     = 2,
  // Number of implemented regions
  parameter int unsigned PMPNumRegions  = 4
) (
  // Interface to CSRs
  input  ibex_pkg::pmp_cfg_t      csr_pmp_cfg_i     [PMPNumRegions],
  input  logic [33:0]             csr_pmp_addr_i    [PMPNumRegions],
  input  ibex_pkg::pmp_mseccfg_t  csr_pmp_mseccfg_i,

  input  ibex_pkg::priv_lvl_e     priv_mode_i    [PMPNumChan],
  // Access checking channels
  input  logic [33:0]             pmp_req_addr_i [PMPNumChan],
  input  ibex_pkg::pmp_req_e      pmp_req_type_i [PMPNumChan],
  output logic                    pmp_req_err_o  [PMPNumChan]

);

  import ibex_pkg::*;

  // Access Checking Signals
  logic [33:0]                                region_start_addr [PMPNumRegions];
  logic [33:PMPGranularity+2]                 region_addr_mask  [PMPNumRegions];
  logic [PMPNumChan-1:0][PMPNumRegions-1:0]   region_match_gt;
  logic [PMPNumChan-1:0][PMPNumRegions-1:0]   region_match_lt;
  logic [PMPNumChan-1:0][PMPNumRegions-1:0]   region_match_eq;
  logic [PMPNumChan-1:0][PMPNumRegions-1:0]   region_match_all;
  logic [PMPNumChan-1:0][PMPNumRegions-1:0]   region_basic_perm_check;
  logic [PMPNumChan-1:0][PMPNumRegions-1:0]   region_perm_check;

  ///////////////////////
  // Functions for PMP //
  ///////////////////////

  // Flow of the PMP checking operation follows as below
  //
  // basic_perm_check ---> perm_check_wrapper ---> mml_perm_check/orig_perm_check ---/
  //                                                                                 |
  // region_match_all --------------------------------> access_fault_check <----------
  //                                                            |
  //                                                            \--> pmp_req_err_o

  // A wrapper function in which it is decided which form of permission check function gets called
  function automatic logic perm_check_wrapper(logic                csr_pmp_mseccfg_mml,
                                              ibex_pkg::pmp_cfg_t  csr_pmp_cfg,
                                              ibex_pkg::pmp_req_e  pmp_req_type,
                                              ibex_pkg::priv_lvl_e priv_mode,
                                              logic                permission_check);
    if (csr_pmp_mseccfg_mml) begin
      return mml_perm_check(csr_pmp_cfg,
                            pmp_req_type,
                            priv_mode,
                            permission_check);
    end else begin
      return orig_perm_check(csr_pmp_cfg.lock,
                             priv_mode,
                             permission_check);
    end
  endfunction

  // Compute permissions checks that apply when MSECCFG.MML is set. Added for Smepmp support.
  function automatic logic mml_perm_check(ibex_pkg::pmp_cfg_t  csr_pmp_cfg,
                                          ibex_pkg::pmp_req_e  pmp_req_type,
                                          ibex_pkg::priv_lvl_e priv_mode,
                                          logic                permission_check);
    logic result = 1'b0;
    logic unused_cfg = |csr_pmp_cfg.mode;

    if (!csr_pmp_cfg.read && csr_pmp_cfg.write) begin
      // Special-case shared regions where R = 0, W = 1
      unique case ({csr_pmp_cfg.lock, csr_pmp_cfg.exec})
        // Read/write in M, read only in S/U
        2'b00: result =
            (pmp_req_type == PMP_ACC_READ) |
            ((pmp_req_type == PMP_ACC_WRITE) & (priv_mode == PRIV_LVL_M));
        // Read/write in M/S/U
        2'b01: result =
            (pmp_req_type == PMP_ACC_READ) | (pmp_req_type == PMP_ACC_WRITE);
        // Execute only on M/S/U
        2'b10: result = (pmp_req_type == PMP_ACC_EXEC);
        // Read/execute in M, execute only on S/U
        2'b11: result =
            (pmp_req_type == PMP_ACC_EXEC) |
            ((pmp_req_type == PMP_ACC_READ) & (priv_mode == PRIV_LVL_M));
        default: ;
      endcase
    end else begin
      if (csr_pmp_cfg.read & csr_pmp_cfg.write & csr_pmp_cfg.exec & csr_pmp_cfg.lock) begin
        // Special-case shared read only region when R = 1, W = 1, X = 1, L = 1
        result = pmp_req_type == PMP_ACC_READ;
      end else begin
        // Otherwise use basic permission check. Permission is always denied if in S/U mode and
        // L is set or if in M mode and L is unset.
        result = permission_check &
                 (priv_mode == PRIV_LVL_M ? csr_pmp_cfg.lock : ~csr_pmp_cfg.lock);
      end
    end
    return result;
  endfunction

  // Compute permissions checks that apply when MSECCFG.MML is unset. This is the original PMP
  // behaviour before Smepmp was added.
  function automatic logic orig_perm_check(logic                pmp_cfg_lock,
                                           ibex_pkg::priv_lvl_e priv_mode,
                                           logic                permission_check);
      return (priv_mode == PRIV_LVL_M) ?
          // For M-mode, any region which matches with the L-bit clear, or with sufficient
          // access permissions will be allowed
          (~pmp_cfg_lock | permission_check) :
          // For other modes, the lock bit doesn't matter
          permission_check;
  endfunction

  // Access fault determination / prioritization
  function automatic logic access_fault_check (logic                     csr_pmp_mseccfg_mmwp,
                                               logic                     csr_pmp_mseccfg_mml,
                                               ibex_pkg::pmp_req_e       pmp_req_type,
                                               logic [PMPNumRegions-1:0] match_all,
                                               ibex_pkg::priv_lvl_e      priv_mode,
                                               logic [PMPNumRegions-1:0] final_perm_check);


    // When MSECCFG.MMWP is set default deny always, otherwise allow for M-mode, deny for other
    // modes. Also deny unmatched for M-mode whe MSECCFG.MML is set and request type is EXEC.
    logic access_fail = csr_pmp_mseccfg_mmwp | (priv_mode != PRIV_LVL_M) |
                        (csr_pmp_mseccfg_mml && (pmp_req_type == PMP_ACC_EXEC));

    // PMP entries are statically prioritized, from 0 to N-1
    // The lowest-numbered PMP entry which matches an address determines accessibility
    for (int r = 0; r < PMPNumRegions; r++) begin
      if (match_all[r]) begin
        access_fail = ~final_perm_check[r];
        break;
      end
    end
    return access_fail;
  endfunction

  // ---------------
  // Access checking
  // ---------------

  for (genvar r = 0; r < PMPNumRegions; r++) begin : g_addr_exp
    // Start address for TOR matching
    if (r == 0) begin : g_entry0
      assign region_start_addr[r] = (csr_pmp_cfg_i[r].mode == PMP_MODE_TOR) ? 34'h000000000 :
                                                                              csr_pmp_addr_i[r];
    end else begin : g_oth
      assign region_start_addr[r] = (csr_pmp_cfg_i[r].mode == PMP_MODE_TOR) ? csr_pmp_addr_i[r-1] :
                                                                              csr_pmp_addr_i[r];
    end
    // Address mask for NA matching
    for (genvar b = PMPGranularity + 2; b < 34; b++) begin : g_bitmask
      if (b == 2) begin : g_bit0
        // Always mask bit 2 for NAPOT
        assign region_addr_mask[r][b] = (csr_pmp_cfg_i[r].mode != PMP_MODE_NAPOT);
      end else begin : g_others
        // We will mask this bit if it is within the programmed granule
        // i.e. addr = yyyy 0111
        //                  ^
        //                  | This bit pos is the top of the mask, all lower bits set
        // thus mask = 1111 0000
        if (PMPGranularity == 0) begin : g_region_addr_mask_zero_granularity
          assign region_addr_mask[r][b] = (csr_pmp_cfg_i[r].mode != PMP_MODE_NAPOT) |
                                          ~&csr_pmp_addr_i[r][b-1:2];
        end else begin : g_region_addr_mask_other_granularity
          assign region_addr_mask[r][b] = (csr_pmp_cfg_i[r].mode != PMP_MODE_NAPOT) |
                                          ~&csr_pmp_addr_i[r][b-1:PMPGranularity+1];
        end
      end
    end
  end

  for (genvar c = 0; c < PMPNumChan; c++) begin : g_access_check
    for (genvar r = 0; r < PMPNumRegions; r++) begin : g_regions
      // Comparators are sized according to granularity
      assign region_match_eq[c][r] = (pmp_req_addr_i[c][33:PMPGranularity+2] &
                                      region_addr_mask[r]) ==
                                     (region_start_addr[r][33:PMPGranularity+2] &
                                      region_addr_mask[r]);
      assign region_match_gt[c][r] = pmp_req_addr_i[c][33:PMPGranularity+2] >
                                     region_start_addr[r][33:PMPGranularity+2];
      assign region_match_lt[c][r] = pmp_req_addr_i[c][33:PMPGranularity+2] <
                                     csr_pmp_addr_i[r][33:PMPGranularity+2];

      always_comb begin
        region_match_all[c][r] = 1'b0;
        unique case (csr_pmp_cfg_i[r].mode)
          PMP_MODE_OFF:   region_match_all[c][r] = 1'b0;
          PMP_MODE_NA4:   region_match_all[c][r] = region_match_eq[c][r];
          PMP_MODE_NAPOT: region_match_all[c][r] = region_match_eq[c][r];
          PMP_MODE_TOR: begin
            region_match_all[c][r] = (region_match_eq[c][r] | region_match_gt[c][r]) &
                                     region_match_lt[c][r];
          end
          default:        region_match_all[c][r] = 1'b0;
        endcase
      end

      // Basic permission check compares cfg register only.
      assign region_basic_perm_check[c][r] =
          ((pmp_req_type_i[c] == PMP_ACC_EXEC)  & csr_pmp_cfg_i[r].exec) |
          ((pmp_req_type_i[c] == PMP_ACC_WRITE) & csr_pmp_cfg_i[r].write) |
          ((pmp_req_type_i[c] == PMP_ACC_READ)  & csr_pmp_cfg_i[r].read);

      // Check specific required permissions since the behaviour is different
      // between Smepmp implementation and original PMP.
      assign region_perm_check[c][r] = perm_check_wrapper(csr_pmp_mseccfg_i.mml,
                                                          csr_pmp_cfg_i[r],
                                                          pmp_req_type_i[c],
                                                          priv_mode_i[c],
                                                          region_basic_perm_check[c][r]);

      // Address bits below PMP granularity (which starts at 4 byte) are deliberately unused.
      logic unused_sigs;
      assign unused_sigs = ^{region_start_addr[r][PMPGranularity+2-1:0],
                             pmp_req_addr_i[c][PMPGranularity+2-1:0]};
    end

    // Once the permission checks of the regions are done, decide if the access is
    // denied by figuring out the matching region and its permission check.
    assign pmp_req_err_o[c] = access_fault_check(csr_pmp_mseccfg_i.mmwp,
                                                 csr_pmp_mseccfg_i.mml,
                                                 pmp_req_type_i[c],
                                                 region_match_all[c],
                                                 priv_mode_i[c],
                                                 region_perm_check[c]);

    // Access fails check against one region but access allowed due to another higher-priority
    // region.
    `DV_FCOV_SIGNAL(logic, pmp_region_override,
      ~pmp_req_err_o[c] & |(region_match_all[c] & ~region_perm_check[c]))
  end

  // RLB, rule locking bypass, is only relevant to ibex_cs_registers which controls writes to the
  // PMP CSRs. Tie to unused signal here to prevent lint warnings.
  logic unused_csr_pmp_mseccfg_rlb;
  assign unused_csr_pmp_mseccfg_rlb = csr_pmp_mseccfg_i.rlb;
endmodule
