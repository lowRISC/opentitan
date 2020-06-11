// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module ibex_pmp #(
    // Granularity of NAPOT access,
    // 0 = No restriction, 1 = 8 byte, 2 = 16 byte, 3 = 32 byte, etc.
    parameter int unsigned PMPGranularity = 0,
    // Number of access channels (e.g. i-side + d-side)
    parameter int unsigned PMPNumChan     = 2,
    // Number of implemented regions
    parameter int unsigned PMPNumRegions  = 4
) (
    // Clock and Reset
    input  logic                    clk_i,
    input  logic                    rst_ni,

    // Interface to CSRs
    input  ibex_pkg::pmp_cfg_t      csr_pmp_cfg_i  [PMPNumRegions],
    input  logic [33:0]             csr_pmp_addr_i [PMPNumRegions],

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
  logic [PMPNumChan-1:0][PMPNumRegions-1:0]   region_perm_check;
  logic [PMPNumChan-1:0]                      access_fault;


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
    for (genvar b = PMPGranularity+2; b < 34; b++) begin : g_bitmask
      if (b == PMPGranularity+2) begin : g_bit0
        // Always mask bit (G+2) for NAPOT
        assign region_addr_mask[r][b] = (csr_pmp_cfg_i[r].mode != PMP_MODE_NAPOT);
      end else begin : g_others
        // We will mask this bit if it is within the programmed granule
        // i.e. addr = yyyy 0111
        //                  ^
        //                  | This bit pos is the top of the mask, all lower bits set
        // thus mask = 1111 0000
        assign region_addr_mask[r][b] = (csr_pmp_cfg_i[r].mode != PMP_MODE_NAPOT) |
                                        ~&csr_pmp_addr_i[r][b-1:PMPGranularity+2];
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
          PMP_MODE_OFF   : region_match_all[c][r] = 1'b0;
          PMP_MODE_NA4   : region_match_all[c][r] = region_match_eq[c][r];
          PMP_MODE_NAPOT : region_match_all[c][r] = region_match_eq[c][r];
          PMP_MODE_TOR   : begin
            region_match_all[c][r] = (region_match_eq[c][r] | region_match_gt[c][r]) &
                                     region_match_lt[c][r];
          end
          default        : region_match_all[c][r] = 1'b0;
        endcase
      end

      // Check specific required permissions
      assign region_perm_check[c][r] =
          ((pmp_req_type_i[c] == PMP_ACC_EXEC)  & csr_pmp_cfg_i[r].exec) |
          ((pmp_req_type_i[c] == PMP_ACC_WRITE) & csr_pmp_cfg_i[r].write) |
          ((pmp_req_type_i[c] == PMP_ACC_READ)  & csr_pmp_cfg_i[r].read);
    end

    // Access fault determination / prioritization
    always_comb begin
      // Default is allow for M-mode, deny for other modes
      access_fault[c] = (priv_mode_i[c] != PRIV_LVL_M);

      // PMP entries are statically prioritized, from 0 to N-1
      // The lowest-numbered PMP entry which matches an address determines accessability
      for (int r = PMPNumRegions-1; r >= 0; r--) begin
        if (region_match_all[c][r]) begin
          access_fault[c] = (priv_mode_i[c] == PRIV_LVL_M) ?
              // For M-mode, any region which matches with the L-bit clear, or with sufficient
              // access permissions will be allowed
              (csr_pmp_cfg_i[r].lock & ~region_perm_check[c][r]) :
              // For other modes, the lock bit doesn't matter
              ~region_perm_check[c][r];
        end
      end
    end

    assign pmp_req_err_o[c] = access_fault[c];
  end

endmodule
