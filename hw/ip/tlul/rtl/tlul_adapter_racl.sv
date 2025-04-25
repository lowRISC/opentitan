// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * Tile-Link UL adapter with RACL support
 *
 * - It allows filtering TLUL requests based on their range using an allow-list approach. A request
 *   is allowed if its address matches a racl range which allows access for the racl role associated
 *   with this request.
 */
module tlul_adapter_racl
  import tlul_pkg::*;
  import prim_mubi_pkg::mubi4_t;
#(
  parameter bit EnableRacl             = 0,          // 1: Enable RACL checks on access
  parameter bit RaclErrorRsp           = EnableRacl, // 1: Return TLUL error on RACL errors
  parameter int RaclPolicySelNumRanges = 1           // Number of ranges with a RACL policy
) (
  input                                                          clk_i,
  input                                                          rst_ni,
  // TL-UL interface
  input  tlul_pkg::tl_h2d_t                                      tl_h2d_i,
  output tlul_pkg::tl_d2h_t                                      tl_d2h_o,
  output tlul_pkg::tl_h2d_t                                      tl_filtered_h2d_o,
  input  tlul_pkg::tl_d2h_t                                      tl_filtered_d2h_i,
  // RACL interface
  input  top_racl_pkg::racl_policy_vec_t                         racl_policies_i,
  output top_racl_pkg::racl_error_log_t                          racl_error_o,
  input  top_racl_pkg::racl_range_t [RaclPolicySelNumRanges-1:0] racl_policy_sel_ranges_i
);
  if (EnableRacl) begin : gen_racl_role_logic
    // Retrieve RACL role from user bits and one-hot encode that for the comparison bitmap
    top_racl_pkg::racl_role_t racl_role;
    assign racl_role = top_racl_pkg::tlul_extract_racl_role_bits(tl_h2d_i.a_user.rsvd);

    top_racl_pkg::racl_role_vec_t racl_role_vec;
    prim_onehot_enc #(
      .OneHotWidth( $bits(top_racl_pkg::racl_role_vec_t) )
    ) u_racl_role_encode (
      .in_i ( racl_role     ),
      .en_i ( 1'b1          ),
      .out_o( racl_role_vec )
    );

    logic rd_req, wr_req, racl_read_allowed, racl_write_allowed, racl_error;
    logic [RaclPolicySelNumRanges-1:0] range_read_allowed;
    logic [RaclPolicySelNumRanges-1:0] range_write_allowed;

    for (genvar r = 0; r < RaclPolicySelNumRanges; r++) begin : gen_racl_range_check
      top_racl_pkg::racl_range_t range;
      top_racl_pkg::racl_policy_t policy;
      logic range_match;
      assign range = racl_policy_sel_ranges_i[r];
      assign policy = racl_policies_i[range.policy_sel];
      // Check if the address is within range
      assign range_match = range.enable
                           & tl_h2d_i.a_address >= range.base
                           & tl_h2d_i.a_address <= range.limit;
      // If address matches, lookup permissions for policy defined for this range
      assign range_read_allowed[r]  = range_match & |(policy.read_perm  & racl_role_vec);
      assign range_write_allowed[r] = range_match & |(policy.write_perm & racl_role_vec);
    end

    assign racl_read_allowed  = |range_read_allowed;
    assign racl_write_allowed = |range_write_allowed;

    assign rd_req             = tl_h2d_i.a_valid & (tl_h2d_i.a_opcode == tlul_pkg::Get);
    assign wr_req             = tl_h2d_i.a_valid & (tl_h2d_i.a_opcode == tlul_pkg::PutFullData |
                                                    tl_h2d_i.a_opcode == tlul_pkg::PutPartialData);
    assign racl_error         = (rd_req & ~racl_read_allowed) | (wr_req & ~racl_write_allowed);
    assign racl_error_o.valid = racl_error & tl_d2h_o.a_ready;

    tlul_request_loopback #(
      .ErrorRsp ( RaclErrorRsp )
    ) u_loopback (
      .clk_i        ( clk_i             ),
      .rst_ni       ( rst_ni            ),
      .squash_req_i ( racl_error        ),
      .tl_h2d_i     ( tl_h2d_i          ),
      .tl_d2h_o     ( tl_d2h_o          ),
      .tl_h2d_o     ( tl_filtered_h2d_o ),
      .tl_d2h_i     ( tl_filtered_d2h_i )
    );

    // Collect RACL error information
    assign racl_error_o.overflow    = 1'b0;
    assign racl_error_o.read_access = tl_h2d_i.a_opcode == tlul_pkg::Get;
    assign racl_error_o.racl_role   = racl_role;
    assign racl_error_o.ctn_uid     = top_racl_pkg::tlul_extract_ctn_uid_bits(tl_h2d_i.a_user.rsvd);
    assign racl_error_o.request_address = tl_h2d_i.a_address;
  end else begin : gen_no_racl_role_logic
    // Pass through and default assignments
    assign tl_filtered_h2d_o = tl_h2d_i;
    assign tl_d2h_o          = tl_filtered_d2h_i;
    assign racl_error_o      = '0;

    // Some signals are not read when RACL is disabled
    logic unused_signals;
    assign unused_signals = ^racl_policy_sel_ranges_i;
  end

  // Not all RACL policies are used, even if RACL is enabled
  logic unused_policy_sel;
  assign unused_policy_sel = ^racl_policies_i;

  `ASSERT(RaclAdapterNumRanges, EnableRacl |-> RaclPolicySelNumRanges > 0)

  // Ensure that RACL signals are not undefined
  `ASSERT_KNOWN(RaclAdapterErrorKnown_A, racl_error_o.valid)

endmodule
