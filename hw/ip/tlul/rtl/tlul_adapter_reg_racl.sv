// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * Tile-Link UL adapter for Register interface with RACL protection
 */

module tlul_adapter_reg_racl
  import tlul_pkg::*;
  import prim_mubi_pkg::mubi4_t;
#(
  parameter  bit CmdIntgCheck      = 0,           // 1: Enable command integrity check
  parameter  bit EnableRspIntgGen  = 0,           // 1: Generate response integrity
  parameter  bit EnableDataIntgGen = 0,           // 1: Generate response data integrity
  parameter  int RegAw             = 8,           // Width of register address
  parameter  int RegDw             = 32,          // Shall be matched with TL_DW
  parameter  int AccessLatency     = 0,           // 0: same cycle, 1: next cycle
  parameter  bit EnableRacl        = 0,           // 1: Enable RACL checks on access
  parameter  bit RaclErrorRsp      = EnableRacl,  // 1: Return TLUL error on RACL errors
  parameter  top_racl_pkg::racl_policy_sel_t RaclPolicySelVec  = 0, // RACL policy for this reg
                                                                    // adapter
  localparam int RegBw             = RegDw/8
) (
  input clk_i,
  input rst_ni,

  // TL-UL interface
  input  tl_h2d_t tl_i,
  output tl_d2h_t tl_o,

  // control interface
  input  mubi4_t  en_ifetch_i,
  output logic    intg_error_o,

  // RACL interface
  input  top_racl_pkg::racl_policy_vec_t racl_policies_i,
  output top_racl_pkg::racl_error_log_t  racl_error_o,

  // Register interface
  output logic             re_o,
  output logic             we_o,
  output logic [RegAw-1:0] addr_o,
  output logic [RegDw-1:0] wdata_o,
  output logic [RegBw-1:0] be_o,
  input                    busy_i,
  // The following two signals are expected
  // to be returned in AccessLatency cycles.
  input        [RegDw-1:0] rdata_i,
  // This can be a write or read error.
  input                    error_i
);
  tl_h2d_t tl_h2d_filtered;
  tl_d2h_t tl_d2h_filtered;

  if (EnableRacl) begin : gen_racl_role_logic
    // Retrieve RACL role from user bits and one-hot encode that for the comparison bitmap
    top_racl_pkg::racl_role_t racl_role;
    assign racl_role = top_racl_pkg::tlul_extract_racl_role_bits(tl_i.a_user.rsvd);

    top_racl_pkg::racl_role_vec_t racl_role_vec;
    prim_onehot_enc #(
      .OneHotWidth( $bits(top_racl_pkg::racl_role_vec_t) )
    ) u_racl_role_encode (
      .in_i ( racl_role     ),
      .en_i ( 1'b1          ),
      .out_o( racl_role_vec )
    );

    logic rd_req, wr_req, racl_read_allowed, racl_write_allowed, racl_error;
    assign rd_req             = tl_i.a_valid & (tl_i.a_opcode == tlul_pkg::Get);
    assign wr_req             = tl_i.a_valid & (tl_i.a_opcode == tlul_pkg::PutFullData |
                                                tl_i.a_opcode == tlul_pkg::PutPartialData);
    assign racl_read_allowed  = (|(racl_policies_i[RaclPolicySelVec].read_perm  & racl_role_vec));
    assign racl_write_allowed = (|(racl_policies_i[RaclPolicySelVec].write_perm & racl_role_vec));
    assign racl_error         = (rd_req & ~racl_read_allowed) | (wr_req & ~racl_write_allowed);
    assign racl_error_o.valid = racl_error & tl_o.a_ready;

    tlul_request_loopback #(
      .ErrorRsp(RaclErrorRsp)
    ) u_loopback (
      .clk_i,
      .rst_ni,
      .squash_req_i ( racl_error      ),
      .tl_h2d_i     ( tl_i            ),
      .tl_d2h_o     ( tl_o            ),
      .tl_h2d_o     ( tl_h2d_filtered ),
      .tl_d2h_i     ( tl_d2h_filtered )
    );

    // Collect RACL error information
    assign racl_error_o.overflow        = 1'b0;
    assign racl_error_o.read_access     = tl_i.a_opcode == tlul_pkg::Get;
    assign racl_error_o.racl_role       = racl_role;
    assign racl_error_o.ctn_uid         = top_racl_pkg::tlul_extract_ctn_uid_bits(tl_i.a_user.rsvd);
    assign racl_error_o.request_address = tl_i.a_address;
  end else begin : gen_no_racl_role_logic
    // Pass through and default assignments
    assign tl_h2d_filtered  = tl_i;
    assign tl_o             = tl_d2h_filtered;
    assign racl_error_o     = '0;
  end

  tlul_adapter_reg #(
    .CmdIntgCheck       (CmdIntgCheck),
    .EnableRspIntgGen   (EnableRspIntgGen),
    .EnableDataIntgGen  (EnableDataIntgGen),
    .RegAw              (RegAw),
    .RegDw              (RegDw),
    .AccessLatency      (AccessLatency)
  ) tlul_adapter_reg (
    .clk_i,
    .rst_ni,
    .tl_i(tl_h2d_filtered),
    .tl_o(tl_d2h_filtered),
    .en_ifetch_i,
    .intg_error_o,
    .re_o,
    .we_o,
    .addr_o,
    .wdata_o,
    .be_o,
    .busy_i,
    .rdata_i,
    .error_i
  );

  // Not all RACL policies are used, even if RACL is enabled
  logic unused_policy;
  assign unused_policy = ^racl_policies_i;

  // Ensure that RACL signals are not undefined
  `ASSERT_KNOWN(RaclAdapterRegErrorKnown_A, racl_error_o.valid)

endmodule
