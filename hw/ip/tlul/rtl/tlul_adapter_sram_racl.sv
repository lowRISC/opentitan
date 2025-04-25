// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * Tile-Link UL adapter for SRAM-like devices with RACL support
 *
 * - Intentionally omitted BaseAddr in case of multiple memory maps are used in a SoC,
 *   it means that aliasing can happen if target device size in TL-UL crossbar is bigger
 *   than SRAM size
 * - At most one of EnableDataIntgGen / EnableDataIntgPt can be enabled. However it
 *   possible for both to be disabled.
 *   A module can neither generate an integrity response nor pass through any pre-existing
 *   integrity.  This might be the case for non-security critical memories where there is
 *   no stored integrity AND another entity upstream is already generating returning integrity.
 *   There is however no case where EnableDataIntgGen and EnableDataIntgPt are both true.
 */
module tlul_adapter_sram_racl
  import tlul_pkg::*;
  import prim_mubi_pkg::mubi4_t;
#(
  parameter int SramAw            = 12,
  parameter int SramDw            = 32,         // Must be multiple of the TL width
  parameter int Outstanding       = 1,          // Only one request is accepted
  parameter int SramBusBankAW     = 12,         // SRAM bus address width of the SRAM bank. Only
                                                // used when DataXorAddr=1.
  parameter bit ByteAccess        = 1,          // 1: Enables sub-word write transactions. Note that
                                                //    this results in read-modify-write operations
                                                //    for integrity re-generation if
                                                //    EnableDataIntgPt is set to 1.
  parameter bit ErrOnWrite        = 0,          // 1: Writes not allowed, automatically error
  parameter bit ErrOnRead         = 0,          // 1: Reads not allowed, automatically error
  parameter bit CmdIntgCheck      = 0,          // 1: Enable command integrity check
  parameter bit EnableRspIntgGen  = 0,          // 1: Generate response integrity
  parameter bit EnableDataIntgGen = 0,          // 1: Generate response data integrity
  parameter bit EnableDataIntgPt  = 0,          // 1: Passthrough command/response data integrity
  parameter bit SecFifoPtr        = 0,          // 1: Duplicated fifo pointers
  parameter bit EnableReadback    = 0,          // 1: Readback and check written/read data.
  parameter bit DataXorAddr       = 0,          // 1: XOR data and address for address protection
  parameter bit EnableRacl        = 0,          // 1: Enable RACL checks on access
  parameter bit RaclErrorRsp      = EnableRacl, // 1: Return TLUL error on RACL errors
  parameter int RaclPolicySelNumRanges = 1,     // Number of ranges with a RACL policy
  localparam int WidthMult        = SramDw / top_pkg::TL_DW,
  localparam int IntgWidth        = tlul_pkg::DataIntgWidth * WidthMult,
  localparam int DataOutW         = EnableDataIntgPt ? SramDw + IntgWidth : SramDw
) (
  input   clk_i,
  input   rst_ni,

  // TL-UL interface
  input   tl_h2d_t          tl_i,
  output  tl_d2h_t          tl_o,

  // control interface
  input   mubi4_t en_ifetch_i,

  // SRAM interface
  output logic                 req_o,
  output mubi4_t               req_type_o,
  input                        gnt_i,
  output logic                 we_o,
  output logic [SramAw-1:0]    addr_o,
  output logic [DataOutW-1:0]  wdata_o,
  output logic [DataOutW-1:0]  wmask_o,
  output logic                 intg_error_o,
  output logic [RsvdWidth-1:0] user_rsvd_o,
  input        [DataOutW-1:0]  rdata_i,
  input                        rvalid_i,
  input        [1:0]           rerror_i, // 2 bit error [1]: Uncorrectable, [0]: Correctable
  output logic                 compound_txn_in_progress_o,
  input  mubi4_t               readback_en_i,
  output logic                 readback_error_o,
  input  logic                 wr_collision_i,
  input  logic                 write_pending_i,
  // RACL interface
  input  top_racl_pkg::racl_policy_vec_t racl_policies_i,
  output top_racl_pkg::racl_error_log_t  racl_error_o,
  input  top_racl_pkg::racl_range_t [RaclPolicySelNumRanges-1:0] racl_policy_sel_ranges_i
);
  tl_h2d_t tl_h2d_filtered;
  tl_d2h_t tl_d2h_filtered;

  tlul_adapter_racl #(
    .EnableRacl               ( EnableRacl             ),
    .RaclErrorRsp             ( RaclErrorRsp           ),
    .RaclPolicySelNumRanges   ( RaclPolicySelNumRanges )
  ) tlul_adapter_racl(
    .clk_i                    ( clk_i                    ),
    .rst_ni                   ( rst_ni                   ),
    .tl_h2d_i                 ( tl_i                     ),
    .tl_d2h_o                 ( tl_o                     ),
    .tl_filtered_h2d_o        ( tl_h2d_filtered          ),
    .tl_filtered_d2h_i        ( tl_d2h_filtered          ),
    .racl_policies_i          ( racl_policies_i          ),
    .racl_error_o             ( racl_error_o             ),
    .racl_policy_sel_ranges_i ( racl_policy_sel_ranges_i )
  );

  tlul_adapter_sram #(
    .SramAw            ( SramAw            ),
    .SramDw            ( SramDw            ),
    .Outstanding       ( Outstanding       ),
    .SramBusBankAW     ( SramBusBankAW     ),
    .ByteAccess        ( ByteAccess        ),
    .ErrOnWrite        ( ErrOnWrite        ),
    .ErrOnRead         ( ErrOnRead         ),
    .CmdIntgCheck      ( CmdIntgCheck      ),
    .EnableRspIntgGen  ( EnableRspIntgGen  ),
    .EnableDataIntgGen ( EnableDataIntgGen ),
    .EnableDataIntgPt  ( EnableDataIntgPt  ),
    .SecFifoPtr        ( SecFifoPtr        ),
    .EnableReadback    ( EnableReadback    ),
    .DataXorAddr       ( DataXorAddr       )
  ) tlul_adapter_sram (
    .clk_i,
    .rst_ni,
    .tl_i(tl_h2d_filtered),
    .tl_o(tl_d2h_filtered),
    .en_ifetch_i,
    .req_o,
    .req_type_o,
    .gnt_i,
    .we_o,
    .addr_o,
    .wdata_o,
    .wmask_o,
    .intg_error_o,
    .user_rsvd_o,
    .rdata_i,
    .rvalid_i,
    .rerror_i,
    .compound_txn_in_progress_o,
    .readback_en_i,
    .readback_error_o,
    .wr_collision_i,
    .write_pending_i
  );

  // Ensure that RACL signals are not undefined
  `ASSERT_KNOWN(RaclAdapterSramErrorKnown_A, racl_error_o.valid)

endmodule
