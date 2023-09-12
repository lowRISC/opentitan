// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module mbx_sramrwarb
  import  tlul_pkg::*;
#(
  parameter int unsigned CfgSramAddrWidth = 32,
  parameter int unsigned CfgSramDataWidth = 32
) (
  input  logic                        clk_i,
  input  logic                        rst_ni,
  // Host port for memory accesses to the OT private memory
  output  tlul_pkg::tl_h2d_t          tl_host_o,
  input   tlul_pkg::tl_d2h_t          tl_host_i,
  output  logic                       intg_err_o,
  output  logic                       sram_err_o,

  // Interface to the inbound mailbox
  input  logic                        imbx_sram_write_req_i,
  output logic                        imbx_sram_write_gnt_o,
  input  logic [CfgSramAddrWidth-1:0] imbx_sram_write_ptr_i,
  output logic                        imbx_sram_write_resp_vld_o,
  input  logic [CfgSramDataWidth-1:0] imbx_write_data_i,
  // Interface to the outpbound mailbox
  input  logic                        ombx_sram_read_req_i,
  output logic                        ombx_sram_read_gnt_o,
  input  logic [CfgSramAddrWidth-1:0] ombx_sram_read_ptr_i,
  output logic                        ombx_sram_read_resp_vld_o,
  output logic [CfgSramDataWidth-1:0] ombx_sram_read_resp_o
);
  import  prim_mubi_pkg::*;
  // Maximum number of outstanding requests
  localparam  int unsigned LCFG_MAX_REQS = 4;
  localparam  int unsigned LCFG_MAX_REQS_LOG2 = $clog2(LCFG_MAX_REQS) + 1;

  // We prioritize the read request.
  // Winner has an outstanding read request.
  logic arb_read_winner;
  assign arb_read_winner = ombx_sram_read_req_i;

  // Winner has an outstanding write request but there is no read request
  logic arb_write_winner;
  assign arb_write_winner = imbx_sram_write_req_i & ~arb_read_winner;

  // Granting logic. Mux it to the request
  logic sram_gnt, sram_valid, max_outstanding_reqs_reached;
  assign ombx_sram_read_gnt_o  = arb_read_winner  & (~max_outstanding_reqs_reached & sram_gnt);
  assign imbx_sram_write_gnt_o = arb_write_winner & (~max_outstanding_reqs_reached & sram_gnt);

  // Mux the arbitration winner address
  logic [CfgSramAddrWidth-1:0] sram_address;
  assign sram_address = arb_read_winner? ombx_sram_read_ptr_i :
                                         imbx_sram_write_ptr_i;

  // make sure the request FIFO is ready (ie not empty)
  logic sram_req;
  assign sram_req = (ombx_sram_read_req_i | imbx_sram_write_req_i);

  // FIFO Counting logic for maximum outstanding requests
  logic [LCFG_MAX_REQS_LOG2-1:0] outstanding_req_count_d, outstanding_req_count_q;
  logic inc_cnt, dec_cnt;
  assign  inc_cnt                 = sram_req & ~max_outstanding_reqs_reached & sram_gnt;
  assign  dec_cnt                 = sram_valid;
  assign  outstanding_req_count_d = outstanding_req_count_q + inc_cnt - dec_cnt;

  prim_generic_flop_en #(
    .Width(LCFG_MAX_REQS_LOG2)
  ) u_outstanding_req_cnt (
    .clk_i  ( clk_i                   ),
    .rst_ni ( rst_ni                  ),
    .en_i   ( inc_cnt | dec_cnt       ),
    .d_i    ( outstanding_req_count_d ),
    .q_o    ( outstanding_req_count_q )
  );
  // Block SRAM requests if we reached the maximum outstanding number
  assign  max_outstanding_reqs_reached = (outstanding_req_count_q == LCFG_MAX_REQS);

  tlul_adapter_host #(
    .MAX_REQS              ( LCFG_MAX_REQS ),
    .EnableDataIntgGen     ( 1             ),
    .EnableRspDataIntgCheck( 1             )
  )  u_sram_host_adapter (
    .clk_i             ( clk_i                                    ),
    .rst_ni            ( rst_ni                                   ),
    // Request channel
    .req_i             ( sram_req & ~max_outstanding_reqs_reached ),
    .gnt_o             ( sram_gnt                                 ),
    .addr_i            ( sram_address                             ),
    .we_i              ( arb_write_winner                         ),
    .wdata_i           ( imbx_write_data_i                       ),
    .wdata_intg_i      ( TL_A_USER_DEFAULT.data_intg              ),
    .be_i              ( {{top_pkg::TL_DBW}{1'b1}}                ),
    .instr_type_i      ( prim_mubi_pkg::MuBi4False                ),
    .user_rsvd_i       ( '0                                       ),
    // Response channel
    .valid_o           ( sram_valid                               ),
    .rdata_o           ( ombx_sram_read_resp_o                    ),
    .rdata_intg_o      (                                          ),
    .err_o             ( sram_err_o                               ),
    .intg_err_o        ( intg_err_o                               ),
    // Bus interface
    .tl_o              ( tl_host_o                                ),
    .tl_i              ( tl_host_i                                )
  );

  // Mux out response valid signal
  // We cannot differentiate on directly on the response signal of the TLUL adapter. We need
  // to look if the response was a response with data or not. It it's with data, it was a read
  // request and we serve ombx_sram_read_resp_vld_o. If it was a response without data
  // it was a write request, so we serve imbx_sram_write_resp_vld_o
  assign  ombx_sram_read_resp_vld_o  = sram_valid & (tl_host_i.d_opcode == tlul_pkg::AccessAckData);
  assign  imbx_sram_write_resp_vld_o = sram_valid & (tl_host_i.d_opcode == tlul_pkg::AccessAck);

  // Functional Coverage
  `COVER(MaxOutstandingRequetsReached_C, sram_req & max_outstanding_reqs_reached)
endmodule
