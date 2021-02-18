// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// N:1 SRAM arbiter
//
// Parameter
//  N:  Number of requst port
//  DW: Data width (SECDED is not included)
//  Aw: Address width
//  ArbiterImpl: can be either PPC or BINTREE.
`include "prim_assert.sv"

module prim_sram_arbiter #(
  parameter int N  = 4,
  parameter int SramDw = 32,
  parameter int SramAw = 12,
  parameter ArbiterImpl = "PPC"
) (
  input clk_i,
  input rst_ni,

  input        [     N-1:0] req_i,
  input        [SramAw-1:0] req_addr_i [N],
  input                     req_write_i[N],
  input        [SramDw-1:0] req_wdata_i[N],
  output logic [     N-1:0] gnt_o,

  output logic [     N-1:0] rsp_rvalid_o,      // Pulse
  output logic [SramDw-1:0] rsp_rdata_o[N],
  output logic [       1:0] rsp_error_o[N],

  // SRAM Interface
  output logic              sram_req_o,
  output logic [SramAw-1:0] sram_addr_o,
  output logic              sram_write_o,
  output logic [SramDw-1:0] sram_wdata_o,
  input                     sram_rvalid_i,
  input        [SramDw-1:0] sram_rdata_i,
  input        [1:0]        sram_rerror_i
);


  typedef struct packed {
    logic write;
    logic [SramAw-1:0] addr;
    logic [SramDw-1:0] wdata;
  } req_t;

  localparam int ARB_DW = $bits(req_t);

  req_t req_packed [N];

  for (genvar i = 0 ; i < N ; i++) begin : gen_reqs
    assign req_packed[i] = {req_write_i[i], req_addr_i[i], req_wdata_i[i]};
  end

  req_t sram_packed;
  assign sram_write_o = sram_packed.write;
  assign sram_addr_o  = sram_packed.addr;
  assign sram_wdata_o = sram_packed.wdata;

  if (ArbiterImpl == "PPC") begin : gen_arb_ppc
    prim_arbiter_ppc #(
      .N (N),
      .DW(ARB_DW)
    ) u_reqarb (
      .clk_i,
      .rst_ni,
      .req_i,
      .data_i  ( req_packed  ),
      .gnt_o,
      .idx_o   (             ),
      .valid_o ( sram_req_o  ),
      .data_o  ( sram_packed ),
      .ready_i ( 1'b1        )
    );
  end else if (ArbiterImpl == "BINTREE") begin : gen_tree_arb
    prim_arbiter_tree #(
      .N (N),
      .DW(ARB_DW)
    ) u_reqarb (
      .clk_i,
      .rst_ni,
      .req_i,
      .data_i  ( req_packed  ),
      .gnt_o,
      .idx_o   (             ),
      .valid_o ( sram_req_o  ),
      .data_o  ( sram_packed ),
      .ready_i ( 1'b1        )
    );
  end else begin : gen_unknown
    `ASSERT_INIT(UnknownArbImpl_A, 0)
  end


  logic [N-1:0] steer;    // Steering sram_rvalid_i
  logic sram_ack;         // Ack for rvalid. |sram_rvalid_i

  assign sram_ack = sram_rvalid_i & (|steer);

  // Request FIFO
  prim_fifo_sync #(
    .Width    (N),
    .Pass     (1'b0),
    .Depth    (4)        // Assume at most 4 pipelined
  ) u_req_fifo (
    .clk_i,
    .rst_ni,
    .clr_i    (1'b0),
    .wvalid_i (sram_req_o & ~sram_write_o),  // Push only for read
    .wready_o (),     // TODO: Generate Error
    .wdata_i  (gnt_o),
    .rvalid_o (),     // TODO; Generate error if sram_rvalid_i but rvalid==0
    .rready_i (sram_ack),
    .rdata_o  (steer),
    .full_o   (),
    .depth_o  ()     // Not used
  );

  assign rsp_rvalid_o = steer & {N{sram_rvalid_i}};

  for (genvar i = 0 ; i < N ; i++) begin : gen_rsp
    assign rsp_rdata_o[i] = sram_rdata_i;
    assign rsp_error_o[i] = sram_rerror_i; // No SECDED yet
  end

endmodule
