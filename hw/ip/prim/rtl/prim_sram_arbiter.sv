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

  input        [     N-1:0] req,
  input        [SramAw-1:0] req_addr   [N],
  input                     req_write  [N],
  input        [SramDw-1:0] req_wdata  [N],
  output logic [     N-1:0] gnt,

  output logic [     N-1:0] rsp_rvalid,      // Pulse
  output logic [SramDw-1:0] rsp_rdata  [N],
  output logic [       1:0] rsp_error  [N],

  // SRAM Interface
  output logic              sram_req,
  output logic [SramAw-1:0] sram_addr,
  output logic              sram_write,
  output logic [SramDw-1:0] sram_wdata,
  input                     sram_rvalid,
  input        [SramDw-1:0] sram_rdata,
  input        [1:0]        sram_rerror
);


  typedef struct packed {
    logic write;
    logic [SramAw-1:0] addr;
    logic [SramDw-1:0] wdata;
  } req_t;

  localparam int ARB_DW = $bits(req_t);

  req_t req_packed [N];

  for (genvar i = 0 ; i < N ; i++) begin : gen_reqs
    assign req_packed[i] = {req_write[i], req_addr[i], req_wdata[i]};
  end

  req_t sram_packed;
  assign sram_write = sram_packed.write;
  assign sram_addr  = sram_packed.addr;
  assign sram_wdata = sram_packed.wdata;

  if (ArbiterImpl == "PPC") begin : gen_arb_ppc
    prim_arbiter_ppc #(
      .N (N),
      .DW(ARB_DW)
    ) u_reqarb (
      .clk_i,
      .rst_ni,
      .req_i   ( req         ),
      .data_i  ( req_packed  ),
      .gnt_o   ( gnt         ),
      .idx_o   (             ),
      .valid_o ( sram_req    ),
      .data_o  ( sram_packed ),
      .ready_i ( 1'b1        )
    );
  end else if (ArbiterImpl == "BINTREE") begin : gen_tree_arb
    prim_arbiter_arb #(
      .N (N),
      .DW(ARB_DW)
    ) u_reqarb (
      .clk_i,
      .rst_ni,
      .req_i   ( req         ),
      .data_i  ( req_packed  ),
      .gnt_o   ( gnt         ),
      .idx_o   (             ),
      .valid_o ( sram_req    ),
      .data_o  ( sram_packed ),
      .ready_i ( 1'b1        )
    );
  end else begin : gen_unknown
    `ASSERT_INIT(UnknownArbImpl_A, 0)
  end


  logic [N-1:0] steer;    // Steering sram_rvalid
  logic sram_ack;         // Ack for rvalid. |sram_rvalid

  assign sram_ack = sram_rvalid & (|steer);

  // Request FIFO
  prim_fifo_sync #(
    .Width    (N),
    .Pass     (1'b0),
    .Depth    (4)        // Assume at most 4 pipelined
  ) u_req_fifo (
    .clk_i,
    .rst_ni,
    .clr_i    (1'b0),
    .wvalid   (sram_req && !sram_write),  // Push only for read
    .wready   (),     // TODO: Generate Error
    .wdata    (gnt),
    .depth    (),     // Not used
    .rvalid   (),     // TODO; Generate error if sram_rvalid but rvalid==0
    .rready   (sram_ack),
    .rdata    (steer)
  );

  assign rsp_rvalid = steer & {N{sram_rvalid}};

  for (genvar i = 0 ; i < N ; i++) begin : gen_rsp
    assign rsp_rdata[i] = sram_rdata;
    assign rsp_error[i] = sram_rerror; // No SECDED yet
  end

endmodule
