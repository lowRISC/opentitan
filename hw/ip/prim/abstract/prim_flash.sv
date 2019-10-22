// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TODO: This module is a hard-coded stopgap to select an implementation of an
// "abstract module". This module is to be replaced by generated code.

`ifndef PRIM_DEFAULT_IMPL
  `define PRIM_DEFAULT_IMPL prim_pkg::ImplGeneric
`endif

module prim_flash #(
  parameter prim_pkg::impl_e Impl = `PRIM_DEFAULT_IMPL,

  parameter int PagesPerBank = 256, // pages per bank
  parameter int WordsPerPage = 256, // words per page
  parameter int DataWidth   = 32, // bits per word

  //Do not touch - Derived parameters
  parameter int PageW = $clog2(PagesPerBank),
  parameter int WordW = $clog2(WordsPerPage),
  parameter int AddrW = PageW + WordW
) (
  input                        clk_i,
  input                        rst_ni,
  input                        req_i,
  input                        host_req_i,
  input [AddrW-1:0]            host_addr_i,
  input                        rd_i,
  input                        prog_i,
  input                        pg_erase_i,
  input                        bk_erase_i,
  input [AddrW-1:0]            addr_i,
  input [DataWidth-1:0]        prog_data_i,
  output logic                 host_req_rdy_o,
  output logic                 host_req_done_o,
  output logic                 rd_done_o,
  output logic                 prog_done_o,
  output logic                 erase_done_o,
  output logic [DataWidth-1:0] rd_data_o,
  output logic                 init_busy_o
);

  import prim_pkg::*;

  if (Impl == ImplGeneric || Impl == ImplXilinx) begin : gen_flash
    prim_generic_flash #(
      .PagesPerBank(PagesPerBank),
      .WordsPerPage(WordsPerPage),
      .DataWidth(DataWidth)
    ) u_impl_generic (
      .clk_i,
      .rst_ni,
      .req_i,
      .host_req_i,
      .host_addr_i,
      .rd_i,
      .prog_i,
      .pg_erase_i,
      .bk_erase_i,
      .addr_i,
      .prog_data_i,
      .host_req_rdy_o,
      .host_req_done_o,
      .rd_done_o,
      .prog_done_o,
      .erase_done_o,
      .rd_data_o,
      .init_busy_o
    );
  end else begin : gen_failure
    // TODO: Find code that works across tools and causes a compile failure
  end

endmodule
