// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Queue for SPI_HOST commands
//

module spi_host_command_queue #(
  parameter int          CmdDepth = 4,
  parameter int unsigned NumCS    = 1,
  localparam int CSW              = prim_util_pkg::vbits(NumCS)
) (
  input                              clk_i,
  input                              rst_ni,

  input  spi_host_cmd_pkg::command_t command_i,
  input  logic [CSW-1:0]             command_csid_i,
  input                              command_valid_i,
  output logic                       command_busy_o,

  output spi_host_cmd_pkg::command_t core_command_o,
  output logic [CSW-1:0]             core_command_csid_o,
  output logic                       core_command_valid_o,
  input                              core_command_ready_i,

  output logic [3:0]                 qd_o,

  output logic                       error_busy_o,

  input                              sw_rst_i
);

  localparam int CmdDepthW = prim_util_pkg::vbits(CmdDepth+1);

  logic command_ready;

  assign command_busy_o = ~command_ready;
  assign error_busy_o   = command_valid_i & command_busy_o;

  logic [CmdDepthW-1:0] cmd_depth;

  prim_fifo_sync #(
    .Width($bits(spi_host_cmd_pkg::command_t) + CSW),
    .Pass(0),
    .Depth(CmdDepth)
  ) cmd_fifo (
    .clk_i,
    .rst_ni,
    .clr_i    (sw_rst_i),
    .wvalid_i (command_valid_i),
    .wready_o (command_ready),
    .wdata_i  ({command_i, command_csid_i}),
    .rvalid_o (core_command_valid_o),
    .rready_i (core_command_ready_i),
    .rdata_o  ({core_command_o, core_command_csid_o}),
    .full_o   (),
    .depth_o  (cmd_depth),
    .err_o    ()
  );

  assign qd_o = 4'(cmd_depth);

endmodule : spi_host_command_queue
