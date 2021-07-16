// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// CDC module for SPI_HOST commands
//

module spi_host_command_cdc (
  input                              clk_i,
  input                              rst_ni,

  input                              clk_core_i,
  input                              rst_core_ni,

  input  spi_host_cmd_pkg::command_t command_i,
  input                              command_valid_i,
  output logic                       command_busy_o,

  output spi_host_cmd_pkg::command_t core_command_o,
  output logic                       core_command_valid_o,
  input                              core_command_ready_i,

  output logic                       error_busy_o,

  input                              sw_rst_i,
  input                              core_sw_rst_i
);

  assign error_busy_o = command_valid_i & command_busy_o;

  logic                                 command_ack;
  logic [spi_host_cmd_pkg::CmdSize-1:0] command_q;
  logic [spi_host_cmd_pkg::CmdSize-1:0] command_d;

  assign command_ack = command_valid_i & ~command_busy_o & ~sw_rst_i;

  // command_d serves as the input to both the command latch register and to the CDC, to ensure that
  // the CDC input stays stable for an extra cycle before command_valid_i.
  assign command_d   = command_ack ? command_i : command_q;

  logic                                 cdc_req_q;
  logic                                 cdc_req_d;
  logic                                 cdc_ack;

  assign cdc_req_d = command_ack ? 1'b1 :
                     cdc_ack     ? 1'b0 :
                     cdc_req_q;

  assign command_busy_o = cdc_req_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      command_q <= {spi_host_cmd_pkg::CmdSize{1'b0}};
      cdc_req_q <= 1'b0;
    end else begin
      cdc_req_q <= cdc_req_d;
      command_q <= command_d;
    end
  end

  // When sw_rst is established, let the handshake end passively by always acknowledging when valid
  logic core_cdc_req;
  logic core_cdc_ack;
  assign core_cdc_ack = (core_command_ready_i | sw_rst_i) & core_cdc_req;

  // drop requests when sw_rst_i is active
  assign core_command_valid_o = core_cdc_req & ~core_sw_rst_i;

  prim_sync_reqack_data #(
    .Width(spi_host_cmd_pkg::CmdSize),
    .DataSrc2Dst(1'b1)
  ) u_sync_reqack (
    .clk_src_i  (clk_i),
    .rst_src_ni (rst_ni),
    .clk_dst_i  (clk_core_i),
    .rst_dst_ni (rst_core_ni),
    .req_chk_i  (1'b1),
    .src_req_i  (cdc_req_q),
    .src_ack_o  (cdc_ack),
    .dst_req_o  (core_cdc_req),
    .dst_ack_i  (core_cdc_ack),
    .data_i     (command_d),
    .data_o     (core_command_o)
  );

endmodule : spi_host_command_cdc
