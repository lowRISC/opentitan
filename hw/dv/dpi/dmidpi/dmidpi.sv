// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module dmidpi #(
  parameter string Name = "dmi0", // name of the interface (display only)
  parameter int ListenPort = 44853 // TCP port to listen on
)(
  input  bit        clk_i,
  input  bit        rst_ni,

  output bit        dmi_req_valid,
  input  bit        dmi_req_ready,
  output bit [6:0]  dmi_req_addr,
  output bit [1:0]  dmi_req_op,
  output bit [31:0] dmi_req_data,
  input  bit        dmi_rsp_valid,
  output bit        dmi_rsp_ready,
  input  bit [31:0] dmi_rsp_data,
  input  bit [1:0]  dmi_rsp_resp,
  output bit        dmi_rst_n
);

  import "DPI-C"
  function chandle dmidpi_create(input string name, input int listen_port);

  import "DPI-C"
  function void dmidpi_tick(input chandle ctx, output bit dmi_req_valid,
                            input bit dmi_req_ready, output bit [6:0] dmi_req_addr,
                            output bit [1:0] dmi_req_op, output bit [31:0] dmi_req_data,
                            input bit dmi_rsp_valid, output bit dmi_rsp_ready,
                            input bit [31:0] dmi_rsp_data, input bit [1:0] dmi_rsp_resp,
                            output bit dmi_rst_n);

  import "DPI-C"
  function void dmidpi_close(input chandle ctx);

  chandle ctx;

  initial begin
    ctx = dmidpi_create(Name, ListenPort);
  end

  final begin
    dmidpi_close(ctx);
    ctx = null;
  end

  always_ff @(posedge clk_i, negedge rst_ni) begin
    dmidpi_tick(ctx, dmi_req_valid, dmi_req_ready, dmi_req_addr, dmi_req_op,
                dmi_req_data, dmi_rsp_valid, dmi_rsp_ready, dmi_rsp_data,
                dmi_rsp_resp, dmi_rst_n);
  end

endmodule
