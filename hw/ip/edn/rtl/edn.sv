// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: edn top level wrapper file


module edn import edn_pkg::*; import csrng_pkg::*; #(
  parameter int EndPointBusWidth0 = 32,
  parameter int EndPointBusWidth1 = 16,
  parameter int EndPointBusWidth2 = 8,
  parameter int EndPointBusWidth3 = 4,
  parameter int BootInsCmd = 32'h0000_0001,
  parameter int BootGenCmd = 32'h0000_3003
) (
  input logic clk_i,
  input logic rst_ni,

  // reg bus Interface
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // edn interfaces
  input  edn_req_t [3:0] edn_i,
  output edn_rsp_t [3:0] edn_o,
  output logic [EndPointBusWidth0-1:0] edn_bus0_o,
  output logic [EndPointBusWidth1-1:0] edn_bus1_o,
  output logic [EndPointBusWidth2-1:0] edn_bus2_o,
  output logic [EndPointBusWidth3-1:0] edn_bus3_o,

  // csrng application interface
  output  csrng_req_t  csrng_cmd_o,
  input   csrng_rsp_t  csrng_cmd_i,

  // Interrupts
  output logic      intr_edn_cmd_req_done_o,
  output logic      intr_edn_fifo_err_o
);

  import edn_reg_pkg::*;

  edn_reg2hw_t reg2hw;
  edn_hw2reg_t hw2reg;

  edn_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,

    .devmode_i(1'b1)
  );

  edn_core #(
    .EndPointBusWidth0(EndPointBusWidth0),
    .EndPointBusWidth1(EndPointBusWidth1),
    .EndPointBusWidth2(EndPointBusWidth2),
    .EndPointBusWidth3(EndPointBusWidth3),
    .BootInsCmd(BootInsCmd),
    .BootGenCmd(BootGenCmd)
  ) u_edn_core (
    .clk_i,
    .rst_ni,
    .reg2hw,
    .hw2reg,

    .edn_i,
    .edn_o,
    .edn_bus0_o,
    .edn_bus1_o,
    .edn_bus2_o,
    .edn_bus3_o,

    .csrng_cmd_o,
    .csrng_cmd_i,

    .intr_edn_cmd_req_done_o,
    .intr_edn_fifo_err_o
  );

endmodule
