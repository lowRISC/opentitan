// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: edn top level wrapper file

`include "prim_assert.sv"

module edn import edn_pkg::*; #(
  parameter int NumEndPoints = 4,
  parameter int BootInsCmd = 32'h0000_0001,
  parameter int BootGenCmd = 32'h0000_3003
) (
  input logic clk_i,
  input logic rst_ni,

  // reg bus Interface
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // edn interfaces
  input  edn_req_t [NumEndPoints-1:0] edn_i,
  output edn_rsp_t [NumEndPoints-1:0] edn_o,

  // csrng application interface
  output  csrng_pkg::csrng_req_t  csrng_cmd_o,
  input   csrng_pkg::csrng_rsp_t  csrng_cmd_i,

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
    .NumEndPoints(NumEndPoints),
    .BootInsCmd(BootInsCmd),
    .BootGenCmd(BootGenCmd)
  ) u_edn_core (
    .clk_i,
    .rst_ni,
    .reg2hw,
    .hw2reg,

    .edn_i,
    .edn_o,

    .csrng_cmd_o,
    .csrng_cmd_i,

    .intr_edn_cmd_req_done_o,
    .intr_edn_fifo_err_o
  );


  // Assertions

  `ASSERT_KNOWN(TlDValidKnownO_A, tl_o.d_valid)
  `ASSERT_KNOWN(TlAReadyKnownO_A, tl_o.a_ready)

  // Endpoint Asserts
  for (genvar i = 0; i < NumEndPoints; i = i+1) begin : gen_edn_if_asserts
    `ASSERT_KNOWN(EdnEndPointOut_A, edn_o[i])
  end : gen_edn_if_asserts

  // CSRNG Asserts
  `ASSERT_KNOWN(CsrngAppIfOut_A, csrng_cmd_o)

  // Interrupt Asserts
  `ASSERT_KNOWN(IntrEdnCmdReqDoneKnownO_A, intr_edn_cmd_req_done_o)
  `ASSERT_KNOWN(IntrEdnFifoErrKnownO_A, intr_edn_fifo_err_o)

endmodule
