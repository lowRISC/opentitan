// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module aes_alert_check
  import aes_reg_pkg::*;
(
 input logic               clk_i,
 input logic               rst_ni,
 input aes_reg2hw_t        reg2hw,
 input logic               alert_i
 );


  logic                    alert;

  assign alert = (reg2hw.status.alert_fatal_fault.d == 1'b1) ? : ;

  // make sure idle_i always matched the register idle state
  `ASSERT(FatalNotFatal_A, alert == alert_i);
endmodule
prim_alert_pkg::alert_tx_t
