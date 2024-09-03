// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: UART top level wrapper file

//algrin `include "prim_assert.sv"

module perfcounters_t
    import perfcounters_t_reg_pkg::*;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}}
) (
  input           clk_i,
  input           rst_ni,

  // Bus Interface
  input  tlul_ot_pkg::tl_h2d_t tl_i,
  output tlul_ot_pkg::tl_d2h_t tl_o,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o

  // Generic IO

  // Interrupts
);

  logic [NumAlerts-1:0] alert_test, alerts;
  perfcounters_t_reg2hw_t reg2hw;
  perfcounters_t_hw2reg_t hw2reg;

  perfcounters_t_reg_top perfcounters_t_reg_top (
  	.clk_i		(clk_i),
  	.rst_ni		(rst_ni),
  	.tl_i		(tl_i),
  	.tl_o		(tl_o),
  // To HW
  	.reg2hw		(reg2hw), // Read
  	.hw2reg		(hw2reg), // Read

  // Integrity check errors
  	.intg_err_o	(),

  // Config
  	.devmode_i	(1'b1) // If 1, explicit error return for unmapped register access
);
  perfcounters_t_core perfcounters_t_core (
    .clk_i	(clk_i),
    .rst_ni	(rst_ni),
    .reg2hw	(reg2hw),
    .hw2reg	(hw2reg)

  );
endmodule
