// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: UART core module
//

module perfcounters_t_core (
  input                  clk_i,
  input                  rst_ni,

  input  perfcounters_t_reg_pkg::perfcounters_t_reg2hw_t reg2hw,
  output perfcounters_t_reg_pkg::perfcounters_t_hw2reg_t hw2reg

);
  import perfcounters_t_reg_pkg::*;

  perfcounters_t_event perfcounters_t_event (
  	.clk_i	(clk_i),
  	.rst_ni	(rst_ni),

  	.reg2hw	(reg2hw),
  	.hw2reg	(hw2reg)

   );

endmodule
