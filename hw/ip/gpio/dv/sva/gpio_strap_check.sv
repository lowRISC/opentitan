// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"
import gpio_env_pkg::*;

module gpio_strap_check

(
		input logic               	clk_i,
		input logic               	rst_ni,
		input logic               	strap_en_i,
		input logic               	strap_valid,
		input logic [NUM_GPIOS-1:0] strap_data,
		input logic [NUM_GPIOS-1:0] gpio_i
 );

		// Check if when a strap_en_i is high,
 		// one clock cycle after it must have a valid signal high.
		`ASSERT(strap_valid_assert,
 						strap_en_i |=> strap_valid,
						clk_i, !rst_ni);
		// Check if strap output data is mirrored from gpio_i input data,
		// one clock cycle after the strap_en is high.
  	`ASSERT(strap_data_assert,
						strap_en_i && !strap_valid |=> strap_data == $past(gpio_i),
						clk_i, !rst_ni);

endmodule
