## Copyright lowRISC contributors.
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0

## Clock Signal
create_clock -add -name sys_clk_pin -period 10.00 -waveform {0 5} [get_ports IO_CLK]

## Clock Domain Crossings
set clks_50_unbuf [get_clocks -of_objects [get_pin clkgen/pll/CLKOUT0]]
set clks_48_unbuf [get_clocks -of_objects [get_pin clkgen/pll/CLKOUT1]]

## Divided clock
## This is not really recommended per Vivado's guidelines, but hopefully these clocks are slow enough and their
## destination flops few enough.

set div2_cell [get_cells top_earlgrey/u_io_div2_div/gen_div2.u_div2/gen_generic.u_impl_generic/q_o_reg[0]]
create_generated_clock -name clk_io_div2 -source [get_pin ${div2_cell}/C] -divide_by 2 [get_pin ${div2_cell}/Q]

set div4_cell [get_cells top_earlgrey/u_clkmgr/u_io_div4_div/gen_div.clk_int_reg]
create_generated_clock -name clk_io_div4 -source [get_pin ${div4_cell}/C] -divide_by 4 [get_pin ${div4_cell}/Q]

set_clock_groups -group ${clks_50_unbuf} -group ${clks_48_unbuf} -group clk_io_div2 -group clk_io_div4 -asynchronous
