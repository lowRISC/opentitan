## Copyright lowRISC contributors.
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0

## Clock Signal
create_clock -add -name sys_clk_pin -period 10.00 -waveform {0 5} [get_ports IO_CLK]

## Clock Domain Crossings
set clks_10_unbuf [get_clocks -of_objects [get_pin clkgen/pll/CLKOUT0]]
set clks_48_unbuf [get_clocks -of_objects [get_pin clkgen/pll/CLKOUT1]]
set clks_aon_unbuf [get_clocks -of_objects [get_pin clkgen/pll/CLKOUT2]]

## Divided clock
## This is not really recommended per Vivado's guidelines, but hopefully these clocks are slow enough and their
## destination flops few enough.

set u_pll clkgen/pll
set u_div2 top_*/u_clkmgr_aon/u_no_scan_io_div2_div
create_generated_clock -name clk_io_div2 -source [get_pin ${u_pll}/CLKOUT0] -divide_by 2 [get_pin ${u_div2}/u_clk_div_buf/gen_xilinx.u_impl_xilinx/bufg_i/O]

set u_div4 top_*/u_clkmgr_aon/u_no_scan_io_div4_div
create_generated_clock -name clk_io_div4 -source [get_pin ${u_pll}/CLKOUT0] -divide_by 4 [get_pin ${u_div4}/u_clk_div_buf/gen_xilinx.u_impl_xilinx/bufg_i/O]

## JTAG and SPI clocks
create_clock -add -name lc_jtag_tck -period 100.00 -waveform {0 5} [get_pin top_*/u_pinmux_aon/u_pinmux_strap_sampling/u_pinmux_jtag_buf_lc/prim_clock_buf_tck/gen_xilinx.u_impl_xilinx/bufg_i/O]
create_clock -add -name rv_jtag_tck -period 100.00 -waveform {0 5} [get_pin top_*/u_pinmux_aon/u_pinmux_strap_sampling/u_pinmux_jtag_buf_rv/prim_clock_buf_tck/gen_xilinx.u_impl_xilinx/bufg_i/O]
create_clock -add -name clk_spi_in  -period 100.00 -waveform {0 5} [get_pin top_*/u_spi_device/u_clk_spi_in_buf/gen_xilinx.u_impl_xilinx/bufg_i/O]
create_clock -add -name clk_spi_out -period 100.00 -waveform {0 5} [get_pin top_*/u_spi_device/u_clk_spi_out_buf/gen_xilinx.u_impl_xilinx/bufg_i/O]

set_clock_groups -group ${clks_10_unbuf} -group ${clks_48_unbuf} -group ${clks_aon_unbuf} -group clk_io_div2 -group clk_io_div4 -group lc_jtag_tck -group rv_jtag_tck -group clk_spi_in -group clk_spi_out -asynchronous

