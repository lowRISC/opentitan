## Copyright lowRISC contributors.
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0

## Clock Signal
create_clock -add -name sys_clk_pin -period 10.00 -waveform {0 5} [get_ports IO_CLK]

## Clock Domain Crossings
set clks_10_unbuf [get_clocks -of_objects [get_pin clkgen/pll/CLKOUT0]]
set clks_48_unbuf [get_clocks -of_objects [get_pin clkgen/pll/CLKOUT1]]
set clks_aon_unbuf [get_clocks -of_objects [get_pin clkgen/pll/CLKOUT4]]

## Divided clock
## This is not really recommended per Vivado's guidelines, but hopefully these clocks are slow enough and their
## destination flops few enough.

set u_pll clkgen/pll
set u_div2 top_*/u_clkmgr_aon/u_no_scan_io_div2_div
create_generated_clock -name clk_io_div2 -source [get_pin ${u_pll}/CLKOUT0] -divide_by 2 [get_pin ${u_div2}/u_clk_div_buf/gen_xilinx.u_impl_xilinx/gen_fpga_buf.gen_bufg.bufg_i/O]

# TODO uncomment below line and integrate u_div4 in path to make constraint more generic
# set u_div4 top_*/u_clkmgr_aon/u_no_scan_io_div4_div
create_generated_clock -name clk_io_div4 -divide_by 4 -source [get_pins top_earlgrey/u_clkmgr_aon/u_no_scan_io_div4_div/gen_div.clk_int_reg/C] [get_pins top_earlgrey/u_clkmgr_aon/u_no_scan_io_div4_div/gen_div.clk_int_reg/Q]

# the step-down mux is implemented with a LUT right now and the mux switches on the falling edge.
# therefore, Vivado propagates both clock edges down the clock network.
# this implementation is not ideal - but we can at least tell Vivado to only honour the rising edge for
# timing analysis.
set_clock_sense -positive \
  [get_pins -filter {DIRECTION == OUT && IS_LEAF} -of_objects \
    [get_nets -segments -of_objects \
      [get_pins top_*/u_clkmgr_aon/u_no_scan_io_div2_div/u_clk_div_buf/gen_xilinx.u_impl_xilinx/gen_fpga_buf.bufg_i/I] \
    ] \
  ]

## JTAG clocks and I/O delays
# Create clocks for the various TAPs.
create_clock -add -name jtag_tck -period 100.00 -waveform {0 50} [get_ports IOR3]
create_generated_clock -name lc_jtag_tck -source [get_ports IOR3] -divide_by 1 [get_pin top_*/u_pinmux_aon/u_pinmux_strap_sampling/u_pinmux_jtag_buf_lc/prim_clock_buf_tck/gen_xilinx.u_impl_xilinx/gen_fpga_buf.gen_bufg.bufg_i/O]
create_generated_clock -name rv_jtag_tck -source [get_ports IOR3] -divide_by 1 [get_pin top_*/u_pinmux_aon/u_pinmux_strap_sampling/u_pinmux_jtag_buf_rv/prim_clock_buf_tck/gen_xilinx.u_impl_xilinx/gen_fpga_buf.gen_bufg.bufg_i/O]

set lc_jtag_tck_inv_pin  \
  [get_pins -filter {DIRECTION == OUT && IS_LEAF} -of_objects \
    [get_nets -segments -of_objects \
      [get_pins top_earlgrey/u_pinmux_aon/u_pinmux_strap_sampling/u_pinmux_jtag_buf_rv/prim_clock_buf_tck/gen_xilinx.u_impl_xilinx/gen_fpga_buf.gen_bufg.bufg_i/I]]]
set rv_jtag_tck_inv_pin  \
  [get_pins -filter {DIRECTION == OUT && IS_LEAF} -of_objects \
    [get_nets -segments -of_objects \
      [get_pins top_earlgrey/u_pinmux_aon/u_pinmux_strap_sampling/u_pinmux_jtag_buf_rv/prim_clock_buf_tck/gen_xilinx.u_impl_xilinx/gen_fpga_buf.gen_bufg.bufg_i/I]]]

set_clock_sense -negative ${lc_jtag_tck_inv_pin}
set_clock_sense -negative ${rv_jtag_tck_inv_pin}

# Assign input and output delays.
# Note that incidental combinatorial paths through the pinmux do not get removed
# from timing below, but the half cycle timing for JTAG leaves a fairly generous
# requirement. If the JTAG constraints need to be tightened and overly constrain
# the combinational port-to-port paths,
#   set_max_delay -datapath_only
# may be used to apply timing exceptions for those paths.
# However, remember that the input and output delays contribute to the path
# delay for such a case, so the constraint value for set_max_delay must
# accommodate them. In other words, for the constraint
#   set_max_delay -datapath_only -from [get_ports] -through ${combo_path_pin} \
#                 -to [get_ports] ${max_delay_value}
# ${max_delay_value} =
#     ${max_input_delay} + ${max_output_delay} + ${max_port_to_port_delay}
set_output_delay -add_delay -clock_fall -clock jtag_tck -max 10.0 [get_ports IOR1]
set_output_delay -add_delay -clock_fall -clock jtag_tck -min -5.0 [get_ports IOR1]
set_input_delay  -add_delay -clock_fall -clock jtag_tck -min  0.0 [get_ports {IOR0 IOR2}]
set_input_delay  -add_delay -clock_fall -clock jtag_tck -max 15.0 [get_ports {IOR0 IOR2}]

## SPI clocks
create_clock -add -name clk_spi  -period 100.00 -waveform {0 50} [get_ports SPI_DEV_CLK]
set_input_delay -clock clk_spi 5 [get_ports SPI_DEV_D0]
set_input_delay -clock clk_spi 5 [get_ports SPI_DEV_D1]
set_output_delay -clock clk_spi 5 [get_ports SPI_DEV_D0] -add_delay
set_output_delay -clock clk_spi 5 [get_ports SPI_DEV_D1] -add_delay

# set clock sense on the input to spi buffers to help the tool understand the clocks are shifted versions of each other
# This can also be accomplished through create_genearted_clocks.

## set clock sense approach
##set_clock_sense -negative \
##  [get_pins -filter {DIRECTION == OUT && IS_LEAF} -of_objects \
##    [get_nets -segments -of_objects \
##      [get_pins top_*/u_spi_device/gen_fpga_buf.gen_bufr.bufr_i_i_1/I] \
##    ] \
##  ] \
##  -clocks clk_spi
##
##set_clock_sense -positive \
##  [get_pins -filter {DIRECTION == OUT && IS_LEAF} -of_objects \
##    [get_nets -segments -of_objects \
##      [get_pins top_*/u_spi_device/gen_fpga_buf.gen_bufr.bufr_i_i_1__0/I] \
##    ] \
##  ] \
##  -clocks clk_spi

## create_generated_clock appraoch
## create_generated_clock is preferred since the buffer cell used here is hand-instantiated, while the set_clock_sense point is simply a LUT
create_generated_clock -name clk_spi_in  -divide_by 1 -source [get_ports SPI_DEV_CLK] [get_pins top_*/u_spi_device/u_clk_spi_in_buf/gen_xilinx.u_impl_xilinx/gen_fpga_buf.gen_bufr.bufr_i/O]
create_generated_clock -name clk_spi_out -divide_by 1 -source [get_ports SPI_DEV_CLK] [get_pins top_*/u_spi_device/u_clk_spi_out_buf/gen_xilinx.u_impl_xilinx/gen_fpga_buf.gen_bufr.bufr_i/O] -invert

## Set asynchronous clock groups
set_clock_groups -group ${clks_10_unbuf} -group ${clks_48_unbuf} -group ${clks_aon_unbuf} -group clk_io_div2 -group clk_io_div4 -group [get_clocks -include_generated_clocks jtag_tck] -group {clk_spi clk_spi_in clk_spi_out} -group sys_clk_pin -asynchronous

## The usb calibration handling inside ast is assumed to be async to the outside world
## even though its interface is also a usb clock.
set_false_path -from ${clks_48_unbuf} -to [get_pins u_ast/u_usb_clk/u_ref_pulse_sync/u_sync*/u_sync_1/gen_*/q_o_reg[0]/D]
