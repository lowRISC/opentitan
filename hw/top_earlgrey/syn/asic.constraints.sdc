# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Generic constraints file for simple testsynthesis flow

# note that we do not fix hold timing in this flow
set SETUP_CLOCK_UNCERTAINTY 0.5

puts "Applying constraints for top level"

# note: this does not account for clock insertion delay and
# there are no pads instantiated in the netlist (yet)

#####################
# DIO pin mapping   #
#####################
set PORT_SPI_DEVICE_SCK 14
set PORT_SPI_DEVICE_CSB 13
set PORT_SPI_DEVICE_MOSI 12
set PORT_SPI_DEVICE_MISO 11

set PORT_UART_RX 10
set PORT_UART_TX 9

set PORT_USBDEV_SENSE 8
set PORT_USBDEV_SE0 7
set PORT_USBDEV_DP_PULLUP 6
set PORT_USBDEV_DN_PULLUP 5
set PORT_USBDEV_TX_MODE_SE 4
set PORT_USBDEV_SUSPEND 3
set PORT_USBDEV_D 2
set PORT_USBDEV_DP 1
set PORT_USBDEV_DN 0

#####################
# main clock        #
#####################
set MAIN_CLK_PIN ast_base_clks.clk_sys
set MAIN_RST_PIN rst_n
# 125 MHz
set MAIN_TCK  8.0
set_ideal_network ${MAIN_CLK_PIN}
set_ideal_network ${MAIN_RST_PIN}

create_clock -name MAIN_CLK -period ${MAIN_TCK} [get_pins ${MAIN_CLK_PIN}]
set_clock_uncertainty ${SETUP_CLOCK_UNCERTAINTY} [get_clocks MAIN_CLK]

# TODO: generated clock
# TODO: clock gating setup/hold


set IN_DEL    5.5
set OUT_DEL   5.5

# Doesn't need
#set_input_delay ${IN_DEL} [get_ports scanmode_i] -clock MAIN_CLK

#####################
# USB clock         #
#####################
set USB_CLK_PIN ast_base_clks.clk_usb
# 50MHz
set USB_TCK 20.0
set_ideal_network ${USB_CLK_PIN}

create_clock -name USB_CLK -period ${USB_TCK} [get_pins ${USB_CLK_PIN}]
set_clock_uncertainty ${SETUP_CLOCK_UNCERTAINTY} [get_clocks USB_CLK]

set IN_DEL    17.0
set OUT_DEL   17.0

set_input_delay ${IN_DEL} [get_ports dio_in_i[$PORT_USBDEV_SENSE]]       -clock USB_CLK
set_input_delay ${IN_DEL} [get_ports dio_in_i[$PORT_USBDEV_DP]]          -clock USB_CLK
set_input_delay ${IN_DEL} [get_ports dio_in_i[$PORT_USBDEV_DN]]          -clock USB_CLK

set_output_delay ${OUT_DEL} [get_ports dio_out_o[$PORT_USBDEV_DP_PULLUP]] -clock USB_CLK
set_output_delay ${OUT_DEL} [get_ports dio_oe_o[$PORT_USBDEV_DP_PULLUP]]  -clock USB_CLK
set_output_delay ${OUT_DEL} [get_ports dio_out_o[$PORT_USBDEV_DN_PULLUP]] -clock USB_CLK
set_output_delay ${OUT_DEL} [get_ports dio_oe_o[$PORT_USBDEV_DN_PULLUP]]  -clock USB_CLK
set_output_delay ${OUT_DEL} [get_ports dio_out_o[$PORT_USBDEV_DP]]        -clock USB_CLK
set_output_delay ${OUT_DEL} [get_ports dio_oe_o[$PORT_USBDEV_DP]]         -clock USB_CLK
set_output_delay ${OUT_DEL} [get_ports dio_out_o[$PORT_USBDEV_DN]]        -clock USB_CLK
set_output_delay ${OUT_DEL} [get_ports dio_oe_o[$PORT_USBDEV_DN]]         -clock USB_CLK

#####################
# IO clk (24MHz)    #
#####################
set IO_CLK_PIN ast_base_clks.clk_io
set IO_TCK 40.0
set_ideal_network ${IO_CLK_PIN}

create_clock -name IO_CLK -period ${IO_TCK} [get_pins ${IO_CLK_PIN}]
set_clock_uncertainty ${SETUP_CLOCK_UNCERTAINTY} [get_clocks IO_CLK]

# TODO: generated clock
# TODO: clock gating setup/hold

set IN_DEL  20.0
set OUT_DEL 20.0

set_input_delay ${IN_DEL} [get_ports mio_in_i*]          -clock IO_CLK

set_output_delay ${OUT_DEL} [get_ports mio_out_o*]       -clock IO_CLK
set_output_delay ${OUT_DEL} [get_ports mio_oe_o*]        -clock IO_CLK

# UART RX
set_input_delay ${IN_DEL} [get_ports dio_in_i[$PORT_UART_RX]]      -clock IO_CLK

# UART TX
set_output_delay ${OUT_DEL} [get_ports dio_out_o[$PORT_UART_TX]]    -clock IO_CLK
set_output_delay ${OUT_DEL} [get_ports dio_oe_o[$PORT_UART_TX]]     -clock IO_CLK

#####################
# AON clk (300kHz)  #
#####################
set AON_CLK_PIN ast_base_clks.clk_aon
set AON_TCK 3333.0
set_ideal_network ${AON_CLK_PIN}

create_clock -name AON_CLK -perio ${AON_TCK} [get_pins ${AON_CLK_PIN}]
set_clock_uncertainty ${SETUP_CLOCK_UNCERTAINTY} [get_clocks AON_CLK]

# use same IO IN/OUT delay

#####################
# JTAG clock        #
#####################
set JTAG_CLK_PIN jtag_tck
set JTAG_RST_PIN jtag_trst_n
# 40MHz
set JTAG_TCK 25.0
set_ideal_network ${JTAG_CLK_PIN}
set_ideal_network ${JTAG_RST_PIN}

create_clock -name JTAG_CLK -period ${JTAG_TCK} [get_pins ${JTAG_CLK_PIN}]
set_clock_uncertainty ${SETUP_CLOCK_UNCERTAINTY} [get_clocks JTAG_CLK]

set IN_DEL    10.0
set OUT_DEL   10.0

set JTAG_TMS_PIN IO_DPS3
set JTAG_TDI_PIN IO_DPS1
set JTAG_TDO_PIN IO_DPS2
set_input_delay ${IN_DEL} [get_ports IO_DPS3]  -clock JTAG_CLK
set_input_delay ${IN_DEL} [get_ports IO_DPS1]   -clock JTAG_CLK

set_output_delay ${OUT_DEL} [get_ports IO_DPS2] -clock JTAG_CLK

#####################
# SPI clock         #
#####################
set SPI_CLK_PIN dio_in_i[$PORT_SPI_DEVICE_SCK]
# 62.5MHz
set SPI_TCK 16.0
set_ideal_network ${SPI_CLK_PIN}

create_clock -name SPID_CLK  -period ${SPI_TCK} [get_ports ${SPI_CLK_PIN}]
set_clock_uncertainty ${SETUP_CLOCK_UNCERTAINTY} [get_clocks SPID_CLK]

## TODO: Create generated clock for negedge SPID_CLK. Then make them clock group

set IN_DEL    6.0
set OUT_DEL   6.0

set_input_delay ${IN_DEL} [get_ports dio_in_i[$PORT_SPI_DEVICE_CSB]]     -clock SPID_CLK
set_input_delay ${IN_DEL} [get_ports dio_in_i[$PORT_SPI_DEVICE_MOSI]]    -clock SPID_CLK

set_output_delay ${OUT_DEL} [get_ports dio_out_o[$PORT_SPI_DEVICE_MISO]] -clock SPID_CLK
set_output_delay ${OUT_DEL} [get_ports dio_oe_o[$PORT_SPI_DEVICE_MISO]]  -clock SPID_CLK

#####################
# CDC               #
#####################

# this may need some refinement (and max delay / skew needs to be constrained)
set_clock_groups -name group1 -async -group [get_clocks MAIN_CLK] \
                                     -group [get_clocks JTAG_CLK] \
                                     -group [get_clocks USB_CLK ] \
                                     -group [get_clocks SPID_CLK] \
                                     -group [get_clocks IO_CLK  ] \
                                     -group [get_clocks AON_CLK ]

# UART loopback path can be considered to be a false path
#set_false_path -from top_earlgrey/dio_in_i[$PORT_UART_RX] -to top_earlgrey/dio_out_o[$PORT_UART_TX]
set_false_path -through [get_ports top_earlgrey/u_uart*/cio_rx_i] -through [get_ports top_earlgrey/u_uart*/cio_tx_o]

#####################
# I/O drive/load    #
#####################

# attach load and drivers to IOs to get a more realistic estimate
set_driving_cell  -no_design_rule -lib_cell ${DRIVING_CELL} -pin X [all_inputs]
set_load [load_of ${LOAD_LIB}/${LOAD_CELL}/A] [all_outputs]

# set a nonzero critical range to be able to spot the violating paths better
# in the report
set_critical_range 0.5 ${DUT}

#####################
# Size Only Cells   #
#####################

set_size_only -all_instances [get_cells -h *u_size_only*] true

puts "Done applying constraints for top level"
