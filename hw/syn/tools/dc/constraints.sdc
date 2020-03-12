# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Generic constraints file for simple testsynthesis flow
# This held very simple for now and needs to be refined

# note that we do not fix hold timing in this flow
set SETUP_CLOCK_UNCERTAINTY 0.5

# TODO: consider splitting this into per-IP .sdc files
if {$TOP_ENTITY == "top_earlgrey"} {

puts "Applying constraints for top level"

# note: this does not account for clock insertion delay and
# there are no pads instantiated in the netlist (yet)

#####################
# main clock        #
#####################
set MAIN_CLK_PIN clk_i
set MAIN_RST_PIN rst_ni
# 125 MHz
set MAIN_TCK  8.0
set_ideal_network ${MAIN_CLK_PIN}
set_ideal_network ${MAIN_RST_PIN}

create_clock ${MAIN_CLK_PIN} -period ${MAIN_TCK}
set_clock_uncertainty ${SETUP_CLOCK_UNCERTAINTY}  ${MAIN_CLK_PIN}

set IN_DEL    5.5
set OUT_DEL   5.5

set_input_delay ${IN_DEL} [get_ports mio_in_i*]          -clock ${MAIN_CLK_PIN}
set_input_delay ${IN_DEL} [get_ports scanmode_i]         -clock ${MAIN_CLK_PIN}
set_input_delay ${IN_DEL} [get_ports dio_uart_rx_i]      -clock ${MAIN_CLK_PIN}

set_output_delay ${OUT_DEL} [get_ports mio_out_o*]       -clock ${MAIN_CLK_PIN}
set_output_delay ${OUT_DEL} [get_ports mio_oe_o*]        -clock ${MAIN_CLK_PIN}
set_output_delay ${OUT_DEL} [get_ports dio_uart_tx_o]    -clock ${MAIN_CLK_PIN}
set_output_delay ${OUT_DEL} [get_ports dio_uart_tx_en_o] -clock ${MAIN_CLK_PIN}

#####################
# USB clock         #
#####################
set USB_CLK_PIN clk_usb_48mhz_i
# 50MHz
set USB_TCK 20.0
set_ideal_network ${USB_CLK_PIN}

create_clock ${USB_CLK_PIN} -period ${USB_TCK}
set_clock_uncertainty ${SETUP_CLOCK_UNCERTAINTY} ${USB_CLK_PIN}

set IN_DEL    17.0
set OUT_DEL   17.0

set_input_delay ${IN_DEL} [get_ports dio_usbdev_sense_i]       -clock ${USB_CLK_PIN}
set_input_delay ${IN_DEL} [get_ports dio_usbdev_dp_i]          -clock ${USB_CLK_PIN}
set_input_delay ${IN_DEL} [get_ports dio_usbdev_dn_i]          -clock ${USB_CLK_PIN}

set_output_delay ${OUT_DEL} [get_ports dio_usbdev_pullup_o]    -clock ${USB_CLK_PIN}
set_output_delay ${OUT_DEL} [get_ports dio_usbdev_pullup_en_o] -clock ${USB_CLK_PIN}
set_output_delay ${OUT_DEL} [get_ports dio_usbdev_dp_o]        -clock ${USB_CLK_PIN}
set_output_delay ${OUT_DEL} [get_ports dio_usbdev_dp_en_o]     -clock ${USB_CLK_PIN}
set_output_delay ${OUT_DEL} [get_ports dio_usbdev_dn_o]        -clock ${USB_CLK_PIN}
set_output_delay ${OUT_DEL} [get_ports dio_usbdev_dn_en_o]     -clock ${USB_CLK_PIN}

#####################
# JTAG clock        #
#####################
set JTAG_CLK_PIN jtag_tck_i
set JTAG_RST_PIN jtag_trst_ni
# 40MHz
set JTAG_TCK 25.0
set_ideal_network ${JTAG_CLK_PIN}
set_ideal_network ${JTAG_RST_PIN}

create_clock ${JTAG_CLK_PIN} -period ${JTAG_TCK}
set_clock_uncertainty ${SETUP_CLOCK_UNCERTAINTY} ${JTAG_CLK_PIN}

set IN_DEL    10.0
set OUT_DEL   10.0

set_input_delay ${IN_DEL} [get_ports jtag_tms_i]  -clock ${JTAG_CLK_PIN}
set_input_delay ${IN_DEL} [get_ports jtag_td_i]   -clock ${JTAG_CLK_PIN}

set_output_delay ${OUT_DEL} [get_ports jtag_td_o] -clock ${JTAG_CLK_PIN}

#####################
# SPI clock         #
#####################
set SPI_CLK_PIN dio_spi_device_sck_i
# 62.5MHz
set SPI_TCK 16.0
set_ideal_network ${SPI_CLK_PIN}

create_clock ${SPI_CLK_PIN} -period ${SPI_TCK}
set_clock_uncertainty ${SETUP_CLOCK_UNCERTAINTY} ${SPI_CLK_PIN}

set IN_DEL    6.0
set OUT_DEL   6.0

set_input_delay ${IN_DEL} [get_ports dio_spi_device_csb_i]       -clock ${SPI_CLK_PIN}
set_input_delay ${IN_DEL} [get_ports dio_spi_device_mosi_i]      -clock ${SPI_CLK_PIN}

set_output_delay ${OUT_DEL} [get_ports dio_spi_device_miso_o]    -clock ${SPI_CLK_PIN}
set_output_delay ${OUT_DEL} [get_ports dio_spi_device_miso_en_o] -clock ${SPI_CLK_PIN}

#####################
# CDC               #
#####################

# this may need some refinement (and max delay / skew needs to be constrained)
set_clock_groups -name group1 -async -group ${MAIN_CLK_PIN} \
                                     -group ${JTAG_CLK_PIN} \
                                     -group ${USB_CLK_PIN}  \
                                     -group ${SPI_CLK_PIN}

# loopback path can be considered to be a false path
set_false_path -from dio_uart_rx_i -to dio_uart_tx_o

} else {

#####################
# main clock        #
#####################
set MAIN_CLK_PIN clk_i
set MAIN_RST_PIN rst_ni
# set main clock to 125 MHz
set MAIN_TCK  8.0
set_ideal_network ${MAIN_CLK_PIN}
set_ideal_network ${MAIN_RST_PIN}
set_clock_uncertainty ${SETUP_CLOCK_UNCERTAINTY} ${MAIN_CLK_PIN}

# other timing constraint in ns
set IN_DEL    1.0
set OUT_DEL   1.0
set DELAY     ${MAIN_TCK}

create_clock ${MAIN_CLK_PIN} -period ${MAIN_TCK}

# in to out
set_max_delay ${DELAY} -from [all_inputs] -to [all_outputs]
# in to reg / reg to out
set_input_delay ${IN_DEL} [remove_from_collection [all_inputs] {${MAIN_CLK_PIN}}] -clock ${MAIN_CLK_PIN}
set_output_delay ${OUT_DEL}  [all_outputs] -clock ${MAIN_CLK_PIN}

}

#####################
# Common            #
#####################

# attach load and drivers to IOs to get a more realistic estimate
set_driving_cell  -no_design_rule -lib_cell ${driving_cell} -pin X [all_inputs]
set_load [load_of ${load_lib}/${load_cell}/A] [all_outputs]

# set a nonzero critical range to be able to spot the violating paths better
# in the report
set_critical_range 0.5 ${TOP_ENTITY}
