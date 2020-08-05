# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Generic constraints file for simple testsynthesis flow

# Note that we do not fix hold timing in this flow
set SETUP_CLOCK_UNCERTAINTY 0.5

puts "Applying constraints for top level"

# Note: the netlist does include pads at this level, but not all IO interfaces
# have been properly constrained yet. The clocks are generated inside AST and
# for the purpose of test synthesis, these clock nets are just set to ideal networks.

#####################
# main clock        #
#####################
set MAIN_CLK_PIN ast_wrapper/i_ast/i_prim_clock_buf_sys/*/u_size_only_buf/${DRIVING_CELL_PIN}
set MAIN_RST_PIN IO_RST_N
# target is 100MHz, overconstrain to 125 MHz (+25%)
set MAIN_TCK  8.0
set_ideal_network [get_pins ${MAIN_CLK_PIN}]
set_ideal_network [get_ports ${MAIN_RST_PIN}]

create_clock -name MAIN_CLK -period ${MAIN_TCK} [get_pins ${MAIN_CLK_PIN}]
set_clock_uncertainty ${SETUP_CLOCK_UNCERTAINTY} [get_clocks MAIN_CLK]

#####################
# USB clock         #
#####################
set USB_CLK_PIN ast_wrapper/i_ast/i_prim_clock_buf_usb/*/u_size_only_buf/${DRIVING_CELL_PIN}
# 50MHz
set USB_TCK 20.0
set_ideal_network [get_pins ${USB_CLK_PIN}]

create_clock -name USB_CLK -period ${USB_TCK} [get_pins ${USB_CLK_PIN}]
set_clock_uncertainty ${SETUP_CLOCK_UNCERTAINTY} [get_clocks USB_CLK]

set USB_IN_DEL_FRACTION 0.55
set USB_OUT_DEL_FRACTION 0.55
set USB_IN_DEL    [expr ${USB_IN_DEL_FRACTION} * ${USB_TCK}]
set USB_OUT_DEL   [expr ${USB_OUT_DEL_FRACTION} * ${USB_TCK}]

# constrain dedicated USB IOs
set_input_delay ${USB_IN_DEL} [get_ports USB_P] -clock USB_CLK
set_input_delay ${USB_IN_DEL} [get_ports USB_N] -clock USB_CLK

set_output_delay ${USB_OUT_DEL} [get_ports USB_P] -clock USB_CLK
set_output_delay ${USB_OUT_DEL} [get_ports USB_N] -clock USB_CLK

#####################
# IO clk            #
#####################
set IO_CLK_PIN ast_wrapper/i_ast/i_prim_clock_buf_io/*/u_size_only_buf/${DRIVING_CELL_PIN}
set IO_TCK 8.3333
# target is 96MHz, overconstrain to 120 MHz (+25%)
set_ideal_network [get_pins ${IO_CLK_PIN}]

create_clock -name IO_CLK -period ${IO_TCK} [get_pins ${IO_CLK_PIN}]
set_clock_uncertainty ${SETUP_CLOCK_UNCERTAINTY} [get_clocks IO_CLK]

# generated clocks (div2/div4)
create_generated_clock -name IO_DIV2_CLK -divide_by 2 \
    -source [get_pins top_earlgrey/u_clkmgr_aon/i_prim_clock_buf_io_div2/*/u_size_only_buf/${LOAD_CELL_PIN}] \
    [get_pins top_earlgrey/u_clkmgr_aon/i_prim_clock_buf_io_div2/*/u_size_only_buf/${DRIVING_CELL_PIN}]

create_generated_clock -name IO_DIV4_CLK -divide_by 4 \
    -source [get_pins top_earlgrey/u_clkmgr_aon/i_prim_clock_buf_io_div4/*/u_size_only_buf/${LOAD_CELL_PIN}] \
    [get_pins top_earlgrey/u_clkmgr_aon/i_prim_clock_buf_io_div4/*/u_size_only_buf/${DRIVING_CELL_PIN}]

# TODO: these are dummy constraints and likely incorrect, need to properly constrain min/max
# note that due to the muxing, additional timing views with set_case_analysis may be needed.

# constrain muxed IOs running on IO_DIV2_CLK and IO_DIV4_CLK
set IO_IN_DEL_FRACTION 0.7
set IO_OUT_DEL_FRACTION 0.7

# IO_DIV2_CLK
set IO_DIV2_IN_DEL    [expr ${IO_IN_DEL_FRACTION} * ${IO_TCK} * 2.0]
set IO_DIV2_OUT_DEL   [expr ${IO_OUT_DEL_FRACTION} * ${IO_TCK} * 2.0]

set_input_delay ${IO_DIV2_IN_DEL}   [get_ports IOA*] -clock IO_DIV2_CLK
set_input_delay ${IO_DIV2_IN_DEL}   [get_ports IOB*] -clock IO_DIV2_CLK
set_input_delay ${IO_DIV2_IN_DEL}   [get_ports IOC*] -clock IO_DIV2_CLK
set_input_delay ${IO_DIV2_IN_DEL}   [get_ports IOR*] -clock IO_DIV2_CLK

set_output_delay ${IO_DIV2_OUT_DEL} [get_ports IOA*] -clock IO_DIV2_CLK
set_output_delay ${IO_DIV2_OUT_DEL} [get_ports IOB*] -clock IO_DIV2_CLK
set_output_delay ${IO_DIV2_OUT_DEL} [get_ports IOC*] -clock IO_DIV2_CLK
set_output_delay ${IO_DIV2_OUT_DEL} [get_ports IOR*] -clock IO_DIV2_CLK

# IO_DIV4_CLK
set IO_DIV4_IN_DEL    [expr ${IO_IN_DEL_FRACTION} * ${IO_TCK} * 4.0]
set IO_DIV4_OUT_DEL   [expr ${IO_OUT_DEL_FRACTION} * ${IO_TCK} * 4.0]

set_input_delay ${IO_DIV4_IN_DEL}   [get_ports IOA*] -clock IO_DIV4_CLK
set_input_delay ${IO_DIV4_IN_DEL}   [get_ports IOB*] -clock IO_DIV4_CLK
set_input_delay ${IO_DIV4_IN_DEL}   [get_ports IOC*] -clock IO_DIV4_CLK
set_input_delay ${IO_DIV4_IN_DEL}   [get_ports IOR*] -clock IO_DIV4_CLK

set_output_delay ${IO_DIV4_OUT_DEL} [get_ports IOA*] -clock IO_DIV4_CLK
set_output_delay ${IO_DIV4_OUT_DEL} [get_ports IOB*] -clock IO_DIV4_CLK
set_output_delay ${IO_DIV4_OUT_DEL} [get_ports IOC*] -clock IO_DIV4_CLK
set_output_delay ${IO_DIV4_OUT_DEL} [get_ports IOR*] -clock IO_DIV4_CLK

#####################
# AON clk (300kHz)  #
#####################
set AON_CLK_PIN ast_wrapper/i_ast/i_prim_clock_buf_aon/*/u_size_only_buf/${DRIVING_CELL_PIN}
set AON_TCK 3333.0
set_ideal_network [get_pins ${AON_CLK_PIN}]

create_clock -name AON_CLK -perio ${AON_TCK} [get_pins ${AON_CLK_PIN}]
set_clock_uncertainty ${SETUP_CLOCK_UNCERTAINTY} [get_clocks AON_CLK]

#####################
# JTAG clock        #
#####################
# TODO: set up constraints for JTAG. this may need additional views with set_case_analysis

#####################
# SPI DEV clock     #
#####################
set SPI_DEV_CLK_PIN SPI_DEV_CLK
# 62.5MHz
set SPI_DEV_TCK 16.0
set_ideal_network ${SPI_DEV_CLK_PIN}

## TODO: Create generated clock for negedge SPI_DEV_CLK. Then make them clock group
create_clock -name SPI_DEV_CLK  -period ${SPI_DEV_TCK} [get_ports ${SPI_DEV_CLK_PIN}]
set_clock_uncertainty ${SETUP_CLOCK_UNCERTAINTY} [get_clocks SPI_DEV_CLK]

## TODO: these are dummy constraints and likely incorrect, need to properly constrain min/max
set SPI_DEV_IN_DEL_FRACTION 0.7
set SPI_DEV_OUT_DEL_FRACTION 0.7
set SPI_DEV_IN_DEL    [expr ${SPI_DEV_IN_DEL_FRACTION} * ${SPI_DEV_TCK}]
set SPI_DEV_OUT_DEL   [expr ${SPI_DEV_OUT_DEL_FRACTION} * ${SPI_DEV_TCK}]

# this is an input only port
set_input_delay ${SPI_DEV_IN_DEL} [get_ports SPI_DEV_CS_L] -clock SPI_DEV_CLK
# bidir ports
set_input_delay ${SPI_DEV_IN_DEL} [get_ports SPI_DEV_D0]   -clock SPI_DEV_CLK
set_input_delay ${SPI_DEV_IN_DEL} [get_ports SPI_DEV_D1]   -clock SPI_DEV_CLK
set_input_delay ${SPI_DEV_IN_DEL} [get_ports SPI_DEV_D2]   -clock SPI_DEV_CLK
set_input_delay ${SPI_DEV_IN_DEL} [get_ports SPI_DEV_D3]   -clock SPI_DEV_CLK

set_output_delay ${SPI_DEV_OUT_DEL} [get_ports SPI_DEV_D0]   -clock SPI_DEV_CLK
set_output_delay ${SPI_DEV_OUT_DEL} [get_ports SPI_DEV_D1]   -clock SPI_DEV_CLK
set_output_delay ${SPI_DEV_OUT_DEL} [get_ports SPI_DEV_D2]   -clock SPI_DEV_CLK
set_output_delay ${SPI_DEV_OUT_DEL} [get_ports SPI_DEV_D3]   -clock SPI_DEV_CLK

#####################
# SPI HOST clock   #
#####################
set SPI_HOST_CLK_PIN SPI_HOST_CLK
# 62.5MHz
set SPI_HOST_TCK 16.0
set_ideal_network ${SPI_HOST_CLK_PIN}

create_clock -name SPI_HOST_CLK  -period ${SPI_HOST_TCK} [get_ports ${SPI_HOST_CLK_PIN}]
set_clock_uncertainty ${SETUP_CLOCK_UNCERTAINTY} [get_clocks SPI_HOST_CLK]

## TODO: Create generated clock for negedge SPI_HOST_CLK. Then make them clock group

## TODO: these are dummy constraints and likely incorrect, need to properly constrain min/max
set SPI_HOST_IN_DEL_FRACTION 0.7
set SPI_HOST_OUT_DEL_FRACTION 0.7
set SPI_HOST_IN_DEL    [expr ${SPI_HOST_IN_DEL_FRACTION} * ${SPI_HOST_TCK}]
set SPI_HOST_OUT_DEL   [expr ${SPI_HOST_OUT_DEL_FRACTION} * ${SPI_HOST_TCK}]

# bidir ports
set_input_delay ${SPI_HOST_IN_DEL} [get_ports SPI_HOST_CS_L] -clock SPI_HOST_CLK
set_input_delay ${SPI_HOST_IN_DEL} [get_ports SPI_HOST_D0]   -clock SPI_HOST_CLK
set_input_delay ${SPI_HOST_IN_DEL} [get_ports SPI_HOST_D1]   -clock SPI_HOST_CLK
set_input_delay ${SPI_HOST_IN_DEL} [get_ports SPI_HOST_D2]   -clock SPI_HOST_CLK
set_input_delay ${SPI_HOST_IN_DEL} [get_ports SPI_HOST_D3]   -clock SPI_HOST_CLK

set_output_delay ${SPI_HOST_OUT_DEL} [get_ports SPI_HOST_CS_L] -clock SPI_HOST_CLK
set_output_delay ${SPI_HOST_OUT_DEL} [get_ports SPI_HOST_D0]   -clock SPI_HOST_CLK
set_output_delay ${SPI_HOST_OUT_DEL} [get_ports SPI_HOST_D1]   -clock SPI_HOST_CLK
set_output_delay ${SPI_HOST_OUT_DEL} [get_ports SPI_HOST_D2]   -clock SPI_HOST_CLK
set_output_delay ${SPI_HOST_OUT_DEL} [get_ports SPI_HOST_D3]   -clock SPI_HOST_CLK

#####################
# SPI passthrough   #
#####################

# input pad + internal + output pad
set TPAD_I 1.2
set THODI  2.0
set TPAD_O 3.3
set SPI_HODI_PASS_MAX_DELAY [expr ${TPAD_I} + ${THODI} + ${TPAD_O}]
set SPI_HIDO_PASS_MAX_DELAY ${SPI_HODI_PASS_MAX_DELAY}

# TODO: These are strawman constraints and need to be refined.
set_max_delay ${SPI_HODI_PASS_MAX_DELAY} -from [get_ports SPI_DEV_D0]   -to [get_ports SPI_HOST_D0]
set_max_delay ${SPI_HODI_PASS_MAX_DELAY} -from [get_ports SPI_DEV_D1]   -to [get_ports SPI_HOST_D1]
set_max_delay ${SPI_HODI_PASS_MAX_DELAY} -from [get_ports SPI_DEV_D2]   -to [get_ports SPI_HOST_D2]
set_max_delay ${SPI_HODI_PASS_MAX_DELAY} -from [get_ports SPI_DEV_D3]   -to [get_ports SPI_HOST_D3]
set_max_delay ${SPI_HODI_PASS_MAX_DELAY} -from [get_ports SPI_DEV_CS_L] -to [get_ports SPI_HOST_CS_L]

set_max_delay ${SPI_HIDO_PASS_MAX_DELAY} -from [get_ports SPI_HOST_D0] -to [get_ports SPI_DEV_D0]
set_max_delay ${SPI_HIDO_PASS_MAX_DELAY} -from [get_ports SPI_HOST_D1] -to [get_ports SPI_DEV_D1]
set_max_delay ${SPI_HIDO_PASS_MAX_DELAY} -from [get_ports SPI_HOST_D2] -to [get_ports SPI_DEV_D2]
set_max_delay ${SPI_HIDO_PASS_MAX_DELAY} -from [get_ports SPI_HOST_D3] -to [get_ports SPI_DEV_D3]

#####################
# CDC               #
#####################

# this may need some refinement (and max delay / skew needs to be constrained)
set_clock_groups -name group1 -async -group [get_clocks MAIN_CLK     ] \
                                     -group [get_clocks USB_CLK      ] \
                                     -group [get_clocks SPI_DEV_CLK  ] \
                                     -group [get_clocks SPI_HOST_CLK ] \
                                     -group [get_clocks IO_CLK       ] \
                                     -group [get_clocks IO_DIV2_CLK  ] \
                                     -group [get_clocks IO_DIV4_CLK  ] \
                                     -group [get_clocks AON_CLK      ]

# UART loopback path can be considered to be a false path
set_false_path -through [get_pins top_earlgrey/u_uart*/cio_rx_i] -through [get_pins top_earlgrey/u_uart*/cio_tx_o]

# break all timing paths through bidirectional IO buffers (i.e., from output and oe to input buffer output)
set_false_path -through [get_pins *padring/*pad/*/oe_i] -through [get_pins *padring/*pad/*/in_o]
set_false_path -through [get_pins *padring/*pad/*/out_i] -through [get_pins *padring/*pad/*/in_o]

# break path through jtag mux
set_false_path -from [get_ports IOC7] -to [get_ports IOR*]

# pass through is not fully supported yet by SPI host
set_false_path -through [get_pins top_earlgrey/u_spi_host1/u_sck_passthrough/gen_*/u_size_only_mux2/${DRIVING_CELL_PIN}]

#####################
# I/O drive/load    #
#####################

# attach load and drivers to IOs to get a more realistic estimate
set_driving_cell -no_design_rule -lib_cell ${DRIVING_PAD} -pin ${DRIVING_PAD_PIN} [all_inputs]
set_load [load_of ${LOAD_PAD_LIB}/${LOAD_PAD}/${LOAD_PAD_PIN}] [all_outputs]

# set a nonzero critical range to be able to spot the violating paths better
# in the report
set_critical_range 0.5 ${DUT}

###################################
# Size Only and Don't touch Cells #
###################################

# this is for architectural clock buffers, inverters and muxes
set_size_only -all_instances [get_cells -h *u_size_only*] true

# do not touch pad cells
set_dont_touch [get_cells -h *u_pad_macro*]

###########################
# Technology speciifc SDC #
###########################

source foundry.constraints.sdc

puts "Done applying constraints for top level"

##########################################
# Case analysis for quasi-static signals #
##########################################

# assume a value of 0 for the pad attribute at index [9]
set_case_analysis 0 [get_pins u_padring/i_*_pad/attr_i[9]]
set_case_analysis 0 [get_pins u_padring/gen_*_gen_*_i_*_pad/attr_i[9]]
