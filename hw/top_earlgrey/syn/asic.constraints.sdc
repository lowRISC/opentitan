# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Generic constraints file for simple testsynthesis flow

# Note that we do not fix hold timing in this flow
set SETUP_CLOCK_UNCERTAINTY 0.5
set CLK_PERIOD_FACTOR 0.95 ;# clock period over constraining factor
puts "Applying constraints for top level"

# Note: the netlist does include pads at this level, but not all IO interfaces
# have been properly constrained yet. The clocks are generated inside AST and
# for the purpose of test synthesis, these clock nets are just set to ideal networks.

#####################
# Architectural CGs #
#####################

# in synthesis, we treat all clock networks as ideal nets.
# architecturally insterted CGs however can be interpreted as
# sequential cells by the tool, hence stopping automatic propagation
# of ideal network attributes. therefore, we go through the design and
# declare all architectural CG outputs as ideal.
set_ideal_network [get_pins -hier u_clkgate/Q]

#####################
# main clock        #
#####################
set MAIN_CLK_PIN u_ast/u_sys_clk/u_sys_osc/u_buf/out_o
set MAIN_RST_PIN IO_RST_N
# target is 100MHz, overconstrain by factor
set MAIN_TCK_TARGET_PERIOD  10
set MAIN_TCK_FACTOR 0.85
set MAIN_TCK_PERIOD [expr $MAIN_TCK_TARGET_PERIOD*$MAIN_TCK_FACTOR] ;# over constraining
# For now we remove this as clock is, by default, ideal. Reset, we'll try w/o ideal_network.
#set_ideal_network [get_pins ${MAIN_CLK_PIN}]
#set_ideal_network [get_ports ${MAIN_RST_PIN}]

create_clock -name MAIN_CLK -period ${MAIN_TCK_PERIOD} [get_pins ${MAIN_CLK_PIN}]
set_clock_uncertainty ${SETUP_CLOCK_UNCERTAINTY} [get_clocks MAIN_CLK]

#####################
# USB clock         #
#####################
set USB_CLK_PIN u_ast/u_usb_clk/u_usb_osc/u_buf/out_o
# target is 48MHz, overconstrain by 5%
set USB_TCK_TARGET_PERIOD 20.8
set USB_TCK_PERIOD [expr $USB_TCK_TARGET_PERIOD*$CLK_PERIOD_FACTOR]
#set_ideal_network [get_pins ${USB_CLK_PIN}]

create_clock -name USB_CLK -period ${USB_TCK_PERIOD} [get_pins ${USB_CLK_PIN}]
set_clock_uncertainty ${SETUP_CLOCK_UNCERTAINTY} [get_clocks USB_CLK]

set_max_delay 3 -from [get_ports USB_N] -to [get_pins top_earlgrey/u_usbdev/i_usbdev_iomux/cdc_io_to_usb/gen_*u_impl_*/u_sync_1/gen_*u_impl*/gen_flops[2]*.u_size_only_reg/D]
set_max_delay 3 -from [get_ports USB_P] -to [get_pins top_earlgrey/u_usbdev/i_usbdev_iomux/cdc_io_to_usb/gen_*u_impl_*/u_sync_1/gen_*u_impl*/gen_flops[3]*.u_size_only_reg/D]
set_max_delay 3 -from [get_ports USB_*] -to [get_pins top_earlgrey/u_usbdev/i_usbdev_iomux/cdc_io_to_usb/gen_*u_impl_*/u_sync_1/gen_*u_impl*/gen_flops[1]*.u_size_only_reg/D]
set_max_delay 3 -from [get_pins top_earlgrey/u_usbdev/usbdev_impl/u_usb_fs_nb_pe/u_usb_fs_tx/usb_d_q_reg/Q] -to [get_ports USB_*]
set_max_delay 3 -from [get_pins top_earlgrey/u_usbdev/usbdev_impl/u_usb_fs_nb_pe/u_usb_fs_tx/oe_q_reg/Q] -to [get_ports USB_*]
#####################
# IO clk            #
#####################
set IO_CLK_PIN u_ast/u_io_clk/u_io_osc/u_buf/out_o
# target is 96MHz, overconstrain by factor
set IO_TCK_TARGET_PERIOD 10.416
set IO_TCK_PERIOD [expr $IO_TCK_TARGET_PERIOD*$CLK_PERIOD_FACTOR]

create_clock -name IO_CLK -period ${IO_TCK_PERIOD} [get_pins ${IO_CLK_PIN}]
set_clock_uncertainty ${SETUP_CLOCK_UNCERTAINTY} [get_clocks IO_CLK]

# generated clocks (div2/div4)
create_generated_clock -name IO_DIV2_CLK -divide_by 2 \
    -source [get_pins top_earlgrey/u_clkmgr_aon/u_no_scan_io_div2_div/u_clk_mux/gen_*u_impl*/u_size_only_mux2/D1] \
    [get_pins top_earlgrey/u_clkmgr_aon/u_no_scan_io_div2_div/u_clk_mux/gen_*u_impl*/u_size_only_inv/${DRIVING_CELL_PIN}]

create_generated_clock -name IO_DIV4_CLK -divide_by 4 \
    -source [get_pins top_earlgrey/u_clkmgr_aon/u_no_scan_io_div4_div/u_clk_mux/gen_*u_impl*/u_size_only_mux2/D1] \
    [get_pins top_earlgrey/u_clkmgr_aon/u_no_scan_io_div4_div/u_clk_mux/gen_*u_impl*/u_size_only_inv/${DRIVING_CELL_PIN}]

# TODO: these are dummy constraints and likely incorrect, need to properly constrain min/max
# note that due to the muxing, additional timing views with set_case_analysis may be needed.

# aggregate all IO banks
set IO_BANKS [get_ports IOA*]
append_to_collection IO_BANKS [get_ports IOB*]
append_to_collection IO_BANKS [get_ports IOC*]
append_to_collection IO_BANKS [get_ports IOR*]

# constrain muxed IOs running on IO_DIV2_CLK and IO_DIV4_CLK
set IO_IN_DEL_FRACTION 0.45
set IO_OUT_DEL_FRACTION 0.45

# IO_DIV2_CLK
set IO_DIV2_IN_DEL    [expr ${IO_IN_DEL_FRACTION} * ${IO_TCK_PERIOD} * 2.0]
set IO_DIV2_OUT_DEL   [expr ${IO_OUT_DEL_FRACTION} * ${IO_TCK_PERIOD} * 2.0]

set_input_delay ${IO_DIV2_IN_DEL}   ${IO_BANKS} -clock IO_DIV2_CLK
set_output_delay ${IO_DIV2_OUT_DEL} ${IO_BANKS} -clock IO_DIV2_CLK

# IO_DIV4_CLK
set IO_DIV4_IN_DEL    [expr ${IO_IN_DEL_FRACTION} * ${IO_TCK_PERIOD} * 4.0]
set IO_DIV4_OUT_DEL   [expr ${IO_OUT_DEL_FRACTION} * ${IO_TCK_PERIOD} * 4.0]

set_input_delay ${IO_DIV4_IN_DEL}   ${IO_BANKS} -clock IO_DIV4_CLK -add_delay
set_output_delay ${IO_DIV4_OUT_DEL} ${IO_BANKS} -clock IO_DIV4_CLK -add_delay

#####################
# sysrst_ctrl       #
#####################

# MIO paths that go into sysrst_ctrl and fan out into MIOs or dedicated sysrst_ctrl outputs are async in nature, hence we constrain them using a max delay.
set SYSRST_MAXDELAY 50.0
set_max_delay -from ${IO_BANKS} -to ${IO_BANKS} -through [get_cells top_earlgrey/u_sysrst_ctrl_aon/*] ${SYSRST_MAXDELAY}

#####################
# AON clk           #
#####################
set AON_CLK_PIN u_ast/u_aon_clk/u_aon_osc/u_buf/out_o
# target is 200KHz, overconstrain by factor
set AON_TCK_TARGET_PERIOD 5000.0
set AON_TCK_PERIOD [expr $AON_TCK_TARGET_PERIOD*$CLK_PERIOD_FACTOR]
#set_ideal_network [get_pins ${AON_CLK_PIN}]

create_clock -name AON_CLK -period ${AON_TCK_PERIOD} [get_pins ${AON_CLK_PIN}]
set_clock_uncertainty ${SETUP_CLOCK_UNCERTAINTY} [get_clocks AON_CLK]

#####################
# JTAG clock        #
#####################
# TODO: set up constraints for JTAG.
set JTAG_CLK_PIN IOR3
# target is 20MHz, overconstrain by factor
set JTAG_TCK_TARGET_PERIOD 50
set JTAG_TCK_PERIOD [expr $JTAG_TCK_TARGET_PERIOD*$CLK_PERIOD_FACTOR]

create_clock -name JTAG_TCK -period $JTAG_TCK_PERIOD [get_ports $JTAG_CLK_PIN]
#set_ideal_network [get_ports $JTAG_CLK_PIN]
set_clock_uncertainty ${SETUP_CLOCK_UNCERTAINTY} [get_clocks JTAG_TCK]


#####################################
# SPI System Parameters             #
#####################################

# routing delay from external component to device
set PCB_DEL 1

# external spi host setup
set HOST_SETUP_DEL 4

# external spi host clk-to-q
set HOST_OUT_DEL 3

# external spi dev setup
set STORAGE_SETUP_DEL 3

# external spi dev clk-to-q
set STORAGE_OUT_DEL 7

#################
# SPI DEV clock #
#################
# TODO
# Add source delays for generated clocks
# Construct realistic input / output delays using system parameters

# strawman constraints. Device target freq is 48MHz. Using 62.5MHz to over-constraint
set SPI_DEV_CLK_PIN SPI_DEV_CLK
# 62.5MHz
set SPI_DEV_TCK 16.0
#set_ideal_network ${SPI_DEV_CLK_PIN}

## TODO: Create generated clock for negedge SPI_DEV_CLK. Then make them clock group
create_clock -name SPI_DEV_CLK  -period ${SPI_DEV_TCK} [get_ports ${SPI_DEV_CLK_PIN}]
set_clock_uncertainty ${SETUP_CLOCK_UNCERTAINTY} [get_clocks SPI_DEV_CLK]

create_generated_clock -name SPI_DEV_IN_CLK -source SPI_DEV_CLK -divide_by 1 \
    [get_pins top_earlgrey/u_spi_device/u_clk_spi_in_buf/clk_o]
create_generated_clock -name SPI_DEV_OUT_CLK -source SPI_DEV_CLK -divide_by 1 \
    -invert [get_pins top_earlgrey/u_spi_device/u_clk_spi_out_buf/clk_o]

## TODO: these are dummy constraints and likely incorrect, need to properly constrain min/max
# FRACTION is reduced to 0.2 as internal datapath for SPI is half clk period
set SPI_DEV_IN_DEL_FRACTION 0.2
set SPI_DEV_OUT_DEL_FRACTION 0.2
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

# False path from CSb to return to host as CSb for that path behaves as reset.
#set_ideal_network [get_pins top_earlgrey/u_spi_device/u_csb_rst_scan_mux/clk_o]
set_false_path -through [get_pins top_earlgrey/u_spi_device/cio_csb_i] \
               -through [get_pins top_earlgrey/u_spi_device/cio_sd_en_o*]
set_false_path -through [get_pins top_earlgrey/u_spi_device/cio_csb_i] \
    -through [get_pins top_earlgrey/u_spi_device/cio_sd_o*]

##################
# SPI HOST clock #
##################
# SPI host core logic operates on the IO_CLK
#
# See https://docs.google.com/drawings/d/1qkUnXaRafIPyBnVpreqfbF_zSy0xlpHqXMZp6F-j8Cc/edit?usp=sharing
# During pre-layout, the SPI_HOST_CLK source latencies are estimanted to account for
# pad and logic latencies.  After CTS, source latency must be removed as all clocks are propagated

# TODO, this flop should be hand instantiated
set CLK_DIV_PIN top_earlgrey/u_spi_host0/u_spi_core/u_fsm/sck_q_reg/Q

# internal divided by 2 clock (fastest spi host configuration)
create_generated_clock -name SPI_HOST_INT_CLK -source [get_pins ${IO_CLK_PIN}] \
    -divide_by 2 [get_pins ${CLK_DIV_PIN}] -add

# cascaded generated clock on the port
create_generated_clock -name SPI_HOST_CLK -source [get_pins ${CLK_DIV_PIN}] \
    -divide_by 1 [get_ports SPI_HOST_CLK] -add

# Approximate source latency
# The following must be removed after CTS when clocks actually propagate
set SPI_HOST_SRC_LATENCY 5
set_clock_latency ${SPI_HOST_SRC_LATENCY} -source [get_clock SPI_HOST_CLK]

# set multicycle path for data going from SPI_HOST_CLK to logic
# the SPI host logic will read these paths at "full cycle"
set_multicycle_path -setup 2 -end -from [get_clocks SPI_HOST_CLK] -to [get_clocks IO_CLK]
set_multicycle_path -hold 1  -end -from [get_clocks SPI_HOST_CLK] -to [get_clocks IO_CLK]

# computed delays from connected device
# host in has 2x the pcb delay to account for delays on both outgoing clocks and incoming data
set SPI_HOST_IN_DEL    [expr 2*${PCB_DEL} + ${STORAGE_OUT_DEL}]
set SPI_HOST_OUT_DEL   [expr ${PCB_DEL} + ${STORAGE_SETUP_DEL}]

# bidir ports
set_input_delay ${SPI_HOST_IN_DEL} [get_ports SPI_HOST_CS_L] -clock SPI_HOST_CLK -add_delay
set_input_delay ${SPI_HOST_IN_DEL} [get_ports SPI_HOST_D0]   -clock SPI_HOST_CLK -add_delay
set_input_delay ${SPI_HOST_IN_DEL} [get_ports SPI_HOST_D1]   -clock SPI_HOST_CLK -add_delay
set_input_delay ${SPI_HOST_IN_DEL} [get_ports SPI_HOST_D2]   -clock SPI_HOST_CLK -add_delay
set_input_delay ${SPI_HOST_IN_DEL} [get_ports SPI_HOST_D3]   -clock SPI_HOST_CLK -add_delay

set_output_delay ${SPI_HOST_OUT_DEL} [get_ports SPI_HOST_CS_L] -clock SPI_HOST_CLK -add_delay
set_output_delay ${SPI_HOST_OUT_DEL} [get_ports SPI_HOST_D0]   -clock SPI_HOST_CLK -add_delay
set_output_delay ${SPI_HOST_OUT_DEL} [get_ports SPI_HOST_D1]   -clock SPI_HOST_CLK -add_delay
set_output_delay ${SPI_HOST_OUT_DEL} [get_ports SPI_HOST_D2]   -clock SPI_HOST_CLK -add_delay
set_output_delay ${SPI_HOST_OUT_DEL} [get_ports SPI_HOST_D3]   -clock SPI_HOST_CLK -add_delay

#####################################
# SPI DEV clock Passthru Operation  #
#####################################
# Passthrough target freq is 33MHz. Using 40MHz to over-constrain
#
# The constraints below take the following approach:
# Define incoming passthrough clock on the SPI_DEV_CLK pin and relate all the inputs to it.
# Define also output delays since all pins are bidirectional.
# Define outgoing passthrough clock on the SPI_HOST_CLK pin but make sure it is a generated version
# of the incoming passthrough clock, relate the host side pins to this clock in both input/output
# directions.
#
# For details on SPI passthrough timing, please see
# https://docs.google.com/presentation/d/1GEPxKaOsr9ZcJwI_MBEL74P7jQvBFzOdzSbgru_yVLQ/edit?usp=sharing

set SPI_DEV_PASSTHRU_CK 25.0
create_clock -name SPI_DEV_PASSTHRU_CLK -period ${SPI_DEV_PASSTHRU_CK} [get_ports ${SPI_DEV_CLK_PIN}] -add
set_clock_uncertainty ${SETUP_CLOCK_UNCERTAINTY} [get_clocks SPI_DEV_PASSTHRU_CLK]

# clocks used by spi device internally
# Unlike spi-dev above, here the "incoming" clock is treated like the "launch", while the inverted
# is treated like "capture".  The other way would work fine as well, but several other adjustments
# would need to be made the rest of the constraints.
create_generated_clock -name SPI_DEV_PASSTHRU_IN_CLK -source SPI_DEV_CLK -divide_by 1 \
    -invert [get_pins top_earlgrey/u_spi_device/u_clk_spi_in_buf/clk_o] -add -master_clock SPI_DEV_PASSTHRU_CLK
create_generated_clock -name SPI_DEV_PASSTHRU_OUT_CLK -source SPI_DEV_CLK -divide_by 1 \
    [get_pins top_earlgrey/u_spi_device/u_clk_spi_out_buf/clk_o] -add -master_clock SPI_DEV_PASSTHRU_CLK

# clocks accounting for propagation delay to the other side
create_generated_clock -name SPI_HOST_PASSTHRU_CLK -source SPI_DEV_CLK \
    -master_clock SPI_DEV_PASSTHRU_CLK -divide_by 1 \
    [get_ports SPI_HOST_CLK] -add

# The propagated properties are needed to ensure the passthrough clocks assume all passthrough delay.
# This is done specifically for the passthrough interface to get realistic timing even during
# pre-layout.
set_propagated_clock [get_clock SPI_DEV_PASSTHRU_CLK]
set_propagated_clock [get_clock SPI_HOST_PASSTHRU_CLK]

# delays below are nominal since target frequency is already over constrained
set HALF_CYCLE [expr ${SPI_DEV_PASSTHRU_CK} / 2]

# These are delays facing the host
set SPI_DEV_PASSTHRU_HOST_IN_DEL [expr 2*${PCB_DEL} + ${HOST_OUT_DEL}]
set SPI_DEV_PASSTHRU_HOST_OUT_DEL [expr {${PCB_DEL} + ${HOST_SETUP_DEL}}]

# for transactions passing from storage into the device, they are going to be sampled
# by the host at "full cycle" boundaries
set SPI_DEV_PASSTHRU_STORAGE_IN_DEL [expr {2*${PCB_DEL} + ${STORAGE_OUT_DEL}}]

# for transactions passing through the device to the storage device, the commands
# are captured on half cycle boundaries
set SPI_DEV_PASSTHRU_STORAGE_OUT_DEL [expr ${PCB_DEL} + ${STORAGE_SETUP_DEL} + ${HALF_CYCLE}]

# bidir ports facing host
set_input_delay ${SPI_DEV_PASSTHRU_HOST_IN_DEL} [get_ports SPI_DEV_D0] -clock SPI_DEV_PASSTHRU_CLK -add_delay
set_input_delay ${SPI_DEV_PASSTHRU_HOST_IN_DEL} [get_ports SPI_DEV_D1] -clock SPI_DEV_PASSTHRU_CLK -add_delay
set_input_delay ${SPI_DEV_PASSTHRU_HOST_IN_DEL} [get_ports SPI_DEV_D2] -clock SPI_DEV_PASSTHRU_CLK -add_delay
set_input_delay ${SPI_DEV_PASSTHRU_HOST_IN_DEL} [get_ports SPI_DEV_D3] -clock SPI_DEV_PASSTHRU_CLK -add_delay
set_input_delay ${SPI_DEV_PASSTHRU_HOST_IN_DEL} [get_ports SPI_DEV_CS_L] -clock SPI_DEV_PASSTHRU_CLK -add_delay
set_output_delay ${SPI_DEV_PASSTHRU_HOST_OUT_DEL} [get_ports SPI_DEV_D0] -clock SPI_DEV_PASSTHRU_CLK -add_delay
set_output_delay ${SPI_DEV_PASSTHRU_HOST_OUT_DEL} [get_ports SPI_DEV_D1] -clock SPI_DEV_PASSTHRU_CLK -add_delay
set_output_delay ${SPI_DEV_PASSTHRU_HOST_OUT_DEL} [get_ports SPI_DEV_D2] -clock SPI_DEV_PASSTHRU_CLK -add_delay
set_output_delay ${SPI_DEV_PASSTHRU_HOST_OUT_DEL} [get_ports SPI_DEV_D3] -clock SPI_DEV_PASSTHRU_CLK -add_delay

# bidir ports facing storage device
set_input_delay ${SPI_DEV_PASSTHRU_STORAGE_IN_DEL} [get_ports SPI_HOST_D0] -clock SPI_HOST_PASSTHRU_CLK -add_delay
set_input_delay ${SPI_DEV_PASSTHRU_STORAGE_IN_DEL} [get_ports SPI_HOST_D1] -clock SPI_HOST_PASSTHRU_CLK -add_delay
set_input_delay ${SPI_DEV_PASSTHRU_STORAGE_IN_DEL} [get_ports SPI_HOST_D2] -clock SPI_HOST_PASSTHRU_CLK -add_delay
set_input_delay ${SPI_DEV_PASSTHRU_STORAGE_IN_DEL} [get_ports SPI_HOST_D3] -clock SPI_HOST_PASSTHRU_CLK -add_delay
set_output_delay ${SPI_DEV_PASSTHRU_STORAGE_OUT_DEL} [get_ports SPI_HOST_D0] -clock SPI_HOST_PASSTHRU_CLK -add_delay
set_output_delay ${SPI_DEV_PASSTHRU_STORAGE_OUT_DEL} [get_ports SPI_HOST_D1] -clock SPI_HOST_PASSTHRU_CLK -add_delay
set_output_delay ${SPI_DEV_PASSTHRU_STORAGE_OUT_DEL} [get_ports SPI_HOST_D2] -clock SPI_HOST_PASSTHRU_CLK -add_delay
set_output_delay ${SPI_DEV_PASSTHRU_STORAGE_OUT_DEL} [get_ports SPI_HOST_D3] -clock SPI_HOST_PASSTHRU_CLK -add_delay
set_output_delay ${SPI_DEV_PASSTHRU_STORAGE_OUT_DEL} [get_ports SPI_HOST_CS_L] -clock SPI_HOST_PASSTHRU_CLK -add_delay


#####################
# SPI passthrough   #
#####################
# Bronze: Over-constraining. Actual values will be set once design is ready
# input pad + internal + output pad
#
# The commented out code below was the bronze approach. We may still return to it later
# for its simplicity. If we stick with the approach below, it will be necessary to add
# set_data_checks to ensure the signals are relatively balanced.

#set TPAD_I 1.2
#set THODI  2.0
#set TPAD_O 3.3
#set SPI_HODI_PASS_MAX_DELAY [expr ${TPAD_I} + ${THODI} + ${TPAD_O}]
#set SPI_HIDO_PASS_MAX_DELAY ${SPI_HODI_PASS_MAX_DELAY}
#
## TODO: These are strawman constraints and need to be refined.
#set_max_delay ${SPI_HODI_PASS_MAX_DELAY} -from [get_ports SPI_DEV_D0]   -to [get_ports SPI_HOST_D0]
#set_max_delay ${SPI_HODI_PASS_MAX_DELAY} -from [get_ports SPI_DEV_D1]   -to [get_ports SPI_HOST_D1]
#set_max_delay ${SPI_HODI_PASS_MAX_DELAY} -from [get_ports SPI_DEV_D2]   -to [get_ports SPI_HOST_D2]
#set_max_delay ${SPI_HODI_PASS_MAX_DELAY} -from [get_ports SPI_DEV_D3]   -to [get_ports SPI_HOST_D3]
#set_max_delay ${SPI_HODI_PASS_MAX_DELAY} -from [get_ports SPI_DEV_CS_L] -to [get_ports SPI_HOST_CS_L]
#
#set_max_delay ${SPI_HIDO_PASS_MAX_DELAY} -from [get_ports SPI_HOST_D0] -to [get_ports SPI_DEV_D0]
#set_max_delay ${SPI_HIDO_PASS_MAX_DELAY} -from [get_ports SPI_HOST_D1] -to [get_ports SPI_DEV_D1]
#set_max_delay ${SPI_HIDO_PASS_MAX_DELAY} -from [get_ports SPI_HOST_D2] -to [get_ports SPI_DEV_D2]
#set_max_delay ${SPI_HIDO_PASS_MAX_DELAY} -from [get_ports SPI_HOST_D3] -to [get_ports SPI_DEV_D3]

#####################
# CDC               #
#####################

# this may need some refinement (and max delay / skew needs to be constrained)
set_clock_groups -name group1 -async                                  \
    -group [get_clocks MAIN_CLK                                     ] \
    -group [get_clocks USB_CLK                                      ] \
    -group [get_clocks {SPI_DEV_CLK SPI_DEV_IN_CLK SPI_DEV_OUT_CLK} ] \
    -group [get_clocks {SPI_DEV_PASSTHRU_CLK SPI_HOST_PASSTHRU_CLK SPI_DEV_PASSTHRU_IN_CLK SPI_DEV_PASSTHRU_OUT_CLK} ] \
    -group [get_clocks {IO_CLK SPI_HOST_INT_CLK SPI_HOST_CLK}       ] \
    -group [get_clocks IO_DIV2_CLK                                  ] \
    -group [get_clocks IO_DIV4_CLK                                  ] \
    -group [get_clocks JTAG_TCK                                     ] \
    -group [get_clocks AON_CLK                                      ]

# UART loopback path can be considered to be a false path
set_false_path -through [get_pins top_earlgrey/u_uart*/cio_rx_i] -through [get_pins top_earlgrey/u_uart*/cio_tx_o]

# break all timing paths through bidirectional IO buffers (i.e., from output and oe to input buffer output)
set_false_path -through [get_pins *padring/*pad/*/oe_i] -through [get_pins *padring/*pad/*/in_o]
set_false_path -through [get_pins *padring/*pad/*/out_i] -through [get_pins *padring/*pad/*/in_o]

# break path through jtag mux
set_false_path -from [get_ports IOC7] -to [get_ports IOR*]

# pass through is not fully supported yet by SPI host
# TODO: revise this
# set_false_path -through [get_pins top_earlgrey/u_spi_host1/u_sck_passthrough/gen_*/u_size_only_mux2/${DRIVING_CELL_PIN}]

#####################
# I/O drive/load    #
#####################

# attach load and drivers to IOs to get a more realistic estimate
set_driving_cell -no_design_rule -lib_cell ${DRIVING_PAD} -pin ${DRIVING_PAD_PIN} [all_inputs]
set_load [load_of ${LOAD_PAD_LIB}/${LOAD_PAD}/${LOAD_PAD_PIN}] [all_outputs]

###################################
# Size Only and Don't touch Cells #
###################################

# this is for architectural clock buffers, inverters and muxes
set_size_only -all_instances [get_cells -h *u_size_only*] true

# do not touch pad cells
set_dont_touch [get_cells -h *u_pad_macro*]

puts "Done applying constraints for top level"

##########################################
# Case analysis for quasi-static signals #
##########################################

# assume a value of 0 for the open drain pad attribute
set_case_analysis 0 [get_pins u_padring/*_pad/attr_i\[od_en\]]
