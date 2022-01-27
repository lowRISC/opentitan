## Copyright lowRISC contributors.
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0

## ChipWhisperer CW310 "Bergen Board".
##
## This pin mapping is for the REV06 (final) PCB (and later).

## Clock Signal
set_property -dict { PACKAGE_PIN N21 IOSTANDARD LVCMOS33 } [get_ports { IO_CLK }]; # PLL_CLK2

## Clock constraints
## set via clocks.xdc

## Preserve prim_prince modules and setup multi-cycle paths
## These are no longer required, but kept here as a reference
## set_property KEEP_HIERARCHY TRUE [get_cells top_earlgrey/u_flash_eflash/gen_flash_banks[*].i_core/u_scramble/u_cipher]
## set_multicycle_path -setup 2 -through [get_pins -of_objects [get_cells top_earlgrey/u_flash_eflash/gen_flash_banks[*].i_core/u_scramble/u_cipher]]
## set_multicycle_path -hold 1  -through [get_pins -of_objects [get_cells top_earlgrey/u_flash_eflash/gen_flash_banks[*].i_core/u_scramble/u_cipher]]

#set_property CLOCK_DEDICATED_ROUTE FALSE [get_nets IO_SDCK_IBUF]; # SDCK clock to be ignored

## LEDs
set_property -dict { PACKAGE_PIN M26  DRIVE 8 IOSTANDARD LVCMOS33 } [get_ports { IOA8 }]; #LED 0
set_property -dict { PACKAGE_PIN M25  DRIVE 8 IOSTANDARD LVCMOS33 } [get_ports { IOB0 }]; #LED 1
set_property -dict { PACKAGE_PIN M24  DRIVE 8 IOSTANDARD LVCMOS33 } [get_ports { IOB1 }]; #LED 2
set_property -dict { PACKAGE_PIN M19  DRIVE 8 IOSTANDARD LVCMOS33 } [get_ports { IOB2 }]; #LED 3
set_property -dict { PACKAGE_PIN L25  DRIVE 8 IOSTANDARD LVCMOS33 } [get_ports { IOB3 }]; #LED 4
set_property -dict { PACKAGE_PIN K26  DRIVE 8 IOSTANDARD LVCMOS33 } [get_ports { IOB4 }]; #LED 5
set_property -dict { PACKAGE_PIN L24  DRIVE 8 IOSTANDARD LVCMOS33 } [get_ports { IOB5 }]; #LED 6
set_property -dict { PACKAGE_PIN K25  DRIVE 8 IOSTANDARD LVCMOS33 } [get_ports { IOB6 }]; #LED 7

## Buttons
set_property -dict { PACKAGE_PIN Y7 IOSTANDARD LVCMOS18 } [get_ports { POR_N }]; #pushbutton SW2

## Switches
set_property -dict { PACKAGE_PIN U9 IOSTANDARD LVCMOS18 }  [get_ports { IOA0 }]; #USRDIP0
set_property -dict { PACKAGE_PIN V7 IOSTANDARD LVCMOS18 }  [get_ports { IOA1 }]; #USRDIP1
set_property -dict { PACKAGE_PIN V8 IOSTANDARD LVCMOS18 }  [get_ports { IOA2 }]; #USRDIP2
set_property -dict { PACKAGE_PIN W9 IOSTANDARD LVCMOS18 }  [get_ports { IOA3 }]; #USRDIP3
set_property -dict { PACKAGE_PIN V9 IOSTANDARD LVCMOS18 }  [get_ports { IOA4 }]; #USRDIP4
set_property -dict { PACKAGE_PIN W8 IOSTANDARD LVCMOS18 }  [get_ports { IOA5 }]; #USRDIP5
set_property -dict { PACKAGE_PIN W10 IOSTANDARD LVCMOS18 } [get_ports { IOA6 }]; #USRDIP6
set_property -dict { PACKAGE_PIN V11 IOSTANDARD LVCMOS18 } [get_ports { IOA7 }]; #USRDIP7

## SPI/JTAG
set_property -dict { PACKAGE_PIN D26 IOSTANDARD LVCMOS33 } [get_ports { SPI_DEV_CLK }]; #SCK (SPI1_SCK)
set_property -dict { PACKAGE_PIN A24 IOSTANDARD LVCMOS33 } [get_ports { SPI_DEV_D0 }]; #SDI (SPI1_COPI)
set_property -dict { PACKAGE_PIN A22 IOSTANDARD LVCMOS33 } [get_ports { SPI_DEV_D1 }]; #SDO (SPI1_CIPO)
set_property -dict { PACKAGE_PIN C26 IOSTANDARD LVCMOS33 } [get_ports { SPI_DEV_CS_L }]; #CSB (SPI1_CS)
set_property -dict { PACKAGE_PIN V21 IOSTANDARD LVCMOS33 } [get_ports { IOB9 }]; #JTAG TRST (USB_A17) #SAM3X
set_property -dict { PACKAGE_PIN W21 IOSTANDARD LVCMOS33 PULLTYPE PULLUP } [get_ports { IO_JSRST_N }]; #JTAG SRST (USB_A18)
set_property -dict { PACKAGE_PIN W20 IOSTANDARD LVCMOS33 PULLTYPE PULLDOWN } [get_ports { IOB7 }]; #JTAG/SPI (USB_A19)
set_property -dict { PACKAGE_PIN U21 IOSTANDARD LVCMOS33 PULLTYPE PULLDOWN } [get_ports { IOB8 }]; #Bootstrap (USB_A16)

## SPI HOST
set_property -dict { PACKAGE_PIN AF8 IOSTANDARD LVCMOS18 } [get_ports { SPI_HOST_CLK }];   #SCK (USR_SPI0CLK)
set_property -dict { PACKAGE_PIN AE8 IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { SPI_HOST_D0 }];    #SDO (USR_SPI0DQ0)
set_property -dict { PACKAGE_PIN AE10 IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { SPI_HOST_D1 }];   #SDO (USR_SPI0DQ1)
set_property -dict { PACKAGE_PIN AF9 IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { SPI_HOST_D2 }];    #SDO (USR_SPI0DQ2)
set_property -dict { PACKAGE_PIN AF10 IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { SPI_HOST_D3 }];   #SDO (USR_SPI0DQ3)
set_property -dict { PACKAGE_PIN AE11 IOSTANDARD LVCMOS18 } [get_ports { SPI_HOST_CS_L }]; #CSB (USR_SPI0CS)

## OTHER IO
set_property -dict { PACKAGE_PIN A8  IOSTANDARD LVCMOS33 } [get_ports { IOC2 }]; #USERIOB-9
set_property -dict { PACKAGE_PIN E10 IOSTANDARD LVCMOS33 } [get_ports { IOC5 }]; #USERIOB-14
set_property -dict { PACKAGE_PIN D8  IOSTANDARD LVCMOS33 } [get_ports { IOC6 }]; #USERIOB-16
set_property -dict { PACKAGE_PIN D9  IOSTANDARD LVCMOS33 } [get_ports { IOC7 }]; #USERIOB-18
#set_property -dict { PACKAGE_PIN C9  IOSTANDARD LVCMOS33 } [get_ports { IOC8 }]; #USERIOB-24
#set_property -dict { PACKAGE_PIN D10 IOSTANDARD LVCMOS33 } [get_ports { IOC9 }]; #USERIOB-26
set_property -dict { PACKAGE_PIN B9  IOSTANDARD LVCMOS33 } [get_ports { IOC10 }]; #USERIOB-11
set_property -dict { PACKAGE_PIN A9  IOSTANDARD LVCMOS33 } [get_ports { IOC11 }]; #USERIOB-15

## ChipWhisperer 20-Pin Connector (J14)
set_property -dict { PACKAGE_PIN AF25 IOSTANDARD LVCMOS33 } [get_ports { IOC9 }];       #J14 PIN 12 CWIO_IO2 - OpenTitan UART1 TX
set_property -dict { PACKAGE_PIN AE25 IOSTANDARD LVCMOS33 } [get_ports { IOC8 }];       #J14 PIN 10 CWIO_IO1 - OpenTitan UART1 RX
set_property -dict { PACKAGE_PIN AF24 IOSTANDARD LVCMOS33 } [get_ports { IO_TRIGGER }]; #J14 PIN 16 CWIO_IO4 - Capture Trigger
set_property -dict { PACKAGE_PIN AB21 IOSTANDARD LVCMOS33 } [get_ports { IO_CLKOUT }];  #J14 PIN  4 CWIO_HS1 - Target clock

## TI TUSB1106 USB PHY usbdev testing
set_property -dict { PACKAGE_PIN AF19  IOSTANDARD LVCMOS18 } [get_ports { IO_UPHY_DP_TX }]; #USRUSB_VPO
set_property -dict { PACKAGE_PIN AF20  IOSTANDARD LVCMOS18 } [get_ports { IO_UPHY_DN_TX }]; #USRUSB_VMO
set_property -dict { PACKAGE_PIN V16   IOSTANDARD LVCMOS18 } [get_ports { IO_UPHY_DP_RX }]; #USRUSB_VP
set_property -dict { PACKAGE_PIN V13   IOSTANDARD LVCMOS18 } [get_ports { IO_UPHY_DN_RX }]; #USRUSB_VM
set_property -dict { PACKAGE_PIN AF14  IOSTANDARD LVCMOS18 } [get_ports { IO_UPHY_DPPULLUP }]; #USRUSB_SOFTCONN
set_property -dict { PACKAGE_PIN P18   IOSTANDARD LVCMOS33 } [get_ports { IOR0 }]; #USRUSB_VBUS_DETECT
set_property -dict { PACKAGE_PIN AE15  IOSTANDARD LVCMOS18 } [get_ports { IO_UPHY_OE_N }]; #USRUSB_OE
set_property -dict { PACKAGE_PIN V17   IOSTANDARD LVCMOS18 } [get_ports { IO_UPHY_D_RX }]; #USRUSB_RCV
set_property -dict { PACKAGE_PIN AE16  IOSTANDARD LVCMOS18 } [get_ports { IO_UPHY_SPD  }]; #USRUSB_SPD
set_property -dict { PACKAGE_PIN AF15  IOSTANDARD LVCMOS18 } [get_ports { IO_UPHY_SUS  }]; #USRUSB_SUS

## USB input delay to accommodate T_FST (full-speed transition time) and the
## PHY's sampling logic. The PHY expects to only see up to one transient / fake
## SE0. The phase relationship with the PHY's sampling clock is arbitrary, but
## for simplicity, constrain the maximum path delay to something smaller than
## `T_sample - T_FST(max)` to help keep the P/N skew from slipping beyond one
## sample period.
set clks_48_unbuf [get_clocks -of_objects [get_pin clkgen/pll/CLKOUT1]]
set_input_delay -clock ${clks_48_unbuf} -min 3 [get_ports {IO_UPHY_DP_RX IO_UPHY_DN_RX IO_UPHY_D_RX}]
set_input_delay -clock ${clks_48_unbuf} -add_delay -max 17 [get_ports {IO_UPHY_DP_RX IO_UPHY_DN_RX IO_UPHY_D_RX}]

## USB output max skew constraint
## Use the output-enable as a "clock" and time the P/N relative to it. Keep the skew within T_FST.
set usb_embed_out_clk [create_generated_clock -name usb_embed_out_clk -source [get_pin clkgen/pll/CLKOUT1] -multiply_by 1 [get_ports IO_UPHY_OE_N]]
set_false_path -from [get_clocks -include_generated_clocks clk_io_div4] -to ${usb_embed_out_clk}
set_output_delay -min -clock ${usb_embed_out_clk} 7 [get_ports {IO_UPHY_DP_TX IO_UPHY_DN_TX}]
set_output_delay -max -clock ${usb_embed_out_clk} 14 [get_ports {IO_UPHY_DP_TX IO_UPHY_DN_TX}] -add_delay

## Not used - route to header for now?
set_property -dict { PACKAGE_PIN A10   IOSTANDARD LVCMOS33 } [get_ports { USB_P }]; #USERIOB-19
set_property -dict { PACKAGE_PIN B11   IOSTANDARD LVCMOS33 } [get_ports { USB_N }]; #USERIOB-21
set_property -dict { PACKAGE_PIN B12   IOSTANDARD LVCMOS33 } [get_ports { IOR1 }]; #USERIOB-23
set_property -dict { PACKAGE_PIN A12   IOSTANDARD LVCMOS33 } [get_ports { IO_USB_DNPULLUP0 }]; #USERIOB-25
set_property -dict { PACKAGE_PIN A13   IOSTANDARD LVCMOS33 } [get_ports { IO_USB_DPPULLUP0 }]; #USERIOB-27

## UART
set_property -dict { PACKAGE_PIN AA22 IOSTANDARD LVCMOS33 } [get_ports { IOC4 }]; #UART1RXD - OpenTitan UART0 TX
set_property -dict { PACKAGE_PIN W24  IOSTANDARD LVCMOS33 } [get_ports { IOC3 }]; #UART1TXD - OpenTitan UART0 RX

## Configuration options, can be used for all designs
set_property CONFIG_VOLTAGE 3.3 [current_design]
set_property CFGBVS VCCO [current_design]
