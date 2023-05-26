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

## Buttons
set_property -dict { PACKAGE_PIN Y7 IOSTANDARD LVCMOS18 } [get_ports { POR_BUTTON_N }]; #pushbutton SW2

## JTAG system reset
set_property -dict { PACKAGE_PIN  T17  IOSTANDARD LVCMOS33 PULLTYPE PULLUP } [get_ports { JTAG_SRST_N }]; # USR_DBG_nRST (SRSTn)

## Power-on Reset
set_property -dict { PACKAGE_PIN  E18  IOSTANDARD LVCMOS33 PULLTYPE PULLUP } [get_ports { POR_N }]; # J4.32


## Preserve prim_prince modules and setup multi-cycle paths
## These are no longer required, but kept here as a reference
## set_property KEEP_HIERARCHY TRUE [get_cells top_earlgrey/u_flash_eflash/gen_flash_banks[*].i_core/u_scramble/u_cipher]
## set_multicycle_path -setup 2 -through [get_pins -of_objects [get_cells top_earlgrey/u_flash_eflash/gen_flash_banks[*].i_core/u_scramble/u_cipher]]
## set_multicycle_path -hold 1  -through [get_pins -of_objects [get_cells top_earlgrey/u_flash_eflash/gen_flash_banks[*].i_core/u_scramble/u_cipher]]

#set_property CLOCK_DEDICATED_ROUTE FALSE [get_nets IO_SDCK_IBUF]; # SDCK clock to be ignored

## For the MIOs, peripheral assignments for the default test configuration are
## noted in comments. However, not all of those functions are realizable on the
## FPGA design.

## IOA bank
set_property -dict { PACKAGE_PIN B10 IOSTANDARD LVCMOS33 } [get_ports { IOA0 }]; # J5.17 USERIOB-17, UART RX
set_property -dict { PACKAGE_PIN A10 IOSTANDARD LVCMOS33 } [get_ports { IOA1 }]; # J5.19 USERIOB-19, UART TX
set_property -dict { PACKAGE_PIN B11 IOSTANDARD LVCMOS33 } [get_ports { IOA2 }]; # J5.21 USERIOB-21
set_property -dict { PACKAGE_PIN B12 IOSTANDARD LVCMOS33 } [get_ports { IOA3 }]; # J5.23 USERIOB-23
set_property -dict { PACKAGE_PIN A12 IOSTANDARD LVCMOS33 } [get_ports { IOA4 }]; # J5.25 USERIOB-25, UART RX
set_property -dict { PACKAGE_PIN A13 IOSTANDARD LVCMOS33 } [get_ports { IOA5 }]; # J5.27 USERIOB-27, UART TX
set_property -dict { PACKAGE_PIN C14 IOSTANDARD LVCMOS33 } [get_ports { IOA6 }]; # J5.29 USERIOB-29, OPEN-DRAIN GPIO
set_property -dict { PACKAGE_PIN A14 IOSTANDARD LVCMOS33 } [get_ports { IOA7 }]; # J5.31 USERIOB-31, I2C TARGET SDA, SPI TPM CSB
set_property -dict { PACKAGE_PIN B14 IOSTANDARD LVCMOS33 } [get_ports { IOA8 }]; # J5.33 USERIOB-33, I2C TARGET SCL

## IOB bank
# All pins except IOB7, IOB8, IOB11, and IOB12 are on the USERIOA header.
# Those four could not be fit onto the USERIOA header, so they have been routed to PMOD2 instead.
set_property -dict { PACKAGE_PIN K15 IOSTANDARD LVCMOS33 }  [get_ports { IOB0  }]; # J4.1 USERIOA-1, SPI HOST CSB
set_property -dict { PACKAGE_PIN J15 IOSTANDARD LVCMOS33 }  [get_ports { IOB1  }]; # J4.3 USERIOA-3, SPI HOST IO0
set_property -dict { PACKAGE_PIN K16 IOSTANDARD LVCMOS33 }  [get_ports { IOB2  }]; # J4.5 USERIOA-5, SPI HOST IO1
set_property -dict { PACKAGE_PIN J16 IOSTANDARD LVCMOS33 }  [get_ports { IOB3  }]; # J4.7 USERIOA-7, SPI HOST SCK
set_property -dict { PACKAGE_PIN H16 IOSTANDARD LVCMOS33 }  [get_ports { IOB4  }]; # J4.9 USERIOA-9, UART RX
set_property -dict { PACKAGE_PIN H17 IOSTANDARD LVCMOS33 }  [get_ports { IOB5  }]; # J4.11 USERIOA-11, UART TX
set_property -dict { PACKAGE_PIN G16 IOSTANDARD LVCMOS33 }  [get_ports { IOB6  }]; # J4.13 USERIOA-13
set_property -dict { PACKAGE_PIN R25 IOSTANDARD LVCMOS33 }  [get_ports { IOB7  }]; # PMOD2_IO5
set_property -dict { PACKAGE_PIN P24 IOSTANDARD LVCMOS33 }  [get_ports { IOB8  }]; # PMOD2_IO6
set_property -dict { PACKAGE_PIN K20 IOSTANDARD LVCMOS33 }  [get_ports { IOB9  }]; # J4.15 USERIOA-15, I2C HOST SDA
set_property -dict { PACKAGE_PIN E16 IOSTANDARD LVCMOS33 }  [get_ports { IOB10 }]; # J4.17 USERIOA-17, I2C HOST SCL
set_property -dict { PACKAGE_PIN P23 IOSTANDARD LVCMOS33 }  [get_ports { IOB11 }]; # PMOD2_IO7, I2C SCL
set_property -dict { PACKAGE_PIN T23 IOSTANDARD LVCMOS33 }  [get_ports { IOB12 }]; # PMOD2_IO8, I2C SDA

## IOC bank
# Most pins are on USERIO* headers, but IOC7 is used for VBUS detection for USB.
# In addition, IOC9 is placed on PMOD2, as it didn't make the cut for the USERIO headers.
set_property -dict { PACKAGE_PIN E10 IOSTANDARD LVCMOS33 }  [get_ports { IOC0  }]; # J5.14 USERIOB-14, SW STRAP 0
set_property -dict { PACKAGE_PIN A9  IOSTANDARD LVCMOS33 }  [get_ports { IOC1  }]; # J5.15 USERIOB-15, SW STRAP 1
set_property -dict { PACKAGE_PIN D8  IOSTANDARD LVCMOS33 }  [get_ports { IOC2  }]; # J5.16 USERIOB-16, SW STRAP 2
set_property -dict { PACKAGE_PIN G15 IOSTANDARD LVCMOS33 }  [get_ports { IOC3  }]; # J4.12 USERIOA-12, UART RX (CONSOLE), DFT STRAP 0
set_property -dict { PACKAGE_PIN F15 IOSTANDARD LVCMOS33 }  [get_ports { IOC4  }]; # J4.14 USERIOA-14, UART TX (CONSOLE), DFT STRAP 1
set_property -dict { PACKAGE_PIN D15 IOSTANDARD LVCMOS33 }  [get_ports { IOC5  }]; # J4.16 USERIOA-16, TAP STRAP 1
set_property -dict { PACKAGE_PIN D16 IOSTANDARD LVCMOS33 }  [get_ports { IOC6  }]; # J4.18 USERIOA-18, PWM, EXT_CLK
set_property -dict { PACKAGE_PIN P18 IOSTANDARD LVCMOS33 }  [get_ports { IOC7  }]; # USRUSB_VBUS_DETECT
set_property -dict { PACKAGE_PIN D9  IOSTANDARD LVCMOS33 }  [get_ports { IOC8  }]; # J5.18 USERIOB-18, TAP STRAP 0
set_property -dict { PACKAGE_PIN N19 IOSTANDARD LVCMOS33 }  [get_ports { IOC9  }]; # PMOD2_IO1 (GPIO)
set_property -dict { PACKAGE_PIN F19 IOSTANDARD LVCMOS33 }  [get_ports { IOC10 }]; # J4.36 USERIOA-36, OPEN-DRAIN ALERT
set_property -dict { PACKAGE_PIN G20 IOSTANDARD LVCMOS33 }  [get_ports { IOC11 }]; # J4.38 USERIOA-38, OPEN-DRAIN ALERT
set_property -dict { PACKAGE_PIN B19 IOSTANDARD LVCMOS33 }  [get_ports { IOC12 }]; # J4.40 USERIOA-40, OPEN-DRAIN ALERT



## IOR bank
set_property -dict { PACKAGE_PIN  E20  IOSTANDARD LVCMOS33 } [get_ports { IOR0  }]; # J4.24 USERIOA-24, JTAG TMS
set_property -dict { PACKAGE_PIN  C18  IOSTANDARD LVCMOS33 } [get_ports { IOR1  }]; # J4.26 USERIOA-26, JTAG TDO
set_property -dict { PACKAGE_PIN  D20  IOSTANDARD LVCMOS33 } [get_ports { IOR2  }]; # J4.28 USERIOA-28, JTAG TDI
set_property -dict { PACKAGE_PIN  F20  IOSTANDARD LVCMOS33 } [get_ports { IOR3  }]; # J4.21 USERIOA-21, JTAG TCK
set_property -dict { PACKAGE_PIN  D19  IOSTANDARD LVCMOS33 } [get_ports { IOR4  }]; # J4.23 USERIOA-23, JTAG TRSTn
set_property -dict { PACKAGE_PIN  C19  IOSTANDARD LVCMOS33 } [get_ports { IOR5  }]; # J4.25 USERIOA-25
set_property -dict { PACKAGE_PIN  K17  IOSTANDARD LVCMOS33 } [get_ports { IOR6  }]; # J4.27 USERIOA-27
set_property -dict { PACKAGE_PIN  K18  IOSTANDARD LVCMOS33 } [get_ports { IOR7  }]; # J4.29 USERIOA-29
set_property -dict { PACKAGE_PIN  G17  IOSTANDARD LVCMOS33 } [get_ports { IOR8  }]; # J4.31 USERIOA-31, DIO EC_RST_L
set_property -dict { PACKAGE_PIN  H18  IOSTANDARD LVCMOS33 } [get_ports { IOR9  }]; # J4.33 USERIOA-33, DIO FLASH_WP_L
set_property -dict { PACKAGE_PIN  F17  IOSTANDARD LVCMOS33 } [get_ports { IOR10 }]; # J4.35 USERIOA-35, OPEN-DRAIN GPIO
set_property -dict { PACKAGE_PIN  G19  IOSTANDARD LVCMOS33 } [get_ports { IOR11 }]; # J4.30 USERIOA-30, OPEN-DRAIN GPIO
set_property -dict { PACKAGE_PIN  F18  IOSTANDARD LVCMOS33 } [get_ports { IOR12 }]; # J4.37 USERIOA-37, OPEN-DRAIN GPIO
set_property -dict { PACKAGE_PIN  E15  IOSTANDARD LVCMOS33 } [get_ports { IOR13 }]; # J4.39 USERIOA-39, OPEN-DRAIN GPIO

## SPI device
set_property -dict { PACKAGE_PIN C12 IOSTANDARD LVCMOS33 } [get_ports { SPI_DEV_CLK  }]; # J5.1 USERIOB-1
set_property -dict { PACKAGE_PIN D13 IOSTANDARD LVCMOS33 } [get_ports { SPI_DEV_D0   }]; # J5.3 USERIOB-3
set_property -dict { PACKAGE_PIN A8  IOSTANDARD LVCMOS33 } [get_ports { SPI_DEV_D1   }]; # J5.9 USERIOB-9
set_property -dict { PACKAGE_PIN C13 IOSTANDARD LVCMOS33 } [get_ports { SPI_DEV_D2   }]; # J5.5 USERIOB-5
set_property -dict { PACKAGE_PIN E13 IOSTANDARD LVCMOS33 } [get_ports { SPI_DEV_D3   }]; # J5.7 USERIOB-7
set_property -dict { PACKAGE_PIN B9  IOSTANDARD LVCMOS33 } [get_ports { SPI_DEV_CS_L }]; # J5.11 USERIOB-11

## SPI host
set_property -dict { PACKAGE_PIN AF8 IOSTANDARD LVCMOS18 } [get_ports { SPI_HOST_CLK }];   #SCK (USR_SPI0CLK)
set_property -dict { PACKAGE_PIN AE8 IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { SPI_HOST_D0 }];    #SDO (USR_SPI0DQ0)
set_property -dict { PACKAGE_PIN AE10 IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { SPI_HOST_D1 }];   #SDO (USR_SPI0DQ1)
set_property -dict { PACKAGE_PIN AF9 IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { SPI_HOST_D2 }];    #SDO (USR_SPI0DQ2)
set_property -dict { PACKAGE_PIN AF10 IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { SPI_HOST_D3 }];   #SDO (USR_SPI0DQ3)
set_property -dict { PACKAGE_PIN AE11 IOSTANDARD LVCMOS18 } [get_ports { SPI_HOST_CS_L }]; #CSB (USR_SPI0CS)

## ChipWhisperer 20-Pin Connector (J14)
set_property -dict { PACKAGE_PIN AF24 IOSTANDARD LVCMOS33 } [get_ports { IO_TRIGGER }]; #J14 PIN 16 CWIO_IO4 - Capture Trigger
set_property -dict { PACKAGE_PIN AB21 IOSTANDARD LVCMOS33 } [get_ports { IO_CLKOUT }];  #J14 PIN  4 CWIO_HS1 - Target clock

## TI TUSB1106 USB PHY usbdev testing
set_property -dict { PACKAGE_PIN AF19  IOSTANDARD LVCMOS18 } [get_ports { IO_USB_DP_TX }]; #USRUSB_VPO
set_property -dict { PACKAGE_PIN AF20  IOSTANDARD LVCMOS18 } [get_ports { IO_USB_DN_TX }]; #USRUSB_VMO
set_property -dict { PACKAGE_PIN V16   IOSTANDARD LVCMOS18 } [get_ports { IO_USB_DP_RX }]; #USRUSB_VP
set_property -dict { PACKAGE_PIN V13   IOSTANDARD LVCMOS18 } [get_ports { IO_USB_DN_RX }]; #USRUSB_VM
set_property -dict { PACKAGE_PIN AF14  IOSTANDARD LVCMOS18 } [get_ports { IO_USB_CONNECT }]; #USRUSB_SOFTCONN
set_property -dict { PACKAGE_PIN AE15  IOSTANDARD LVCMOS18 } [get_ports { IO_USB_OE_N }]; #USRUSB_OE
set_property -dict { PACKAGE_PIN V17   IOSTANDARD LVCMOS18 } [get_ports { IO_USB_D_RX }]; #USRUSB_RCV
set_property -dict { PACKAGE_PIN AE16  IOSTANDARD LVCMOS18 } [get_ports { IO_USB_SPEED }]; #USRUSB_SPD
set_property -dict { PACKAGE_PIN AF15  IOSTANDARD LVCMOS18 } [get_ports { IO_USB_SUSPEND }]; #USRUSB_SUS

## USB input delay to accommodate T_FST (full-speed transition time) and the
## PHY's sampling logic. The PHY expects to only see up to one transient / fake
## SE0. The phase relationship with the PHY's sampling clock is arbitrary, but
## for simplicity, constrain the maximum path delay to something smaller than
## `T_sample - T_FST(max)` to help keep the P/N skew from slipping beyond one
## sample period.
set clks_48_unbuf [get_clocks -of_objects [get_pin clkgen/pll/CLKOUT1]]
set_input_delay -clock ${clks_48_unbuf} -min 3 [get_ports {IO_USB_DP_RX IO_USB_DN_RX IO_USB_D_RX}]
set_input_delay -clock ${clks_48_unbuf} -add_delay -max 17 [get_ports {IO_USB_DP_RX IO_USB_DN_RX IO_USB_D_RX}]

## USB output max skew constraint
## Use the output-enable as a "clock" and time the P/N relative to it. Keep the skew within T_FST.
set usb_embed_out_clk [create_generated_clock -name usb_embed_out_clk -source [get_pin clkgen/pll/CLKOUT1] -multiply_by 1 [get_ports IO_USB_OE_N]]
set_false_path -from [get_clocks -include_generated_clocks clk_io_div4] -to ${usb_embed_out_clk}
set_output_delay -min -clock ${usb_embed_out_clk} 7 [get_ports {IO_USB_DP_TX IO_USB_DN_TX}]
set_output_delay -max -clock ${usb_embed_out_clk} 14 [get_ports {IO_USB_DP_TX IO_USB_DN_TX}] -add_delay

## Configuration options, can be used for all designs
set_property CONFIG_VOLTAGE 3.3 [current_design]
set_property CFGBVS VCCO [current_design]
