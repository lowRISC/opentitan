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
set_property -dict { PACKAGE_PIN  T17  IOSTANDARD LVCMOS33 PULLTYPE PULLUP } [get_ports { JTAG_SRST_N }]; #USR_DBG_nRST (nSRST)

## Power-on Reset
set_property -dict { PACKAGE_PIN  U22  IOSTANDARD LVCMOS33 PULLTYPE PULLUP } [get_ports { POR_N }]; #USB_A14 (SAM3X)

## Preserve prim_prince modules and setup multi-cycle paths
## These are no longer required, but kept here as a reference
## set_property KEEP_HIERARCHY TRUE [get_cells top_earlgrey/u_flash_eflash/gen_flash_banks[*].i_core/u_scramble/u_cipher]
## set_multicycle_path -setup 2 -through [get_pins -of_objects [get_cells top_earlgrey/u_flash_eflash/gen_flash_banks[*].i_core/u_scramble/u_cipher]]
## set_multicycle_path -hold 1  -through [get_pins -of_objects [get_cells top_earlgrey/u_flash_eflash/gen_flash_banks[*].i_core/u_scramble/u_cipher]]

#set_property CLOCK_DEDICATED_ROUTE FALSE [get_nets IO_SDCK_IBUF]; # SDCK clock to be ignored

########################################################
## MIOs ##

# earlgrey-pinmux pad banks
# See hw/top_earlgrey/data/top_earlgrey.hjson['pinout']['pads']
#
# __Comment_Structure__
# K410T_PACKAGE_PIN:CW310_SCHEMATIC_SIGNAL_NAME  TEST_PINMUX_MAPPING(typical)   CONNECTED_HW
#              AA24:SAM_TXD0                     EarlGrey:UART2_RX              (SAM3X)
##############
## IOA bank ##
##############                                                                     #
set_property -dict { PACKAGE_PIN AA24 IOSTANDARD LVCMOS33 } [get_ports { IOA0  }]; # AA24:SAM_TXD0   EarlGrey:UART2_RX        (SAM3X)
set_property -dict { PACKAGE_PIN AB22 IOSTANDARD LVCMOS33 } [get_ports { IOA1  }]; # AB22:SAM_RXD0   EarlGrey:UART2_TX        (SAM3X)
set_property -dict { PACKAGE_PIN N17  IOSTANDARD LVCMOS33 } [get_ports { IOA2  }]; #  N17:PMOD1_IO1  EarlGrey:GPIO            (BoB):PMOD2_CSB0
set_property -dict { PACKAGE_PIN T22  IOSTANDARD LVCMOS33 } [get_ports { IOA3  }]; #  T22:PMOD1_IO4  Earlgrey:SPI_HOST1_SCK   (BoB):PMOD2_SCLK
set_property -dict { PACKAGE_PIN R23  IOSTANDARD LVCMOS33 } [get_ports { IOA4  }]; #  R23:PMOD1_IO3  Earlgrey:SPI_HOST1_SIO1  (BoB):PMOD2_SIO1
set_property -dict { PACKAGE_PIN R26  IOSTANDARD LVCMOS33 } [get_ports { IOA5  }]; #  R26:PMOD1_IO2  Earlgrey:SPI_HOST1_SIO0  (BoB):PMOD2_SIO0
set_property -dict { PACKAGE_PIN R25  IOSTANDARD LVCMOS33 } [get_ports { IOA6  }]; #  R25:PMOD1_IO5  EarlGrey:GPIO            (BoB):PMOD2_CSB1
set_property -dict { PACKAGE_PIN T23  IOSTANDARD LVCMOS33 } [get_ports { IOA7  }]; #  T23:PMOD1_IO8  EarlGrey:SPI_HOST1_SIO3  (BoB):PMOD2_SIO3
set_property -dict { PACKAGE_PIN P23  IOSTANDARD LVCMOS33 } [get_ports { IOA8  }]; #  P23:PMOD1_IO7  EarlGrey:SPI_HOST1_SIO2  (BoB):PMOD2_SIO2
#############
## IOB bank #
#############
set_property -dict { PACKAGE_PIN F12  IOSTANDARD LVCMOS33 } [get_ports { IOB0  }]; #  F12:USR_SPI1CLK
set_property -dict { PACKAGE_PIN E11  IOSTANDARD LVCMOS33 } [get_ports { IOB1  }]; #  E11:USR_SPI1DQ0
set_property -dict { PACKAGE_PIN A15  IOSTANDARD LVCMOS33 } [get_ports { IOB2  }]; #  A15:USR_SPI1DQ1
set_property -dict { PACKAGE_PIN F14  IOSTANDARD LVCMOS33 } [get_ports { IOB3  }]; #  F14:USR_SPI1CS
set_property -dict { PACKAGE_PIN AE25 IOSTANDARD LVCMOS33 } [get_ports { IOB4  }]; # AE25:CWIO_IO1     EarlGrey:UART1_RX   ChipWhisperer_ConnectorJ14_PIN10
set_property -dict { PACKAGE_PIN AF25 IOSTANDARD LVCMOS33 } [get_ports { IOB5  }]; # AF25:CWIO_IO2     EarlGrey:UART1_TX   ChipWhisperer_ConnectorJ14_PIN12
set_property -dict { PACKAGE_PIN N23  IOSTANDARD LVCMOS33 } [get_ports { IOB6  }]; #  N23:PMOD2_IO5    EarlGrey:GPIO       (BoB):PMOD1_CSB7
set_property -dict { PACKAGE_PIN N26  IOSTANDARD LVCMOS33 } [get_ports { IOB7  }]; #  N26:PMOD2_IO6    EarlGrey:GPIO       (BoB):PMOD1_RST
set_property -dict { PACKAGE_PIN M20  IOSTANDARD LVCMOS33 } [get_ports { IOB8  }]; #  M20:PMOD2_IO7    EarlGrey:I2C0_SCL   (BoB):PMOD1_I2C_SCL
set_property -dict { PACKAGE_PIN P25  IOSTANDARD LVCMOS33 } [get_ports { IOB9  }]; #  P25:PMOD2_IO8    EarlGrey:I2C0_SDA   (BoB):PMOD1_I2C_SDA
set_property -dict { PACKAGE_PIN V9   IOSTANDARD LVCMOS18 } [get_ports { IOB10 }]; #   V9:USRDIP4                          DIP switches
set_property -dict { PACKAGE_PIN W8   IOSTANDARD LVCMOS18 } [get_ports { IOB11 }]; #   W8:USRDIP5                          DIP switches
set_property -dict { PACKAGE_PIN W10  IOSTANDARD LVCMOS18 } [get_ports { IOB12 }]; #  W10:USRDIP6                          DIP switches
#############
## IOC bank #
#############
set_property -dict { PACKAGE_PIN V22  IOSTANDARD LVCMOS33 PULLTYPE PULLDOWN } [get_ports { IOC0  }]; #  V22:USB_A15               SW Strap 0          (SAM3X):A15
set_property -dict { PACKAGE_PIN U21  IOSTANDARD LVCMOS33 PULLTYPE PULLDOWN } [get_ports { IOC1  }]; #  U21:USB_A16               SW Strap 1          (SAM3X):A16
set_property -dict { PACKAGE_PIN V21  IOSTANDARD LVCMOS33 PULLTYPE PULLDOWN } [get_ports { IOC2  }]; #  V21:USB_A17               SW Strap 2          (SAM3X):A17
set_property -dict { PACKAGE_PIN W24  IOSTANDARD LVCMOS33                   } [get_ports { IOC3  }]; #  W24:SAM_TXD1              EarlGrey:UART0_RX   (SAM3X)
set_property -dict { PACKAGE_PIN AA22 IOSTANDARD LVCMOS33                   } [get_ports { IOC4  }]; # AA22:SAM_RXD1              EarlGrey:UART0_TX   (SAM3X)
set_property -dict { PACKAGE_PIN W20  IOSTANDARD LVCMOS33 PULLTYPE PULLDOWN } [get_ports { IOC5  }]; #  W20:USB_A19               TAP Strap 1         (SAM3X):A19
set_property -dict { PACKAGE_PIN M21  IOSTANDARD LVCMOS33                   } [get_ports { IOC6  }]; #  M21:PMOD2_IO2             EarlGrey:GPIO       (BoB):PMOD1_CSB4
set_property -dict { PACKAGE_PIN P18  IOSTANDARD LVCMOS33                   } [get_ports { IOC7  }]; #  P18:USRUSB_VBUS_DETECT
set_property -dict { PACKAGE_PIN W21  IOSTANDARD LVCMOS33 PULLTYPE PULLDOWN } [get_ports { IOC8  }]; #  W21:USB_A18               TAP Strap 0         (SAM3X):A18
set_property -dict { PACKAGE_PIN M22  IOSTANDARD LVCMOS33                   } [get_ports { IOC9  }]; #  M22:PMOD2_IO1             EarlGrey:GPIO       (BoB):PMOD1_CSB3
set_property -dict { PACKAGE_PIN N19  IOSTANDARD LVCMOS33                   } [get_ports { IOC10 }]; #  N19:PMOD2_IO3             EarlGrey:GPIO       (BoB):PMOD1_CSB5
set_property -dict { PACKAGE_PIN P26  IOSTANDARD LVCMOS33                   } [get_ports { IOC11 }]; #  P26:PMOD2_IO4             EarlGrey:GPIO       (BoB):PMOD1_CSB6
set_property -dict { PACKAGE_PIN P24  IOSTANDARD LVCMOS33                   } [get_ports { IOC12 }]; #  P24:PMOD1_IO6             EarlGrey:GPIO       (BoB):PMOD2_CSB2
#############
## IOR bank #
#############
set_property -dict { PACKAGE_PIN N16         IOSTANDARD LVCMOS33 PULLTYPE PULLUP } [get_ports { IOR0  }]; # N16:USR_DBG_TMS           JTAG
set_property -dict { PACKAGE_PIN P16         IOSTANDARD LVCMOS33 PULLTYPE PULLUP } [get_ports { IOR1  }]; # P16:USR_DBG_TDO           JTAG
set_property -dict { PACKAGE_PIN R16         IOSTANDARD LVCMOS33 PULLTYPE PULLUP } [get_ports { IOR2  }]; # R16:USR_DBG_TDI           JTAG
set_property -dict { PACKAGE_PIN N18         IOSTANDARD LVCMOS33 PULLTYPE PULLUP } [get_ports { IOR3  }]; # N18:USR_DBG_TCK           JTAG
set_property -dict { PACKAGE_PIN U19         IOSTANDARD LVCMOS33 PULLTYPE PULLUP } [get_ports { IOR4  }]; # U19:USR_DBG_TDAT1(nTRST)  JTAG
set_property -dict { PACKAGE_PIN V11         IOSTANDARD LVCMOS18                 } [get_ports { IOR5  }]; # V11:USRDIP7
set_property -dict { PACKAGE_PIN M26 DRIVE 8 IOSTANDARD LVCMOS33                 } [get_ports { IOR6  }]; # M26:USRLED0               EarlGrey:GPIO
set_property -dict { PACKAGE_PIN M25 DRIVE 8 IOSTANDARD LVCMOS33                 } [get_ports { IOR7  }]; # M25:USRLED1               EarlGrey:GPIO
set_property -dict { PACKAGE_PIN M24 DRIVE 8 IOSTANDARD LVCMOS33                 } [get_ports { IOR8  }]; # M24:USRLED2               EarlGrey:GPIO
set_property -dict { PACKAGE_PIN M19 DRIVE 8 IOSTANDARD LVCMOS33                 } [get_ports { IOR9  }]; # M19:USRLED3               EarlGrey:GPIO
set_property -dict { PACKAGE_PIN L25 DRIVE 8 IOSTANDARD LVCMOS33                 } [get_ports { IOR10 }]; # L25:USRLED4               EarlGrey:GPIO
set_property -dict { PACKAGE_PIN K26 DRIVE 8 IOSTANDARD LVCMOS33                 } [get_ports { IOR11 }]; # K26:USRLED5               EarlGrey:GPIO
set_property -dict { PACKAGE_PIN L24 DRIVE 8 IOSTANDARD LVCMOS33                 } [get_ports { IOR12 }]; # L24:USRLED6               EarlGrey:GPIO
set_property -dict { PACKAGE_PIN K25 DRIVE 8 IOSTANDARD LVCMOS33                 } [get_ports { IOR13 }]; # K25:USRLED7               EarlGrey:GPIO

########################################################
## DIOs ##

## SPI device
set_property -dict { PACKAGE_PIN D26 IOSTANDARD LVCMOS33 } [get_ports { SPI_DEV_CLK  }]; #SCK (SPI1_SCK)
set_property -dict { PACKAGE_PIN A24 IOSTANDARD LVCMOS33 } [get_ports { SPI_DEV_D0   }]; #SDI (SPI1_COPI)
set_property -dict { PACKAGE_PIN A22 IOSTANDARD LVCMOS33 } [get_ports { SPI_DEV_D1   }]; #SDO (SPI1_CIPO)
set_property -dict { PACKAGE_PIN E25 IOSTANDARD LVCMOS33 } [get_ports { SPI_DEV_D2   }]; # NC (USB_SPARE2)
set_property -dict { PACKAGE_PIN A23 IOSTANDARD LVCMOS33 } [get_ports { SPI_DEV_D3   }]; # NC (USB_SPARE3)
set_property -dict { PACKAGE_PIN C26 IOSTANDARD LVCMOS33 } [get_ports { SPI_DEV_CS_L }]; #CSB (SPI1_CS)

## EarlGrey:SPI_HOST0
set_property -dict { PACKAGE_PIN AF8  IOSTANDARD LVCMOS18                 } [get_ports { SPI_HOST_CLK  }]; #  AF8:USR_SPI0CLK   EarlGrey:SPI_HOST0_SCK
set_property -dict { PACKAGE_PIN AE8  IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { SPI_HOST_D0   }]; #  AE8:USR_SPI0DQ0   EarlGrey:SPI_HOST0_SDO
set_property -dict { PACKAGE_PIN AE10 IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { SPI_HOST_D1   }]; # AE10:USR_SPI0DQ1   EarlGrey:SPI_HOST0_SD1
set_property -dict { PACKAGE_PIN AF9  IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { SPI_HOST_D2   }]; #  AF9:USR_SPI0DQ2   EarlGrey:SPI_HOST0_SD2
set_property -dict { PACKAGE_PIN AF10 IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { SPI_HOST_D3   }]; # AF10:USR_SPI0DQ3   EarlGrey:SPI_HOST0_SD3
set_property -dict { PACKAGE_PIN AE11 IOSTANDARD LVCMOS18                 } [get_ports { SPI_HOST_CS_L }]; # AE11:USR_SPI0CS    EarlGrey:SPI_HOST0_CSB

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
