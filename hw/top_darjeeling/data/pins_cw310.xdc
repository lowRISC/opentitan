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
## set_property KEEP_HIERARCHY TRUE [get_cells top_darjeeling/u_flash_eflash/gen_flash_banks[*].i_core/u_scramble/u_cipher]
## set_multicycle_path -setup 2 -through [get_pins -of_objects [get_cells top_darjeeling/u_flash_eflash/gen_flash_banks[*].i_core/u_scramble/u_cipher]]
## set_multicycle_path -hold 1  -through [get_pins -of_objects [get_cells top_darjeeling/u_flash_eflash/gen_flash_banks[*].i_core/u_scramble/u_cipher]]

#set_property CLOCK_DEDICATED_ROUTE FALSE [get_nets IO_SDCK_IBUF]; # SDCK clock to be ignored

########################################################
## MIOs ##

# darjeeling-pinmux pad banks
# See hw/top_darjeeling/data/top_darjeeling.hjson['pinout']['pads']
#
# __Comment_Structure__
# K410T_PACKAGE_PIN:CW310_SCHEMATIC_SIGNAL_NAME  TEST_PINMUX_MAPPING(typical)   CONNECTED_HW
#              AA22:SAM_RXD1                     Darjeeling:UART0_TX              (SAM3X)
##############
## IOA bank ##
##############                                                                     #
set_property -dict { PACKAGE_PIN AA24 IOSTANDARD LVCMOS33 } [get_ports { GPIO0  }]; # AA24:SAM_TXD0   Darjeeling:GPIO (SAM3X)
set_property -dict { PACKAGE_PIN AB22 IOSTANDARD LVCMOS33 } [get_ports { GPIO1  }]; # AB22:SAM_RXD0   Darjeeling:GPIO (SAM3X)
set_property -dict { PACKAGE_PIN N17  IOSTANDARD LVCMOS33 } [get_ports { GPIO2  }]; #  N17:PMOD1_IO1  Darjeeling:GPIO (BoB):PMOD2_CSB0
set_property -dict { PACKAGE_PIN T22  IOSTANDARD LVCMOS33 } [get_ports { GPIO3  }]; #  T22:PMOD1_IO4  Darjeeling:GPIO (BoB):PMOD2_SCLK
set_property -dict { PACKAGE_PIN R23  IOSTANDARD LVCMOS33 } [get_ports { GPIO4  }]; #  R23:PMOD1_IO3  Darjeeling:GPIO (BoB):PMOD2_SIO1
set_property -dict { PACKAGE_PIN R26  IOSTANDARD LVCMOS33 } [get_ports { GPIO5  }]; #  R26:PMOD1_IO2  Darjeeling:GPIO (BoB):PMOD2_SIO0
set_property -dict { PACKAGE_PIN R25  IOSTANDARD LVCMOS33 } [get_ports { GPIO6  }]; #  R25:PMOD1_IO5  Darjeeling:GPIO (BoB):PMOD2_CSB1
set_property -dict { PACKAGE_PIN T23  IOSTANDARD LVCMOS33 } [get_ports { GPIO7  }]; #  T23:PMOD1_IO8  Darjeeling:GPIO (BoB):PMOD2_SIO3
set_property -dict { PACKAGE_PIN P23  IOSTANDARD LVCMOS33 } [get_ports { GPIO8  }]; #  P23:PMOD1_IO7  Darjeeling:GPIO (BoB):PMOD2_SIO2
#############
## IOB bank #
#############
set_property -dict { PACKAGE_PIN F12  IOSTANDARD LVCMOS33 } [get_ports { GPIO9  }]; #  F12:USR_SPI1CLK  Darjeeling:GPIO
set_property -dict { PACKAGE_PIN E11  IOSTANDARD LVCMOS33 } [get_ports { GPIO10 }]; #  E11:USR_SPI1DQ0  Darjeeling:GPIO
set_property -dict { PACKAGE_PIN A15  IOSTANDARD LVCMOS33 } [get_ports { GPIO11 }]; #  A15:USR_SPI1DQ1  Darjeeling:GPIO
set_property -dict { PACKAGE_PIN F14  IOSTANDARD LVCMOS33 } [get_ports { GPIO12 }]; #  F14:USR_SPI1CS   Darjeeling:GPIO
set_property -dict { PACKAGE_PIN AE25 IOSTANDARD LVCMOS33 } [get_ports { GPIO13 }]; # AE25:CWIO_IO1     Darjeeling:GPIO       ChipWhisperer_ConnectorJ14_PIN10
set_property -dict { PACKAGE_PIN AF25 IOSTANDARD LVCMOS33 } [get_ports { GPIO14 }]; # AF25:CWIO_IO2     Darjeeling:GPIO       ChipWhisperer_ConnectorJ14_PIN12
set_property -dict { PACKAGE_PIN U9   IOSTANDARD LVCMOS18 } [get_ports { GPIO15 }]; #   U9:USRDIP0      Darjeeling:GPIO       DIP switches
set_property -dict { PACKAGE_PIN N23  IOSTANDARD LVCMOS33 } [get_ports { GPIO16 }]; #  N23:PMOD2_IO5    Darjeeling:GPIO       (BoB):PMOD1_CSB7
set_property -dict { PACKAGE_PIN N26  IOSTANDARD LVCMOS33 } [get_ports { GPIO17 }]; #  N26:PMOD2_IO6    Darjeeling:GPIO       (BoB):PMOD1_RST
set_property -dict { PACKAGE_PIN V7   IOSTANDARD LVCMOS18 } [get_ports { GPIO18 }]; #   V7:USRDIP1      Darjeeling:GPIO       DIP switches
set_property -dict { PACKAGE_PIN V8   IOSTANDARD LVCMOS18 } [get_ports { GPIO19 }]; #   V8:USRDIP2      Darjeeling:GPIO       DIP switches
set_property -dict { PACKAGE_PIN M20  IOSTANDARD LVCMOS33 } [get_ports { I2C_SCL }]; #  M20:PMOD2_IO7    Darjeeling:I2C0_SCL   (BoB):PMOD1_I2C_SCL
set_property -dict { PACKAGE_PIN P25  IOSTANDARD LVCMOS33 } [get_ports { I2C_SDA }]; #  P25:PMOD2_IO8    Darjeeling:I2C0_SDA   (BoB):PMOD1_I2C_SDA
#############
## IOC bank #
#############
set_property -dict { PACKAGE_PIN V22  IOSTANDARD LVCMOS33 PULLTYPE PULLDOWN } [get_ports { GPIO22  }]; #  V22:USB_A15             SW Strap 0            (SAM3X):A15
set_property -dict { PACKAGE_PIN U21  IOSTANDARD LVCMOS33 PULLTYPE PULLDOWN } [get_ports { GPIO23  }]; #  U21:USB_A16             SW Strap 1            (SAM3X):A16
set_property -dict { PACKAGE_PIN V21  IOSTANDARD LVCMOS33 PULLTYPE PULLDOWN } [get_ports { GPIO24  }]; #  V21:USB_A17             SW Strap 2            (SAM3X):A17
set_property -dict { PACKAGE_PIN W24  IOSTANDARD LVCMOS33                   } [get_ports { UART_RX  }]; #  W24:SAM_TXD1           Darjeeling:UART0_RX   (SAM3X)
set_property -dict { PACKAGE_PIN AA22 IOSTANDARD LVCMOS33                   } [get_ports { UART_TX  }]; # AA22:SAM_RXD1           Darjeeling:UART0_TX   (SAM3X)
set_property -dict { PACKAGE_PIN W20  IOSTANDARD LVCMOS33 PULLTYPE PULLDOWN } [get_ports { MIO1  }]; #  W20:USB_A19               TAP Strap 1           (SAM3X):A19
set_property -dict { PACKAGE_PIN M21  IOSTANDARD LVCMOS33                   } [get_ports { MIO2  }]; #  M21:PMOD2_IO2             Darjeeling:GPIO       (BoB):PMOD1_CSB4
set_property -dict { PACKAGE_PIN P18  IOSTANDARD LVCMOS33                   } [get_ports { MIO3  }]; #  P18:USRUSB_VBUS_DETECT    Darjeeling:GPIO
set_property -dict { PACKAGE_PIN W21  IOSTANDARD LVCMOS33 PULLTYPE PULLDOWN } [get_ports { MIO0  }]; #  W21:USB_A18               TAP Strap 0           (SAM3X):A18
set_property -dict { PACKAGE_PIN M22  IOSTANDARD LVCMOS33                   } [get_ports { GPIO20  }]; #  M22:PMOD2_IO1           Darjeeling:GPIO       (BoB):PMOD1_CSB3
set_property -dict { PACKAGE_PIN N19  IOSTANDARD LVCMOS33                   } [get_ports { MIO9 }]; #  N19:PMOD2_IO3              Darjeeling:GPIO       (BoB):PMOD1_CSB5
set_property -dict { PACKAGE_PIN P26  IOSTANDARD LVCMOS33                   } [get_ports { MIO10 }]; #  P26:PMOD2_IO4             Darjeeling:GPIO       (BoB):PMOD1_CSB6
set_property -dict { PACKAGE_PIN P24  IOSTANDARD LVCMOS33                   } [get_ports { MIO11 }]; #  P24:PMOD1_IO6             Darjeeling:GPIO       (BoB):PMOD2_CSB2
#############
## IOR bank #
#############
set_property -dict { PACKAGE_PIN N16         IOSTANDARD LVCMOS33 PULLTYPE PULLUP } [get_ports { JTAG_TMS    }]; # N16:USR_DBG_TMS           JTAG
set_property -dict { PACKAGE_PIN P16         IOSTANDARD LVCMOS33 PULLTYPE PULLUP } [get_ports { JTAG_TDO    }]; # P16:USR_DBG_TDO           JTAG
set_property -dict { PACKAGE_PIN R16         IOSTANDARD LVCMOS33 PULLTYPE PULLUP } [get_ports { JTAG_TDI    }]; # R16:USR_DBG_TDI           JTAG
set_property -dict { PACKAGE_PIN N18         IOSTANDARD LVCMOS33 PULLTYPE PULLUP } [get_ports { JTAG_TCK    }]; # N18:USR_DBG_TCK           JTAG
set_property -dict { PACKAGE_PIN U19         IOSTANDARD LVCMOS33 PULLTYPE PULLUP } [get_ports { JTAG_TRST_N }]; # U19:USR_DBG_TDAT1(nTRST)  JTAG
set_property -dict { PACKAGE_PIN V9          IOSTANDARD LVCMOS18                 } [get_ports { MIO5  }]; #  V9:USRDIP4               Darjeeling:GPIO
set_property -dict { PACKAGE_PIN W8          IOSTANDARD LVCMOS18                 } [get_ports { MIO8  }]; #  W8:USRDIP5               Darjeeling:GPIO
set_property -dict { PACKAGE_PIN W10         IOSTANDARD LVCMOS18                 } [get_ports { MIO7  }]; # W10:USRDIP6               Darjeeling:GPIO
set_property -dict { PACKAGE_PIN V11         IOSTANDARD LVCMOS18                 } [get_ports { MIO4  }]; # V11:USRDIP7               Darjeeling:GPIO
set_property -dict { PACKAGE_PIN Y11         IOSTANDARD LVCMOS18                 } [get_ports { MIO6  }]; # Y11:USR_SW0               Darjeeling:GPIO
set_property -dict { PACKAGE_PIN W9          IOSTANDARD LVCMOS18                 } [get_ports { GPIO21  }]; #  W9:USRDIP3             Darjeeling:GPIO
set_property -dict { PACKAGE_PIN M26 DRIVE 8 IOSTANDARD LVCMOS33                 } [get_ports { GPIO25  }]; # M26:USRLED0             Darjeeling:GPIO
set_property -dict { PACKAGE_PIN M25 DRIVE 8 IOSTANDARD LVCMOS33                 } [get_ports { GPIO26  }]; # M25:USRLED1             Darjeeling:GPIO
set_property -dict { PACKAGE_PIN M24 DRIVE 8 IOSTANDARD LVCMOS33                 } [get_ports { GPIO27  }]; # M24:USRLED2             Darjeeling:GPIO
set_property -dict { PACKAGE_PIN M19 DRIVE 8 IOSTANDARD LVCMOS33                 } [get_ports { GPIO28  }]; # M19:USRLED3             Darjeeling:GPIO
set_property -dict { PACKAGE_PIN L25 DRIVE 8 IOSTANDARD LVCMOS33                 } [get_ports { GPIO29  }]; # L25:USRLED4             Darjeeling:GPIO
set_property -dict { PACKAGE_PIN K26 DRIVE 8 IOSTANDARD LVCMOS33                 } [get_ports { GPIO30  }]; # K26:USRLED5             Darjeeling:GPIO
set_property -dict { PACKAGE_PIN L24 DRIVE 8 IOSTANDARD LVCMOS33                 } [get_ports { GPIO31  }]; # L24:USRLED6             Darjeeling:GPIO

########################################################
## DIOs ##

## SPI device
set_property -dict { PACKAGE_PIN D26 IOSTANDARD LVCMOS33 } [get_ports { SPI_DEV_CLK      }]; #SCK (SPI1_SCK)
set_property -dict { PACKAGE_PIN A24 IOSTANDARD LVCMOS33 } [get_ports { SPI_DEV_D0       }]; #SDI (SPI1_COPI)
set_property -dict { PACKAGE_PIN A22 IOSTANDARD LVCMOS33 } [get_ports { SPI_DEV_D1       }]; #SDO (SPI1_CIPO)
set_property -dict { PACKAGE_PIN E25 IOSTANDARD LVCMOS33 } [get_ports { SPI_DEV_D2       }]; # NC (USB_SPARE2)
set_property -dict { PACKAGE_PIN A23 IOSTANDARD LVCMOS33 } [get_ports { SPI_DEV_D3       }]; # NC (USB_SPARE3)
set_property -dict { PACKAGE_PIN C26 IOSTANDARD LVCMOS33 } [get_ports { SPI_DEV_CS_L     }]; #CSB (SPI1_CS)
set_property -dict { PACKAGE_PIN G25 IOSTANDARD LVCMOS33 } [get_ports { SPI_DEV_TPM_CS_L }]; #USB_SPARE1

## Darjeeling:SPI_HOST0
set_property -dict { PACKAGE_PIN AF8  IOSTANDARD LVCMOS18                 } [get_ports { SPI_HOST_CLK  }]; #  AF8:USR_SPI0CLK   Darjeeling:SPI_HOST0_SCK
set_property -dict { PACKAGE_PIN AE8  IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { SPI_HOST_D0   }]; #  AE8:USR_SPI0DQ0   Darjeeling:SPI_HOST0_SDO
set_property -dict { PACKAGE_PIN AE10 IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { SPI_HOST_D1   }]; # AE10:USR_SPI0DQ1   Darjeeling:SPI_HOST0_SD1
set_property -dict { PACKAGE_PIN AF9  IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { SPI_HOST_D2   }]; #  AF9:USR_SPI0DQ2   Darjeeling:SPI_HOST0_SD2
set_property -dict { PACKAGE_PIN AF10 IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { SPI_HOST_D3   }]; # AF10:USR_SPI0DQ3   Darjeeling:SPI_HOST0_SD3
set_property -dict { PACKAGE_PIN AE11 IOSTANDARD LVCMOS18                 } [get_ports { SPI_HOST_CS_L }]; # AE11:USR_SPI0CS    Darjeeling:SPI_HOST0_CSB

## ChipWhisperer 20-Pin Connector (J14)
set_property -dict { PACKAGE_PIN AF24 IOSTANDARD LVCMOS33 } [get_ports { IO_TRIGGER }]; #J14 PIN 16 CWIO_IO4 - Capture Trigger
set_property -dict { PACKAGE_PIN AB21 IOSTANDARD LVCMOS33 } [get_ports { IO_CLKOUT }];  #J14 PIN  4 CWIO_HS1 - Target clock

## SoC GPIOs
set_property -dict { PACKAGE_PIN C12  IOSTANDARD LVCMOS33 } [get_ports { SOC_GPI0  }]; # C12:USERIOB-1
set_property -dict { PACKAGE_PIN D13  IOSTANDARD LVCMOS33 } [get_ports { SOC_GPI1  }]; # D13:USERIOB-3
set_property -dict { PACKAGE_PIN C13  IOSTANDARD LVCMOS33 } [get_ports { SOC_GPI2  }]; # C13:USERIOB-5
set_property -dict { PACKAGE_PIN E13  IOSTANDARD LVCMOS33 } [get_ports { SOC_GPI3  }]; # E13:USERIOB-7
set_property -dict { PACKAGE_PIN A8   IOSTANDARD LVCMOS33 } [get_ports { SOC_GPI4  }]; #  A8:USERIOB-9
set_property -dict { PACKAGE_PIN B9   IOSTANDARD LVCMOS33 } [get_ports { SOC_GPI5  }]; #  B9:USERIOB-11
set_property -dict { PACKAGE_PIN A9   IOSTANDARD LVCMOS33 } [get_ports { SOC_GPI6  }]; #  A9:USERIOB-15
set_property -dict { PACKAGE_PIN B10  IOSTANDARD LVCMOS33 } [get_ports { SOC_GPI7  }]; # B10:USERIOB-17
set_property -dict { PACKAGE_PIN A10  IOSTANDARD LVCMOS33 } [get_ports { SOC_GPI8  }]; # A10:USERIOB-19
set_property -dict { PACKAGE_PIN B11  IOSTANDARD LVCMOS33 } [get_ports { SOC_GPI9  }]; # B11:USERIOB-21
set_property -dict { PACKAGE_PIN B12  IOSTANDARD LVCMOS33 } [get_ports { SOC_GPI10 }]; # B12:USERIOB-23
set_property -dict { PACKAGE_PIN A12  IOSTANDARD LVCMOS33 } [get_ports { SOC_GPI11 }]; # A12:USERIOB-25
set_property -dict { PACKAGE_PIN F10  IOSTANDARD LVCMOS33 } [get_ports { SOC_GPO0  }]; # F10:USERIOB-6
set_property -dict { PACKAGE_PIN H8   IOSTANDARD LVCMOS33 } [get_ports { SOC_GPO1  }]; #  H8:USERIOB-8
set_property -dict { PACKAGE_PIN F8   IOSTANDARD LVCMOS33 } [get_ports { SOC_GPO2  }]; #  F8:USERIOB-10
set_property -dict { PACKAGE_PIN F9   IOSTANDARD LVCMOS33 } [get_ports { SOC_GPO3  }]; #  F9:USERIOB-12
set_property -dict { PACKAGE_PIN E10  IOSTANDARD LVCMOS33 } [get_ports { SOC_GPO4  }]; # E10:USERIOB-14
set_property -dict { PACKAGE_PIN D8   IOSTANDARD LVCMOS33 } [get_ports { SOC_GPO5  }]; #  D8:USERIOB-16
set_property -dict { PACKAGE_PIN D9   IOSTANDARD LVCMOS33 } [get_ports { SOC_GPO6  }]; #  D9:USERIOB-18
set_property -dict { PACKAGE_PIN C9   IOSTANDARD LVCMOS33 } [get_ports { SOC_GPO7  }]; #  C9:USERIOB-24
set_property -dict { PACKAGE_PIN D10  IOSTANDARD LVCMOS33 } [get_ports { SOC_GPO8  }]; # D10:USERIOB-26
set_property -dict { PACKAGE_PIN E12  IOSTANDARD LVCMOS33 } [get_ports { SOC_GPO9  }]; # E12:USERIOB-28
set_property -dict { PACKAGE_PIN C11  IOSTANDARD LVCMOS33 } [get_ports { SOC_GPO10 }]; # C11:USERIOB-30
set_property -dict { PACKAGE_PIN D11  IOSTANDARD LVCMOS33 } [get_ports { SOC_GPO11 }]; # D11:USERIOB-32

## Configuration options, can be used for all designs
set_property CONFIG_VOLTAGE 3.3 [current_design]
set_property CFGBVS VCCO [current_design]
