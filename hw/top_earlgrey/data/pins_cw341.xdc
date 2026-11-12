## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0

## ChipWhisperer CW340 + CW341 "Luna Board".
##

## Clock Signal
set_property -dict { PACKAGE_PIN E22 IOSTANDARD LVCMOS18 } [get_ports { IO_CLK }]; # PLL_CLK2

## Clock constraints
## set via clocks.xdc

## Power-on Reset
set_property -dict { PACKAGE_PIN  G26 IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { POR_N }]; # Main PORN, requires jumper to SW0 CW340:SAM3X_OT_POR SAM3X:PC30

## MIOs
# The sparse pinmux of EG2 only allows routing of every peripheral signal to a small set of pads.
# To still use the existing EG1 specific CW340 setup, some chip pads sit on FPGA pins whose PCB
# nets carry different names:
# - JTAG pads IOA0/1/4/5/6 on the OT_IOR0-4 nets.
# - IOR0/3/4/5/6 on the OT_IOA6/4/5/0/1 nets (the opposite of the JTAG pad swap).
# - IOR1/2 on the OT_IOR5/6 nets. Required as IOR3-6 must reside on the old IOA0/1/4/5 pads so the
#   UART1/UART3 can communicate with the HD's UART (on CN8 6/8/10/12).
# IOC7 is connected to USRUSB_VBUS_DETECT on the CW341, not the OT_IOC7 net.

## IOA bank
set_property -dict { PACKAGE_PIN AL33 IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { IOA0 }]; # EarlGrey:JTAG_TMS,GPIO,UART1_RX
set_property -dict { PACKAGE_PIN AK27 IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { IOA1 }]; # EarlGrey:JTAG_TDO,GPIO,UART1_TX
set_property -dict { PACKAGE_PIN AN27 IOSTANDARD LVCMOS18 } [get_ports { IOA2 }]; # EarlGrey:GPIO,UART0_RX,SPI_HOST0_CSB1,SPI_TPM_CSB,I3C0_SDA_PU
set_property -dict { PACKAGE_PIN AP26 IOSTANDARD LVCMOS18 } [get_ports { IOA3 }]; # EarlGrey:GPIO,UART0_TX,SPI_HOST0_CSB2
set_property -dict { PACKAGE_PIN AK31 IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { IOA4 }]; # EarlGrey:JTAG_TDI,GPIO,UART3_RX,SPI_HOST0_CSB2,SPI_TPM_CSB
set_property -dict { PACKAGE_PIN AL34 IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { IOA5 }]; # EarlGrey:JTAG_TCK,GPIO,UART3_TX,SPI_HOST0_CSB1
set_property -dict { PACKAGE_PIN AJ34 IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { IOA6 }]; # EarlGrey:JTAG_TRSTn,GPIO
set_property -dict { PACKAGE_PIN AN28 IOSTANDARD LVCMOS18 } [get_ports { IOA7 }]; # EarlGrey:GPIO,SPI_TPM_CSB,I2C0_SDA,I2C2_SDA,I3C0_SDA,AST_DEBUG_OUT0
set_property -dict { PACKAGE_PIN AP30 IOSTANDARD LVCMOS18 } [get_ports { IOA8 }]; # EarlGrey:GPIO,I2C0_SCL,I2C2_SCL,I3C0_SCL,AST_DEBUG_OUT1

## IOB bank
set_property -dict { PACKAGE_PIN AP8  IOSTANDARD LVCMOS18 } [get_ports { IOB0  }]; # EarlGrey:GPIO,SPI_HOST1_CSB0
set_property -dict { PACKAGE_PIN AN8  IOSTANDARD LVCMOS18 } [get_ports { IOB1  }]; # EarlGrey:GPIO,SPI_HOST1_SD0
set_property -dict { PACKAGE_PIN AP9  IOSTANDARD LVCMOS18 } [get_ports { IOB2  }]; # EarlGrey:GPIO,SPI_HOST1_SD1
set_property -dict { PACKAGE_PIN AL8  IOSTANDARD LVCMOS18 } [get_ports { IOB3  }]; # EarlGrey:GPIO,SPI_HOST1_SCK
set_property -dict { PACKAGE_PIN AL10 IOSTANDARD LVCMOS18 } [get_ports { IOB4  }]; # EarlGrey:GPIO,SPI_HOST1_SD2,UART2_RX
set_property -dict { PACKAGE_PIN AN9  IOSTANDARD LVCMOS18 } [get_ports { IOB5  }]; # EarlGrey:GPIO,UART2_TX,SPI_HOST1_CSB1
set_property -dict { PACKAGE_PIN AM10 IOSTANDARD LVCMOS18 } [get_ports { IOB6  }]; # EarlGrey:GPIO,SPI_HOST1_SD3
set_property -dict { PACKAGE_PIN AP10 IOSTANDARD LVCMOS18 } [get_ports { IOB7  }]; # EarlGrey:GPIO,UART2_RX,SPI_HOST1_CSB2,I3C1_SDA_PU
set_property -dict { PACKAGE_PIN AL9  IOSTANDARD LVCMOS18 } [get_ports { IOB8  }]; # EarlGrey:GPIO,SPI_HOST1_CSB2,I3C0_SDA_PU
set_property -dict { PACKAGE_PIN AP11 IOSTANDARD LVCMOS18 } [get_ports { IOB9  }]; # EarlGrey:GPIO,I2C0_SCL,I2C2,I3C1_SCL
set_property -dict { PACKAGE_PIN AM12 IOSTANDARD LVCMOS18 } [get_ports { IOB10 }]; # EarlGrey:GPIO,I2C0_SDA,I2C2,I3C1_SDA,I3C1_SDA_PU
set_property -dict { PACKAGE_PIN AN11 IOSTANDARD LVCMOS18 } [get_ports { IOB11 }]; # EarlGrey:GPIO,I2C1,I3C0_SCL,I3C1_SCL
set_property -dict { PACKAGE_PIN AN12 IOSTANDARD LVCMOS18 } [get_ports { IOB12 }]; # EarlGrey:GPIO,I2C1,I3C0_SDA,I3C1_SDA

## IOC bank
set_property -dict { PACKAGE_PIN  T24  IOSTANDARD LVCMOS18 PULLTYPE PULLDOWN } [get_ports { IOC0 }]; # EarlGrey:SW_STRAP0,GPIO,AST_DEBUG_OUT5 CW340:PC23 SAM3X:USBSPARE2
set_property -dict { PACKAGE_PIN  T25  IOSTANDARD LVCMOS18 PULLTYPE PULLDOWN } [get_ports { IOC1 }]; # EarlGrey:SW_STRAP1,GPIO,AST_DEBUG_OUT3 CW340:PC22 SAM3X:USBSPARE1
set_property -dict { PACKAGE_PIN  R27  IOSTANDARD LVCMOS18 PULLTYPE PULLDOWN } [get_ports { IOC2 }]; # EarlGrey:SW_STRAP2,GPIO,AST_DEBUG_OUT4 CW340:PC21 SAM3X:USBSPARE0
set_property -dict { PACKAGE_PIN  P25  IOSTANDARD LVCMOS18 } [get_ports { IOC3 }]; # EarlGrey:UART0_RX,GPIO,AST_DEBUG_OUT7
set_property -dict { PACKAGE_PIN  N24  IOSTANDARD LVCMOS18 } [get_ports { IOC4 }]; # EarlGrey:UART0_TX,GPIO,AST_DEBUG_OUT6
set_property -dict { PACKAGE_PIN  M24  IOSTANDARD LVCMOS18 PULLTYPE PULLDOWN } [get_ports { IOC5 }]; # EarlGrey:TAP_STRAP1,GPIO CW340:PB13 SAM3X:SAM_JTAGSTRAP0
set_property -dict { PACKAGE_PIN  M27  IOSTANDARD LVCMOS18 } [get_ports { IOC6 }]; # EarlGrey:GPIO
set_property -dict { PACKAGE_PIN  B29  IOSTANDARD LVCMOS18 } [get_ports { IOC7 }]; # EarlGrey:GPIO,USB_SENSE
set_property -dict { PACKAGE_PIN  K23  IOSTANDARD LVCMOS18 PULLTYPE PULLDOWN } [get_ports { IOC8 }]; # EarlGrey:TAP_STRAP0,GPIO CW340:PB12 SAM3X:SAM_JTAGSTRAP1
set_property -dict { PACKAGE_PIN  K26  IOSTANDARD LVCMOS18 } [get_ports { IOC9  }]; # EarlGrey:GPIO,I2C2_SCL
set_property -dict { PACKAGE_PIN  J26  IOSTANDARD LVCMOS18 } [get_ports { IOC10 }]; # EarlGrey:GPIO,UART2_RX
set_property -dict { PACKAGE_PIN  H24  IOSTANDARD LVCMOS18 } [get_ports { IOC11 }]; # EarlGrey:GPIO,UART2_TX
set_property -dict { PACKAGE_PIN  H26  IOSTANDARD LVCMOS18 } [get_ports { IOC12 }]; # EarlGrey:GPIO,USB_SENSE,I2C2_SDA

## IOR bank
set_property -dict { PACKAGE_PIN AP29 IOSTANDARD LVCMOS18 } [get_ports { IOR0  }]; # EarlGrey:GPIO,SYSRST_PWRB_IN
set_property -dict { PACKAGE_PIN AK30 IOSTANDARD LVCMOS18 } [get_ports { IOR1  }]; # EarlGrey:GPIO,SYSRST_KEY0_IN
set_property -dict { PACKAGE_PIN AH32 DRIVE 8 IOSTANDARD LVCMOS18 } [get_ports { IOR2  }]; # EarlGrey:GPIO,SYSRST_AC_PRESENT,I3C1_SDA_PU
set_property -dict { PACKAGE_PIN AP28 IOSTANDARD LVCMOS18 } [get_ports { IOR3  }]; # EarlGrey:GPIO,UART3_RX,SYSRST_KEY1_IN
set_property -dict { PACKAGE_PIN AM27 IOSTANDARD LVCMOS18 } [get_ports { IOR4  }]; # EarlGrey:GPIO,UART3_TX,SYSRST_Z3_WAKEUP
set_property -dict { PACKAGE_PIN AN26 IOSTANDARD LVCMOS18 } [get_ports { IOR5  }]; # EarlGrey:GPIO,UART1_RX,SYSRST_KEY2_IN
set_property -dict { PACKAGE_PIN AK26 IOSTANDARD LVCMOS18 } [get_ports { IOR6  }]; # EarlGrey:GPIO,UART1_TX,SYSRST_KEY0_OUT
set_property -dict { PACKAGE_PIN AJ33 DRIVE 8 IOSTANDARD LVCMOS18 } [get_ports { IOR7  }]; # EarlGrey:GPIO,SYSRST_KEY2_OUT,I3C0_SDA_PU
set_property -dict { PACKAGE_PIN AH34 DRIVE 8 IOSTANDARD LVCMOS18 } [get_ports { IOR8  }]; # EarlGrey:SYSRST_EC_RST_L,GPIO
set_property -dict { PACKAGE_PIN AH31 DRIVE 8 IOSTANDARD LVCMOS18 } [get_ports { IOR9  }]; # EarlGrey:SYSRST_FLASH_WP_L,GPIO
set_property -dict { PACKAGE_PIN AH27 DRIVE 8 IOSTANDARD LVCMOS18 } [get_ports { IOR10 }]; # EarlGrey:GPIO,SYSRST_PWRB_OUT,I2C1_SCL,I3C1_SCL
set_property -dict { PACKAGE_PIN AH33 DRIVE 8 IOSTANDARD LVCMOS18 } [get_ports { IOR11 }]; # EarlGrey:GPIO,SYSRST_LID_OPEN,I2C1_SDA,I3C1_SDA,USB_SENSE
set_property -dict { PACKAGE_PIN AH28 DRIVE 8 IOSTANDARD LVCMOS18 } [get_ports { IOR12 }]; # EarlGrey:GPIO,SYSRST_BAT_DISABLE,I2C0_SCL,I3C0_SCL
set_property -dict { PACKAGE_PIN AH26 DRIVE 8 IOSTANDARD LVCMOS18 } [get_ports { IOR13 }]; # EarlGrey:GPIO,SYSRST_KEY1_OUT,I2C0_SDA,I3C0_SDA

## SPI device
set_property -dict { PACKAGE_PIN AM30 IOSTANDARD LVCMOS18 } [get_ports { SPI_DEV_CLK  }]; # CW341:OT_SPI_DEV_CLK
set_property -dict { PACKAGE_PIN AL30 IOSTANDARD LVCMOS18 } [get_ports { SPI_DEV_D0   }]; # CW341:OT_SPI_DEV_D0
set_property -dict { PACKAGE_PIN AM26 IOSTANDARD LVCMOS18 } [get_ports { SPI_DEV_D1   }]; # CW341:OT_SPI_DEV_D1
set_property -dict { PACKAGE_PIN AN32 IOSTANDARD LVCMOS18 } [get_ports { SPI_DEV_D2   }]; # CW341:OT_SPI_DEV_D2
set_property -dict { PACKAGE_PIN AN34 IOSTANDARD LVCMOS18 } [get_ports { SPI_DEV_D3   }]; # CW341:OT_SPI_DEV_D3
set_property -dict { PACKAGE_PIN AM34 IOSTANDARD LVCMOS18 } [get_ports { SPI_DEV_CS_L }]; # CW341:OT_SPI_DEV_CS_L

## SPI HOST
set_property -dict { PACKAGE_PIN AP31 IOSTANDARD LVCMOS18 } [get_ports { SPI_HOST_CLK }]; # CW341:OT_SPI_HOST_CLK
set_property -dict { PACKAGE_PIN AP33 IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { SPI_HOST_D0 }]; # CW341:OT_SPI_HOST_D0
set_property -dict { PACKAGE_PIN AP34 IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { SPI_HOST_D1 }]; # CW341:OT_SPI_HOST_D1
# The D2/D3 pull-ups also set the DFT straps dft0/dft1 to 1, which is harmless on the FPGA
# because dft_hold_tap_sel is tied off and the AST ignores the straps.
set_property -dict { PACKAGE_PIN AL27 IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { SPI_HOST_D2 }]; # CW341:OT_SPI_HOST_D2
set_property -dict { PACKAGE_PIN AN33 IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { SPI_HOST_D3 }]; # CW341:OT_SPI_HOST_D3
set_property -dict { PACKAGE_PIN AL32 IOSTANDARD LVCMOS18 } [get_ports { SPI_HOST_CS_L }]; # CW341:OT_SPI_HOST_CS_L

## ChipWhisperer 20-Pin Connector (J14)
set_property -dict { PACKAGE_PIN AM11 IOSTANDARD LVCMOS18 } [get_ports { IO_TRIGGER }]; # CW341:CWIO_IO4
set_property -dict { PACKAGE_PIN AK12 IOSTANDARD LVCMOS18 } [get_ports { IO_CLKOUT }];  # CW341:CWIO_HS1

## TI TUSB1106 USB PHY usbdev testing
set_property -dict { PACKAGE_PIN E28  IOSTANDARD LVCMOS18 } [get_ports { IO_USB_DP_TX   }]; # CW341:USRUSB_VPO
set_property -dict { PACKAGE_PIN A27  IOSTANDARD LVCMOS18 } [get_ports { IO_USB_DN_TX   }]; # CW341:USRUSB_VMO
set_property -dict { PACKAGE_PIN C27  IOSTANDARD LVCMOS18 } [get_ports { IO_USB_DP_RX   }]; # CW341:USRUSB_VP
set_property -dict { PACKAGE_PIN B27  IOSTANDARD LVCMOS18 } [get_ports { IO_USB_DN_RX   }]; # CW341:USRUSB_VM
set_property -dict { PACKAGE_PIN E27  IOSTANDARD LVCMOS18 } [get_ports { IO_USB_CONNECT }]; # CW341:USRUSB_SOFTCN
set_property -dict { PACKAGE_PIN D24  IOSTANDARD LVCMOS18 } [get_ports { IO_USB_OE_N    }]; # CW341:USRUSB_OE
set_property -dict { PACKAGE_PIN F27  IOSTANDARD LVCMOS18 } [get_ports { IO_USB_D_RX    }]; # CW341:USRUSB_RCV
set_property -dict { PACKAGE_PIN A28  IOSTANDARD LVCMOS18 } [get_ports { IO_USB_SPEED   }]; # CW341:USRUSB_SPD
set_property -dict { PACKAGE_PIN A25  IOSTANDARD LVCMOS18 } [get_ports { IO_USB_SUSPEND }]; # CW341:USRUSB_SUS

## Configuration options, can be used for all designs
set_property CONFIG_VOLTAGE 1.8 [current_design]
set_property CFGBVS GND [current_design]
