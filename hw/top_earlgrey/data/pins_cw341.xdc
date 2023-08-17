## Copyright lowRISC contributors.
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
# All MIOS except for IOC7 are connected to nets of the same name (prefixed
# with OT_ in the PCB design). IOC7 is connected to USRUSB_VBUS_DETECT on the
# CW341, not the OT_IOC7 signal.

## IOA bank
set_property -dict { PACKAGE_PIN AN26 IOSTANDARD LVCMOS18 } [get_ports { IOA0 }]; # EarlGrey:UART2_RX
set_property -dict { PACKAGE_PIN AK26 IOSTANDARD LVCMOS18 } [get_ports { IOA1 }]; # EarlGrey:UART2_TX
set_property -dict { PACKAGE_PIN AN27 IOSTANDARD LVCMOS18 } [get_ports { IOA2 }]; # EarlGrey:GPIO
set_property -dict { PACKAGE_PIN AP26 IOSTANDARD LVCMOS18 } [get_ports { IOA3 }]; # EarlGrey:GPIO
set_property -dict { PACKAGE_PIN AP28 IOSTANDARD LVCMOS18 } [get_ports { IOA4 }]; # EarlGrey:UART3_RX
set_property -dict { PACKAGE_PIN AM27 IOSTANDARD LVCMOS18 } [get_ports { IOA5 }]; # EarlGrey:UART3_TX
set_property -dict { PACKAGE_PIN AP29 IOSTANDARD LVCMOS18 } [get_ports { IOA6 }]; # EarlGrey:GPIO
set_property -dict { PACKAGE_PIN AN28 IOSTANDARD LVCMOS18 } [get_ports { IOA7 }]; # EarlGrey:SPI_TPM_CSB,I2C_TARGET_SDA
set_property -dict { PACKAGE_PIN AP30 IOSTANDARD LVCMOS18 } [get_ports { IOA8 }]; # EarlGrey:I2C_TARGET_SCL

## IOB bank
set_property -dict { PACKAGE_PIN AP8  IOSTANDARD LVCMOS18 } [get_ports { IOB0  }]; # EarlGrey:SPI_HOST1_CSB
set_property -dict { PACKAGE_PIN AN8  IOSTANDARD LVCMOS18 } [get_ports { IOB1  }]; # EarlGrey:SPI_HOST1_CSB
set_property -dict { PACKAGE_PIN AP9  IOSTANDARD LVCMOS18 } [get_ports { IOB2  }]; # EarlGrey:SPI_HOST1_CSB
set_property -dict { PACKAGE_PIN AL8  IOSTANDARD LVCMOS18 } [get_ports { IOB3  }]; # EarlGrey:SPI_HOST1_CSB
set_property -dict { PACKAGE_PIN AL10 IOSTANDARD LVCMOS18 } [get_ports { IOB4  }]; # EarlGrey:UART1_RX
set_property -dict { PACKAGE_PIN AN9  IOSTANDARD LVCMOS18 } [get_ports { IOB5  }]; # EarlGrey:UART1_TX
set_property -dict { PACKAGE_PIN AM10 IOSTANDARD LVCMOS18 } [get_ports { IOB6  }]; # EarlGrey:GPIO
set_property -dict { PACKAGE_PIN AP10 IOSTANDARD LVCMOS18 } [get_ports { IOB7  }]; # EarlGrey:GPIO
set_property -dict { PACKAGE_PIN AL9  IOSTANDARD LVCMOS18 } [get_ports { IOB8  }]; # EarlGrey:GPIO
set_property -dict { PACKAGE_PIN AP11 IOSTANDARD LVCMOS18 } [get_ports { IOB9  }]; # EarlGrey:I2C_HOST_SDA
set_property -dict { PACKAGE_PIN AM12 IOSTANDARD LVCMOS18 } [get_ports { IOB10 }]; # EarlGrey:I2C_HOST_SCL
set_property -dict { PACKAGE_PIN AN11 IOSTANDARD LVCMOS18 } [get_ports { IOB11 }]; # EarlGrey:I2C_HOST_SCL
set_property -dict { PACKAGE_PIN AN12 IOSTANDARD LVCMOS18 } [get_ports { IOB12 }]; # EarlGrey:I2C_HOST_SDA


## IOC bank
set_property -dict { PACKAGE_PIN  T24  IOSTANDARD LVCMOS18 PULLTYPE PULLDOWN } [get_ports { IOC0 }]; # EarlGrey:SW_STRAP0     CW340:PC23 SAM3X:USBSPARE2
set_property -dict { PACKAGE_PIN  T25  IOSTANDARD LVCMOS18 PULLTYPE PULLDOWN } [get_ports { IOC1 }]; # EarlGrey:SW_STRAP1     CW340:PC22 SAM3X:USBSPARE1
set_property -dict { PACKAGE_PIN  R27  IOSTANDARD LVCMOS18 PULLTYPE PULLDOWN } [get_ports { IOC2 }]; # EarlGrey:SW_STRAP2     CW340:PC21 SAM3X:USBSPARE0
set_property -dict { PACKAGE_PIN  P25  IOSTANDARD LVCMOS18 } [get_ports { IOC3 }]; # EarlGrey:UART0_RX
set_property -dict { PACKAGE_PIN  N24  IOSTANDARD LVCMOS18 } [get_ports { IOC4 }]; # EarlGrey:UART0_TX
set_property -dict { PACKAGE_PIN  M24  IOSTANDARD LVCMOS18 PULLTYPE PULLDOWN } [get_ports { IOC5 }]; # EarlGrey:TAP_STRAP1    CW340:PB13 SAM3X:SAM_JTAGSTRAP0
set_property -dict { PACKAGE_PIN  M27  IOSTANDARD LVCMOS18 } [get_ports { IOC6 }]; # EarlGrey:GPIO
set_property -dict { PACKAGE_PIN  B29  IOSTANDARD LVCMOS18 } [get_ports { IOC7 }]; # EarlGrey:VBUS_DETECT
set_property -dict { PACKAGE_PIN  K23  IOSTANDARD LVCMOS18 PULLTYPE PULLDOWN } [get_ports { IOC8 }]; # EarlGrey:TAP_STRAP0    CW340:PB12 SAM3X:SAM_JTAGSTRAP1
set_property -dict { PACKAGE_PIN  K26 IOSTANDARD LVCMOS18 } [get_ports { IOC9  }]; # EarlGrey:GPIO
set_property -dict { PACKAGE_PIN  J26 IOSTANDARD LVCMOS18 } [get_ports { IOC10 }]; # EarlGrey:GPIO
set_property -dict { PACKAGE_PIN  H24 IOSTANDARD LVCMOS18 } [get_ports { IOC11 }]; # EarlGrey:GPIO
set_property -dict { PACKAGE_PIN  H26 IOSTANDARD LVCMOS18 } [get_ports { IOC12 }]; # EarlGrey:GPIO

## IOR bank
# JTAG
set_property -dict { PACKAGE_PIN AL33 IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { IOR0  }]; # EarlGrey:JTAG_TMS
set_property -dict { PACKAGE_PIN AK27 IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { IOR1  }]; # EarlGrey:JTAG_TDO
set_property -dict { PACKAGE_PIN AK31 IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { IOR2  }]; # EarlGrey:JTAG_TDI
set_property -dict { PACKAGE_PIN AL34 IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { IOR3  }]; # EarlGrey:JTAG_TCK
set_property -dict { PACKAGE_PIN AJ34 IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { IOR4  }]; # EarlGrey:JTAG_TRSTn
set_property -dict { PACKAGE_PIN AK30 IOSTANDARD LVCMOS18 } [get_ports { IOR5  }]; # EarlGrey:GPIO
set_property -dict { PACKAGE_PIN AH32 DRIVE 8 IOSTANDARD LVCMOS18 } [get_ports { IOR6  }]; # EarlGrey:GPIO(LED0)
set_property -dict { PACKAGE_PIN AJ33 DRIVE 8 IOSTANDARD LVCMOS18 } [get_ports { IOR7  }]; # EarlGrey:GPIO(LED1)
set_property -dict { PACKAGE_PIN AH34 DRIVE 8 IOSTANDARD LVCMOS18 } [get_ports { IOR8  }]; # EarlGrey:GPIO(LED2)
set_property -dict { PACKAGE_PIN AH31 DRIVE 8 IOSTANDARD LVCMOS18 } [get_ports { IOR9  }]; # EarlGrey:GPIO(LED3)
set_property -dict { PACKAGE_PIN AH27 DRIVE 8 IOSTANDARD LVCMOS18 } [get_ports { IOR10 }]; # EarlGrey:GPIO(LED4)
set_property -dict { PACKAGE_PIN AH33 DRIVE 8 IOSTANDARD LVCMOS18 } [get_ports { IOR11 }]; # EarlGrey:GPIO(LED5)
set_property -dict { PACKAGE_PIN AH28 DRIVE 8 IOSTANDARD LVCMOS18 } [get_ports { IOR12 }]; # EarlGrey:GPIO(LED6)
set_property -dict { PACKAGE_PIN AH26 DRIVE 8 IOSTANDARD LVCMOS18 } [get_ports { IOR13 }]; # EarlGrey:GPIO(LED7)

## DIOs
# For DIOs, the port name maps directly to the function in Earl Grey, so
# instead, the net names on the PCB are provided in comments.

## SPI device
set_property -dict { PACKAGE_PIN AM30 IOSTANDARD LVCMOS18 } [get_ports { SPI_DEV_CLK  }]; # CW341:OT_SPI_DEVICE_CLK
set_property -dict { PACKAGE_PIN AL30 IOSTANDARD LVCMOS18 } [get_ports { SPI_DEV_D0   }]; # CW341:OT_SPI_DEVICE_D0
set_property -dict { PACKAGE_PIN AM26 IOSTANDARD LVCMOS18 } [get_ports { SPI_DEV_D1   }]; # CW341:OT_SPI_DEVICE_D1
set_property -dict { PACKAGE_PIN AN32 IOSTANDARD LVCMOS18 } [get_ports { SPI_DEV_D2   }]; # CW341:OT_SPI_DEVICE_D2
set_property -dict { PACKAGE_PIN AN34 IOSTANDARD LVCMOS18 } [get_ports { SPI_DEV_D3   }]; # CW341:OT_SPI_DEVICE_D3
set_property -dict { PACKAGE_PIN AM34 IOSTANDARD LVCMOS18 } [get_ports { SPI_DEV_CS_L }]; # CW341:OT_SPI_DEVICE_CS_L

## SPI HOST
set_property -dict { PACKAGE_PIN AP31 IOSTANDARD LVCMOS18 } [get_ports { SPI_HOST_CLK }]; # CW341:OT_SPI_HOST_CLK
set_property -dict { PACKAGE_PIN AP33 IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { SPI_HOST_D0 }]; # CW341:OT_SPI_HOST_D0
set_property -dict { PACKAGE_PIN AP34 IOSTANDARD LVCMOS18 PULLTYPE PULLUP } [get_ports { SPI_HOST_D1 }]; # CW341:OT_SPI_HOST_D1
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
set_property -dict { PACKAGE_PIN E27  IOSTANDARD LVCMOS18 } [get_ports { IO_USB_CONNECT }]; # CW341:USRUSB_SOFTCON
set_property -dict { PACKAGE_PIN D24  IOSTANDARD LVCMOS18 } [get_ports { IO_USB_OE_N    }]; # CW341:USRUSB_OE
set_property -dict { PACKAGE_PIN F27  IOSTANDARD LVCMOS18 } [get_ports { IO_USB_D_RX    }]; # CW341:USRUSB_RCV
set_property -dict { PACKAGE_PIN A28  IOSTANDARD LVCMOS18 } [get_ports { IO_USB_SPEED   }]; # CW341:USRUSB_VMO
set_property -dict { PACKAGE_PIN A25  IOSTANDARD LVCMOS18 } [get_ports { IO_USB_SUSPEND }]; # CW341:USRUSB_VMO

## Configuration options, can be used for all designs
set_property CONFIG_VOLTAGE 1.8 [current_design]
set_property CFGBVS GND [current_design]
