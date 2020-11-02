## Partially based on https://github.com/newaetech/chipwhisperer/blob/develop/hardware/victims/cw305_artixtarget/fpga/common/cw305_main.xdc
## Tested with a A100T FPGA configuration.

## Clock Signal
set_property -dict { PACKAGE_PIN N13 IOSTANDARD LVCMOS33 } [get_ports { IO_CLK }]

## Clock constraints
## set via clocks.xdc

## LEDs
set_property -dict { PACKAGE_PIN T2  DRIVE 8 IOSTANDARD LVCMOS33 } [get_ports { IO_GP8 }]
set_property -dict { PACKAGE_PIN T3  DRIVE 8 IOSTANDARD LVCMOS33 } [get_ports { IO_GP9 }]
set_property -dict { PACKAGE_PIN T4  DRIVE 8 IOSTANDARD LVCMOS33 } [get_ports { IO_GP10 }]

## Buttons
set_property -dict { PACKAGE_PIN R1 IOSTANDARD LVCMOS33 } [get_ports { IO_RST_N }]; #pushbutton

## Switches
set_property -dict { PACKAGE_PIN J16 IOSTANDARD LVCMOS33 } [get_ports { IO_GP0 }]; #sw1
set_property -dict { PACKAGE_PIN K16 IOSTANDARD LVCMOS33 } [get_ports { IO_GP1 }]; #sw2
set_property -dict { PACKAGE_PIN K15 IOSTANDARD LVCMOS33 } [get_ports { IO_GP2 }]; #sw3
set_property -dict { PACKAGE_PIN L14 IOSTANDARD LVCMOS33 } [get_ports { IO_GP3 }]; #sw4

## SPI/JTAG
set_property -dict { PACKAGE_PIN L2 IOSTANDARD LVCMOS33 } [get_ports { IO_DPS0 }]; #SCK (USB_A13)
set_property -dict { PACKAGE_PIN J3 IOSTANDARD LVCMOS33 } [get_ports { IO_DPS1 }]; #SDI (USB_A14)
set_property -dict { PACKAGE_PIN B2 IOSTANDARD LVCMOS33 } [get_ports { IO_DPS2 }]; #SDO (USB_A15)
set_property -dict { PACKAGE_PIN C7 IOSTANDARD LVCMOS33 } [get_ports { IO_DPS3 }]; #CSB (USB_A16)
set_property -dict { PACKAGE_PIN C6 IOSTANDARD LVCMOS33 } [get_ports { IO_DPS4 }]; #JTAG TRST (USB_A17)
set_property -dict { PACKAGE_PIN D6 IOSTANDARD LVCMOS33 PULLTYPE PULLUP } [get_ports { IO_DPS5 }]; #JTAG SRST (USB_A18)
set_property -dict { PACKAGE_PIN C4 IOSTANDARD LVCMOS33 PULLTYPE PULLDOWN } [get_ports { IO_DPS6 }]; #JTAG/SPI (USB_A19)
set_property -dict { PACKAGE_PIN D5 IOSTANDARD LVCMOS33 PULLTYPE PULLDOWN } [get_ports { IO_DPS7 }]; #Bootstrap (USB_A20)

## OTHER IO
set_property -dict { PACKAGE_PIN B16 IOSTANDARD LVCMOS33 } [get_ports { IO_GP4  }]; #JP3.B16
set_property -dict { PACKAGE_PIN C13 IOSTANDARD LVCMOS33 } [get_ports { IO_GP5  }]; #JP3.C13
set_property -dict { PACKAGE_PIN D15 IOSTANDARD LVCMOS33 } [get_ports { IO_GP6  }]; #JP3.D15
set_property -dict { PACKAGE_PIN E15 IOSTANDARD LVCMOS33 } [get_ports { IO_GP7  }]; #JP3.E15
set_property -dict { PACKAGE_PIN E13 IOSTANDARD LVCMOS33 } [get_ports { IO_GP11 }]; #JP3.E13
set_property -dict { PACKAGE_PIN F15 IOSTANDARD LVCMOS33 } [get_ports { IO_GP12 }]; #JP3.F15
set_property -dict { PACKAGE_PIN E11 IOSTANDARD LVCMOS33 } [get_ports { IO_GP13 }]; #JP3.E11
set_property -dict { PACKAGE_PIN F13 IOSTANDARD LVCMOS33 } [get_ports { IO_GP14 }]; #JP3.F13

set_property -dict { PACKAGE_PIN C16 IOSTANDARD LVCMOS33 DRIVE 8 SLEW FAST } [get_ports { IO_USB_DP0 }]; #JP3.C16
set_property -dict { PACKAGE_PIN D13 IOSTANDARD LVCMOS33 DRIVE 8 SLEW FAST } [get_ports { IO_USB_DN0 }]; #JP3.D13
set_property -dict { PACKAGE_PIN H16 IOSTANDARD LVCMOS33 } [get_ports { IO_USB_DPPULLUP0 }]; #JP3.H16
set_property -dict { PACKAGE_PIN D16 IOSTANDARD LVCMOS33 } [get_ports { IO_USB_SENSE0 }]; #JP3.D16
set_property -dict { PACKAGE_PIN E16 IOSTANDARD LVCMOS33 } [get_ports { IO_USB_DNPULLUP0 }]; #JP3.E16

set_property -dict { PACKAGE_PIN G16 IOSTANDARD LVCMOS33 } [get_ports { IO_UTX_DEBUG }]; #JP3.G16 (UART) for debugging

## Unused pins of JP3: A12, B12, F12

## 20-Pin Connector (JP1)

set_property -dict { PACKAGE_PIN R16 IOSTANDARD LVCMOS33 } [get_ports { IO_UTX }];     #JP1 PIN 10 (UART)
set_property -dict { PACKAGE_PIN P16 IOSTANDARD LVCMOS33 } [get_ports { IO_URX }];     #JP1 PIN 12 (UART)
set_property -dict { PACKAGE_PIN T14 IOSTANDARD LVCMOS33 } [get_ports { IO_GP15 }];    #JP1 PIN 16 TIO4 (Trigger)
set_property -dict { PACKAGE_PIN M16 IOSTANDARD LVCMOS33 } [get_ports { TIO_CLKOUT }]; #JP1 PIN 4 TIO_HS1. Clock sync capture board.


## USB Connector
# TODO: Configure USB capture interface and sync triggers.

#set_property PACKAGE_PIN F5 [get_ports usb_clk]

#set_property IOSTANDARD LVCMOS33 [get_ports *]
#set_property PACKAGE_PIN A7 [get_ports {usb_data[0]}]
#set_property PACKAGE_PIN B6 [get_ports {usb_data[1]}]
#set_property PACKAGE_PIN D3 [get_ports {usb_data[2]}]
#set_property PACKAGE_PIN E3 [get_ports {usb_data[3]}]
#set_property PACKAGE_PIN F3 [get_ports {usb_data[4]}]
#set_property PACKAGE_PIN B5 [get_ports {usb_data[5]}]
#set_property PACKAGE_PIN K1 [get_ports {usb_data[6]}]
#set_property PACKAGE_PIN K2 [get_ports {usb_data[7]}]

#set_property PACKAGE_PIN F4 [get_ports {usb_addr[0]}]
#set_property PACKAGE_PIN G5 [get_ports {usb_addr[1]}]
#set_property PACKAGE_PIN J1 [get_ports {usb_addr[2]}]
#set_property PACKAGE_PIN H1 [get_ports {usb_addr[3]}]
#set_property PACKAGE_PIN H2 [get_ports {usb_addr[4]}]
#set_property PACKAGE_PIN G1 [get_ports {usb_addr[5]}]
#set_property PACKAGE_PIN G2 [get_ports {usb_addr[6]}]
#set_property PACKAGE_PIN F2 [get_ports {usb_addr[7]}]
#set_property PACKAGE_PIN E1 [get_ports {usb_addr[8]}]
#set_property PACKAGE_PIN E2 [get_ports {usb_addr[9]}]
#set_property PACKAGE_PIN D1 [get_ports {usb_addr[10]}]
#set_property PACKAGE_PIN C1 [get_ports {usb_addr[11]}]
#set_property PACKAGE_PIN K3 [get_ports {usb_addr[12]}]
#set_property PACKAGE_PIN L2 [get_ports {usb_addr[13]}]
#set_property PACKAGE_PIN J3 [get_ports {usb_addr[14]}]
#set_property PACKAGE_PIN B2 [get_ports {usb_addr[15]}]
#set_property PACKAGE_PIN C7 [get_ports {usb_addr[16]}]
#set_property PACKAGE_PIN C6 [get_ports {usb_addr[17]}]
#set_property PACKAGE_PIN D6 [get_ports {usb_addr[18]}]
#set_property PACKAGE_PIN C4 [get_ports {usb_addr[19]}]
#set_property PACKAGE_PIN D5 [get_ports {usb_addr[20]}]

#set_property PACKAGE_PIN A4 [get_ports usb_rdn]
#set_property PACKAGE_PIN C2 [get_ports usb_wrn]
#set_property PACKAGE_PIN A3 [get_ports usb_cen]

#set_property PACKAGE_PIN A5 [get_ports usb_trigger]

#set_property CLOCK_DEDICATED_ROUTE FALSE [get_nets usb_clk]
#set_property CLOCK_DEDICATED_ROUTE FALSE [get_nets crypt_clk]


#create_clock -period 10.000 -name usb_clk -waveform {0.000 5.000} [get_nets usb_clk]
#create_clock -period 10.000 -name tio_clkin -waveform {0.000 5.000} [get_nets tio_clkin]
#create_clock -period 10.000 -name pll_clk1 -waveform {0.000 5.000} [get_nets pll_clk1]

#set_input_delay -clock [get_clocks -filter { NAME =~  "*usb_clk*" }] 3.000 [get_ports -filter { NAME =~  "*usb_data*" && DIRECTION == "INOUT" }]

#set_property CLOCK_DEDICATED_ROUTE FALSE [get_nets usb_rdn]
#set_property CLOCK_DEDICATED_ROUTE FALSE [get_nets usb_wrn]


## Configuration options, can be used for all designs
set_property CONFIG_VOLTAGE 3.3 [current_design]
set_property CFGBVS VCCO [current_design]
