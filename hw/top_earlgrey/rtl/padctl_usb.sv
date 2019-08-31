// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module padctl_usb (
  // UART device side
  input   cio_uart_tx_d2p,
  input   cio_uart_tx_en_d2p,
  output  cio_uart_rx_p2d,
  // USB device side
  output        cio_usb_dp_p2d[2],
  input         cio_usb_dp_d2p[2],
  input         cio_usb_dp_en_d2p[2],
  output        cio_usb_dn_p2d[2],
  input         cio_usb_dn_d2p[2],
  input         cio_usb_dn_en_d2p[2],
  output        cio_usb_sense_p2d[2],
  input         cio_usb_pullup_d2p[2],
  input         cio_usb_pullup_en_d2p[2],

  // UART pads
  input   IO_URX,
  output  IO_UTX,

  // USB pads
  inout         IO_USB_DP0,
  inout         IO_USB_DN0,
  input         IO_USB_SENSE0,
  output        IO_USB_PULLUP0,
  inout         IO_USB_DP1,
  inout         IO_USB_DN1,
  input         IO_USB_SENSE1,
  output        IO_USB_PULLUP1,
  // GPIO device side
  input [31:0]  cio_gpio_d2p,
  input [31:0]  cio_gpio_en_d2p,
  output [31:0] cio_gpio_p2d,
  // GPIO pads
  inout         IO_GP0,
  inout         IO_GP1,
  inout         IO_GP2,
  inout         IO_GP3,
  inout         IO_GP4,
  inout         IO_GP5,
  inout         IO_GP6,
  inout         IO_GP7,
  inout         IO_GP8,
  inout         IO_GP9,
  inout         IO_GP10,
  inout         IO_GP11,
  inout         IO_GP12,
  inout         IO_GP13,
  inout         IO_GP14,
  inout         IO_GP15,

  // SPI device interface
  output        cio_spi_device_sck_p2d,
  output        cio_spi_device_csb_p2d,
  output        cio_spi_device_mosi_p2d,
  input         cio_spi_device_miso_d2p,
  input         cio_spi_device_miso_en_d2p,
  // JTAG interface
  output        cio_jtag_tck_p2d,
  output        cio_jtag_tms_p2d,
  output        cio_jtag_trst_n_p2d,
  output        cio_jtag_srst_n_p2d,
  output        cio_jtag_tdi_p2d,
  input         cio_jtag_tdo_d2p,
  // FTDI MSEE pins shared between JTAG and SPI
  input         IO_DPS0,
  input         IO_DPS1,
  output        IO_DPS2,
  input         IO_DPS3,
  input         IO_DPS4,
  input         IO_DPS5,
  input         IO_DPS6
);

  // Important that the rx (p2d) line is fixed when transmitting
  // Otherwise you are trying to regenerate the bit clock from
  // the bit clock you are regenerating, rather than just holding the phase
  assign IO_USB_DP0 = cio_usb_dp_en_d2p[0] ? cio_usb_dp_d2p[0] : 1'bz;
  assign cio_usb_dp_p2d[0] = cio_usb_dp_en_d2p[0] ? 1'b1 : IO_USB_DP0;

  assign IO_USB_DN0 = cio_usb_dn_en_d2p[0] ? cio_usb_dn_d2p[0] : 1'bz;
  assign cio_usb_dn_p2d[0] = cio_usb_dn_en_d2p[0] ? 1'b0 : IO_USB_DN0;

  assign IO_USB_PULLUP0 = cio_usb_pullup_en_d2p[0] ? cio_usb_pullup_d2p[0] : 1'bz;
  assign cio_usb_sense_p2d[0] = IO_USB_SENSE0;

  assign IO_USB_DP1 = cio_usb_dp_en_d2p[1] ? cio_usb_dp_d2p[1] : 1'bz;
  assign cio_usb_dp_p2d[1] = cio_usb_dp_en_d2p[1] ? 1'b1 : IO_USB_DP1;

  assign IO_USB_DN1 = cio_usb_dn_en_d2p[1] ? cio_usb_dn_d2p[1] : 1'bz;
  assign cio_usb_dn_p2d[1] = cio_usb_dn_en_d2p[1] ? 1'b0 : IO_USB_DN1;

  assign IO_USB_PULLUP1 = cio_usb_pullup_en_d2p[1] ? cio_usb_pullup_d2p[1] : 1'bz;
  assign cio_usb_sense_p2d[1] = IO_USB_SENSE1;

  // JTAG or SPI mux to the FTDI MSEE pins DPS0-DPS6
  logic    jtag_spi_n, dps2, dps2_en;

  assign  cio_gpio_p2d = {
      15'h0,    // unpopulated
      jtag_spi_n, // Use GPIO16 to pass SPI/JTAG control flag
      IO_GP15,
      IO_GP14,
      IO_GP13,
      IO_GP12,
      IO_GP11,
      IO_GP10,
      IO_GP9,
      IO_GP8,
      IO_GP7,
      IO_GP6,
      IO_GP5,
      IO_GP4,
      IO_GP3,
      IO_GP2,
      IO_GP1,
      IO_GP0
  };

  assign  IO_GP0  = cio_gpio_en_d2p[0]  ? cio_gpio_d2p[0]  : 1'bz;
  assign  IO_GP1  = cio_gpio_en_d2p[1]  ? cio_gpio_d2p[1]  : 1'bz;
  assign  IO_GP2  = cio_gpio_en_d2p[2]  ? cio_gpio_d2p[2]  : 1'bz;
  assign  IO_GP3  = cio_gpio_en_d2p[3]  ? cio_gpio_d2p[3]  : 1'bz;
  assign  IO_GP4  = cio_gpio_en_d2p[4]  ? cio_gpio_d2p[4]  : 1'bz;
  assign  IO_GP5  = cio_gpio_en_d2p[5]  ? cio_gpio_d2p[5]  : 1'bz;
  assign  IO_GP6  = cio_gpio_en_d2p[6]  ? cio_gpio_d2p[6]  : 1'bz;
  assign  IO_GP7  = cio_gpio_en_d2p[7]  ? cio_gpio_d2p[7]  : 1'bz;
  assign  IO_GP8  = cio_gpio_en_d2p[8]  ? cio_gpio_d2p[8]  : 1'bz;
  assign  IO_GP9  = cio_gpio_en_d2p[9]  ? cio_gpio_d2p[9]  : 1'bz;
  assign  IO_GP10 = cio_gpio_en_d2p[10] ? cio_gpio_d2p[10] : 1'bz;
  assign  IO_GP11 = cio_gpio_en_d2p[11] ? cio_gpio_d2p[11] : 1'bz;
  assign  IO_GP12 = cio_gpio_en_d2p[12] ? cio_gpio_d2p[12] : 1'bz;
  assign  IO_GP13 = cio_gpio_en_d2p[13] ? cio_gpio_d2p[13] : 1'bz;
  assign  IO_GP14 = cio_gpio_en_d2p[14] ? cio_gpio_d2p[14] : 1'bz;
  assign  IO_GP15 = cio_gpio_en_d2p[15] ? cio_gpio_d2p[15] : 1'bz;

  assign jtag_spi_n = IO_DPS6;

  assign cio_spi_device_sck_p2d  = jtag_spi_n ?  0         : IO_DPS0;
  assign cio_jtag_tck_p2d        = jtag_spi_n ?  IO_DPS0   : 0;
  assign cio_spi_device_mosi_p2d = jtag_spi_n ?  0         : IO_DPS1;
  assign cio_jtag_tdi_p2d        = jtag_spi_n ?  IO_DPS1   : 0;

  assign dps2    = jtag_spi_n ?    cio_jtag_tdi_p2d : cio_spi_device_miso_d2p;
  assign dps2_en = jtag_spi_n ?    1                : cio_spi_device_miso_en_d2p;
  assign IO_DPS2 = dps2_en ? dps2 : 1'bz;

  assign cio_spi_device_csb_p2d  = jtag_spi_n ?  1         : IO_DPS3;
  assign cio_jtag_tms_p2d        = jtag_spi_n ?  IO_DPS3   : 0;

  assign cio_jtag_trst_n_p2d     = jtag_spi_n ?  IO_DPS4   : 1;
  assign cio_jtag_srst_n_p2d     = jtag_spi_n ?  IO_DPS5   : 1;

endmodule
