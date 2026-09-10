// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Padring substitute for the English Breakfast Verilator simulation top.
//
// This module models the (otherwise absent) padring for the Verilator
// simulation top. It performs the mapping between the mio/dio pad interface
// of the toplevel and the cio_* interfaces of the IPs that the DPI models in
// the testbench drive and observe.

// The cio_*_p2d signals are intentionally left *undriven* inside this module:
// The Verilator testbench (chip_sim_tb) is their sole driver (through hierarchical
// cross-references). Similarly, the cio_*_d2p and other output signals are driven
// here and read back by the testbench in the same way.

// This allows to encapsulate the Verilator padring functionality here instead of
// having to expose the who

module padring_verilator
  import top_englishbreakfast_pkg::*;
(
  // Multiplexed I/O (to/from top_englishbreakfast)
  output logic [pinmux_reg_pkg::NMioPads-1:0] mio_in_o,
  input  logic [pinmux_reg_pkg::NMioPads-1:0] mio_out_i,
  input  logic [pinmux_reg_pkg::NMioPads-1:0] mio_oe_i,
  input  prim_pad_wrapper_pkg::pad_attr_t [pinmux_reg_pkg::NMioPads-1:0] mio_attr_i,

  // Dedicated I/O (to/from top_englishbreakfast)
  output logic [pinmux_reg_pkg::NDioPads-1:0] dio_in_o,
  input  logic [pinmux_reg_pkg::NDioPads-1:0] dio_out_i,
  input  logic [pinmux_reg_pkg::NDioPads-1:0] dio_oe_i,
  input  prim_pad_wrapper_pkg::pad_attr_t [pinmux_reg_pkg::NDioPads-1:0] dio_attr_i,

  // USB signals routed directly to/from top_englishbreakfast (not via mio/dio)
  output logic usb_rx_d_o,
  input  logic usb_tx_d_i,
  input  logic usb_tx_se0_i,
  input  logic usb_tx_use_d_se0_i,
  input  logic usb_rx_enable_i,
  input  logic usb_dp_pullup_en_i,
  input  logic usb_dn_pullup_en_i
);

  //////////////////////////////////////////////////////////////////////////
  // Pad-level signals                                                    //
  //////////////////////////////////////////////////////////////////////////

  // GPIO
  logic [31:0] cio_gpio_p2d;
  logic [31:0] cio_gpio_d2p;
  logic [31:0] cio_gpio_en_d2p;

  // UART
  logic cio_uart_rx_p2d;
  logic cio_uart_tx_d2p;
  logic cio_uart_tx_en_d2p;

  // SPI device
  logic cio_spi_device_sck_p2d;
  logic cio_spi_device_csb_p2d;
  logic cio_spi_device_sdi_p2d;
  logic cio_spi_device_sdo_d2p;
  logic cio_spi_device_sdo_en_d2p;

  // USB
  logic cio_usbdev_sense_p2d;
  logic cio_usbdev_dp_pullup_d2p;
  logic cio_usbdev_dn_pullup_d2p;
  logic cio_usbdev_dp_p2d, cio_usbdev_dp_d2p, cio_usbdev_dp_en_d2p;
  logic cio_usbdev_dn_p2d, cio_usbdev_dn_d2p, cio_usbdev_dn_en_d2p;
  logic cio_usbdev_d_p2d,  cio_usbdev_d_d2p,  cio_usbdev_d_en_d2p;
  logic cio_usbdev_se0_d2p;
  logic cio_usbdev_rx_enable_d2p;
  logic cio_usbdev_tx_use_d_se0_d2p;

  //////////////////////////////////////////////////////////////////////////
  // Dedicated I/O mapping                                                //
  //////////////////////////////////////////////////////////////////////////

  always_comb begin : assign_dio_in
    dio_in_o = '0;
    dio_in_o[DioSpiDeviceSck] = cio_spi_device_sck_p2d;
    dio_in_o[DioSpiDeviceCsb] = cio_spi_device_csb_p2d;
    dio_in_o[DioSpiDeviceSd0] = cio_spi_device_sdi_p2d;
    dio_in_o[DioUsbdevUsbDp]  = cio_usbdev_dp_p2d;
    dio_in_o[DioUsbdevUsbDn]  = cio_usbdev_dn_p2d;
  end

  // USB
  assign usb_rx_d_o                  = cio_usbdev_d_p2d;
  assign cio_usbdev_dn_d2p           = dio_out_i[DioUsbdevUsbDn];
  assign cio_usbdev_dp_d2p           = dio_out_i[DioUsbdevUsbDp];
  assign cio_usbdev_d_d2p            = usb_tx_d_i;
  assign cio_usbdev_rx_enable_d2p    = usb_rx_enable_i;
  assign cio_usbdev_tx_use_d_se0_d2p = usb_tx_use_d_se0_i;
  assign cio_usbdev_dn_pullup_d2p    = usb_dn_pullup_en_i;
  assign cio_usbdev_dp_pullup_d2p    = usb_dp_pullup_en_i;
  assign cio_usbdev_se0_d2p          = usb_tx_se0_i;
  assign cio_spi_device_sdo_d2p      = dio_out_i[DioSpiDeviceSd1];

  assign cio_usbdev_dn_en_d2p        = dio_oe_i[DioUsbdevUsbDn];
  assign cio_usbdev_dp_en_d2p        = dio_oe_i[DioUsbdevUsbDp];
  assign cio_usbdev_d_en_d2p         = dio_oe_i[DioUsbdevUsbDp];
  assign cio_spi_device_sdo_en_d2p   = dio_oe_i[DioSpiDeviceSd1];

  //////////////////////////////////////////////////////////////////////////
  // Multiplexed I/O mapping                                              //
  //////////////////////////////////////////////////////////////////////////

  always_comb begin : assign_mio_in
    mio_in_o = '0;
    mio_in_o[31:0] = cio_gpio_p2d;
    mio_in_o[25] = cio_uart_rx_p2d;
    mio_in_o[35] = cio_usbdev_sense_p2d;
    mio_in_o[36] = cio_usbdev_sense_p2d;
  end

  assign cio_gpio_d2p[31:27]    = mio_out_i[31:27];
  assign cio_gpio_en_d2p[31:27] = mio_oe_i[31:27];

  // GPIO bit 26 is overlaid with the UART Tx output.
  assign cio_gpio_d2p[26]       = '0;
  assign cio_gpio_en_d2p[26]    = '0;
  assign cio_uart_tx_d2p        = mio_out_i[26];
  assign cio_uart_tx_en_d2p     = mio_oe_i[26];

  assign cio_gpio_d2p[25:0]     = mio_out_i[25:0];
  assign cio_gpio_en_d2p[25:0]  = mio_oe_i[25:0];

  // Pad attributes are not modelled in the Verilator padring.
  logic unused_mio_attr;
  assign unused_mio_attr = ^{mio_attr_i};

endmodule : padring_verilator
