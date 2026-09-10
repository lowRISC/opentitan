// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Padring substitute for the Verilator simulation top.
//
// This module models the (otherwise absent) padring for the Verilator
// simulation top. It performs the mapping between the mio/dio pad interface
// of the toplevel and the cio_* interfaces of the IPs that the DPI models in
// the testbench drive and observe.

// The cio_*_p2d signals are intentionally left *undriven* inside this module:
// The Verilator testbench (chip_sim_tb) is their sole driver (through hierarchical
// cross-references). Similarly, the cio_*_d2p and other output signals are driven
// here and read back by the testbench in the same way.
//
// This allows to encapsulate the Verilator padring functionality here instead of
// having to expose the whole cio_* signals through ports all the way to the Verilator
// test bench.

module padring_verilator
  import top_earlgrey_pkg::*;
(
  // Multiplexed I/O (to/from top_earlgrey)
  output logic [pinmux_reg_pkg::NMioPads-1:0] mio_in_o,
  input  logic [pinmux_reg_pkg::NMioPads-1:0] mio_out_i,
  input  logic [pinmux_reg_pkg::NMioPads-1:0] mio_oe_i,
  input  prim_pad_wrapper_pkg::pad_attr_t [pinmux_reg_pkg::NMioPads-1:0] mio_attr_i,

  // Dedicated I/O (to/from top_earlgrey)
  output logic [pinmux_reg_pkg::NDioPads-1:0] dio_in_o,
  input  logic [pinmux_reg_pkg::NDioPads-1:0] dio_out_i,
  input  logic [pinmux_reg_pkg::NDioPads-1:0] dio_oe_i,
  input  prim_pad_wrapper_pkg::pad_attr_t [pinmux_reg_pkg::NDioPads-1:0] dio_attr_i,

  // USB signals routed directly to/from top_earlgrey (not via mio/dio)
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
  logic [31:0] cio_gpio_pull_en;
  logic [31:0] cio_gpio_pull_select;

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
  assign cio_usbdev_d_d2p            = usb_tx_d_i;
  assign cio_usbdev_d_en_d2p         = dio_oe_i[DioUsbdevUsbDp];
  assign cio_usbdev_dn_pullup_d2p    = usb_dn_pullup_en_i;
  assign cio_usbdev_dp_pullup_d2p    = usb_dp_pullup_en_i;
  assign cio_usbdev_se0_d2p          = usb_tx_se0_i;
  assign cio_usbdev_rx_enable_d2p    = usb_rx_enable_i;
  assign cio_usbdev_tx_use_d_se0_d2p = usb_tx_use_d_se0_i;

  assign cio_usbdev_dp_d2p    = dio_out_i[DioUsbdevUsbDp];
  assign cio_usbdev_dp_en_d2p = dio_oe_i[DioUsbdevUsbDp];
  assign cio_usbdev_dn_d2p    = dio_out_i[DioUsbdevUsbDn];
  assign cio_usbdev_dn_en_d2p = dio_oe_i[DioUsbdevUsbDn];

  assign cio_spi_device_sdo_d2p    = dio_out_i[DioSpiDeviceSd1];
  assign cio_spi_device_sdo_en_d2p = dio_oe_i[DioSpiDeviceSd1];

  //////////////////////////////////////////////////////////////////////////
  // Multiplexed I/O mapping                                              //
  //////////////////////////////////////////////////////////////////////////

  always_comb begin : assign_mio_in
    mio_in_o = '0;
    // 14 generic GPIOs
    mio_in_o[MioPadIob12:MioPadIob6] = cio_gpio_p2d[6:0];
    mio_in_o[MioPadIor13:MioPadIor5] = cio_gpio_p2d[13:7];
    // SW straps
    mio_in_o[MioPadIoc2:MioPadIoc0] = cio_gpio_p2d[24:22];
    // TAP straps
    mio_in_o[MioPadIoc5] = cio_gpio_p2d[27];
    mio_in_o[MioPadIoc8] = cio_gpio_p2d[30];
    // UART RX
    mio_in_o[MioPadIoc3] = cio_uart_rx_p2d;
    // USB VBUS sense
    mio_in_o[MioPadIoc7] = cio_usbdev_sense_p2d;
  end

  // 14 generic GPIOs
  assign cio_gpio_d2p[6:0]        = mio_out_i[MioPadIob12:MioPadIob6];
  assign cio_gpio_en_d2p[6:0]     = mio_oe_i[MioPadIob12:MioPadIob6];
  assign cio_gpio_d2p[13:7]       = mio_out_i[MioPadIor13:MioPadIor5];
  assign cio_gpio_en_d2p[13:7]    = mio_oe_i[MioPadIor13:MioPadIor5];
  assign cio_gpio_d2p[21:14]      = '0;
  assign cio_gpio_en_d2p[21:14]   = '0;
  // SW straps
  assign cio_gpio_d2p[24:22]      = mio_out_i[MioPadIoc2:MioPadIoc0];
  assign cio_gpio_en_d2p[24:22]   = mio_oe_i[MioPadIoc2:MioPadIoc0];
  assign cio_gpio_d2p[26:25]      = '0;
  assign cio_gpio_en_d2p[26:25]   = '0;
  // TAP straps
  assign cio_gpio_d2p[27]         = mio_out_i[MioPadIoc5];
  assign cio_gpio_en_d2p[27]      = mio_oe_i[MioPadIoc5];
  assign cio_gpio_d2p[29:28]      = '0;
  assign cio_gpio_en_d2p[29:28]   = '0;
  assign cio_gpio_d2p[30]         = mio_out_i[MioPadIoc8];
  assign cio_gpio_en_d2p[30]      = mio_oe_i[MioPadIoc8];
  assign cio_gpio_d2p[31]         = '0;
  assign cio_gpio_en_d2p[31]      = '0;

  assign cio_uart_tx_d2p    = mio_out_i[MioPadIoc4];
  assign cio_uart_tx_en_d2p = mio_oe_i[MioPadIoc4];

  // Note: we're collecting the pull_en and pull_select signals together
  // such that the GPIO DPI functions can simulate weak and strong GPIO
  // inputs. The cio_gpio_pull_en and cio_gpio_pull_select bit vectors
  // must have the same ordering as cio_gpio_d2p.
  // See gpiodpi.c to see how weak/strong inputs work.

  // Pull enable for 14 generic GPIOs
  assign cio_gpio_pull_en[0] = mio_attr_i[MioPadIob6].pull_en;
  assign cio_gpio_pull_en[1] = mio_attr_i[MioPadIob7].pull_en;
  assign cio_gpio_pull_en[2] = mio_attr_i[MioPadIob8].pull_en;
  assign cio_gpio_pull_en[3] = mio_attr_i[MioPadIob9].pull_en;
  assign cio_gpio_pull_en[4] = mio_attr_i[MioPadIob10].pull_en;
  assign cio_gpio_pull_en[5] = mio_attr_i[MioPadIob11].pull_en;
  assign cio_gpio_pull_en[6] = mio_attr_i[MioPadIob12].pull_en;
  assign cio_gpio_pull_en[7] = mio_attr_i[MioPadIor5].pull_en;
  assign cio_gpio_pull_en[8] = mio_attr_i[MioPadIor6].pull_en;
  assign cio_gpio_pull_en[9] = mio_attr_i[MioPadIor7].pull_en;
  assign cio_gpio_pull_en[10] = mio_attr_i[MioPadIor10].pull_en;
  assign cio_gpio_pull_en[11] = mio_attr_i[MioPadIor11].pull_en;
  assign cio_gpio_pull_en[12] = mio_attr_i[MioPadIor12].pull_en;
  assign cio_gpio_pull_en[13] = mio_attr_i[MioPadIor13].pull_en;
  assign cio_gpio_pull_en[21:14] = '0;

  // Pull enable for SW STRAPs
  assign cio_gpio_pull_en[22] = mio_attr_i[MioPadIoc0].pull_en;
  assign cio_gpio_pull_en[23] = mio_attr_i[MioPadIoc1].pull_en;
  assign cio_gpio_pull_en[24] = mio_attr_i[MioPadIoc2].pull_en;

  // Pull enable for TAP STRAPs
  assign cio_gpio_pull_en[26:25] = '0;
  assign cio_gpio_pull_en[27] = mio_attr_i[MioPadIoc5].pull_en;
  assign cio_gpio_pull_en[29:28] = '0;
  assign cio_gpio_pull_en[30] = mio_attr_i[MioPadIoc8].pull_en;
  assign cio_gpio_pull_en[31] = '0;

  // Pull select for 14 generic GPIOs
  assign cio_gpio_pull_select[0] = mio_attr_i[MioPadIob6].pull_select;
  assign cio_gpio_pull_select[1] = mio_attr_i[MioPadIob7].pull_select;
  assign cio_gpio_pull_select[2] = mio_attr_i[MioPadIob8].pull_select;
  assign cio_gpio_pull_select[3] = mio_attr_i[MioPadIob9].pull_select;
  assign cio_gpio_pull_select[4] = mio_attr_i[MioPadIob10].pull_select;
  assign cio_gpio_pull_select[5] = mio_attr_i[MioPadIob11].pull_select;
  assign cio_gpio_pull_select[6] = mio_attr_i[MioPadIob12].pull_select;
  assign cio_gpio_pull_select[7] = mio_attr_i[MioPadIor5].pull_select;
  assign cio_gpio_pull_select[8] = mio_attr_i[MioPadIor6].pull_select;
  assign cio_gpio_pull_select[9] = mio_attr_i[MioPadIor7].pull_select;
  assign cio_gpio_pull_select[10] = mio_attr_i[MioPadIor10].pull_select;
  assign cio_gpio_pull_select[11] = mio_attr_i[MioPadIor11].pull_select;
  assign cio_gpio_pull_select[12] = mio_attr_i[MioPadIor12].pull_select;
  assign cio_gpio_pull_select[13] = mio_attr_i[MioPadIor13].pull_select;
  assign cio_gpio_pull_select[21:14] = '0;

  // Pull select for SW STRAPs
  assign cio_gpio_pull_select[22] = mio_attr_i[MioPadIoc0].pull_select;
  assign cio_gpio_pull_select[23] = mio_attr_i[MioPadIoc1].pull_select;
  assign cio_gpio_pull_select[24] = mio_attr_i[MioPadIoc2].pull_select;

  // Pull select for TAP STRAPs
  assign cio_gpio_pull_select[26:25] = '0;
  assign cio_gpio_pull_select[27] = mio_attr_i[MioPadIoc5].pull_select;
  assign cio_gpio_pull_select[29:28] = '0;
  assign cio_gpio_pull_select[30] = mio_attr_i[MioPadIoc8].pull_select;
  assign cio_gpio_pull_select[31] = '0;

endmodule
