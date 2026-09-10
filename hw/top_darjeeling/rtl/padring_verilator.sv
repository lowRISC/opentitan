// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Padring substitute for the Darjeeling Verilator simulation top.
//
// This module models the (otherwise absent) padring for the Verilator
// simulation top. It performs the mapping between the mio/dio pad interface
// of the toplevel and the cio_* interfaces of the IPs that the DPI models in
// the testbench drive and observe.
//
// The cio_*_p2d signals are intentionally left *undriven* inside this module:
// The Verilator testbench (chip_sim_tb) is their sole driver (through hierarchical
// cross-references). Similarly, the cio_*_d2p and other output signals are driven
// here and read back by the testbench in the same way.
//
// Note: Darjeeling has no USB. GPIO is not wired to the MIO pads in this simulation
// top; the GPIO `cio_*` nets are kept for DPI compatibility but are not mapped.

module padring_verilator
  import top_darjeeling_pkg::*;
(
  // Multiplexed I/O (to/from top_darjeeling)
  output logic [pinmux_reg_pkg::NMioPads-1:0] mio_in_o,
  input  logic [pinmux_reg_pkg::NMioPads-1:0] mio_out_i,
  input  logic [pinmux_reg_pkg::NMioPads-1:0] mio_oe_i,
  input  prim_pad_wrapper_pkg::pad_attr_t [pinmux_reg_pkg::NMioPads-1:0] mio_attr_i,

  // Dedicated I/O (to/from top_darjeeling)
  output logic [pinmux_reg_pkg::NDioPads-1:0] dio_in_o,
  input  logic [pinmux_reg_pkg::NDioPads-1:0] dio_out_i,
  input  logic [pinmux_reg_pkg::NDioPads-1:0] dio_oe_i
);

  //////////////////////////////////////////////////////////////////////////
  // Pad-level signals                                                    //
  //////////////////////////////////////////////////////////////////////////

  // GPIO (not mapped to MIO in the Verilator top; kept for DPI compatibility)
  logic [31:0] cio_gpio_p2d;
  logic [31:0] cio_gpio_d2p;
  logic [31:0] cio_gpio_en_d2p;
  logic [31:0] cio_gpio_pull_en;
  logic [31:0] cio_gpio_pull_select;

  // UART (dedicated I/O)
  logic cio_uart_rx_p2d;
  logic cio_uart_tx_d2p;
  logic cio_uart_tx_en_d2p;

  // SPI device (dedicated I/O)
  logic cio_spi_device_sck_p2d;
  logic cio_spi_device_csb_p2d;
  logic cio_spi_device_sdi_p2d;
  logic cio_spi_device_sdo_d2p;
  logic cio_spi_device_sdo_en_d2p;

  //////////////////////////////////////////////////////////////////////////
  // Dedicated I/O mapping                                                //
  //////////////////////////////////////////////////////////////////////////

  always_comb begin : assign_dio_in
    dio_in_o = '0;
    dio_in_o[DioSpiDeviceSck] = cio_spi_device_sck_p2d;
    dio_in_o[DioSpiDeviceCsb] = cio_spi_device_csb_p2d;
    dio_in_o[DioSpiDeviceSd0] = cio_spi_device_sdi_p2d;
    dio_in_o[DioUart0Rx]      = cio_uart_rx_p2d;
  end

  assign cio_spi_device_sdo_d2p    = dio_out_i[DioSpiDeviceSd1];
  assign cio_spi_device_sdo_en_d2p = dio_oe_i[DioSpiDeviceSd1];
  assign cio_uart_tx_d2p           = dio_out_i[DioUart0Tx];
  assign cio_uart_tx_en_d2p        = dio_oe_i[DioUart0Tx];

  //////////////////////////////////////////////////////////////////////////
  // Multiplexed I/O                                                      //
  //                                                                      //
  // No MIO peripherals are wired in the Verilator top, so mio_in is tied //
  // off and the GPIO cio_* nets are left unmapped.                       //
  //////////////////////////////////////////////////////////////////////////

  assign mio_in_o             = '0;
  assign cio_gpio_d2p         = '0;
  assign cio_gpio_en_d2p      = '0;
  assign cio_gpio_pull_en     = '0;
  assign cio_gpio_pull_select = '0;

  // Tie off unused inputs.
  logic unused_sigs;
  assign unused_sigs = ^{mio_out_i, mio_oe_i, mio_attr_i, cio_gpio_p2d};

endmodule
