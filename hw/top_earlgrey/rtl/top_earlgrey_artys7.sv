// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module top_earlgrey_artys7 #(
    // Path to a VMEM file containing the contents of the boot ROM, which will be
    // baked into the FPGA bitstream.
    parameter BootRomInitFile = "boot_rom_fpga_artys7.32.vmem"
) (
    // Clock and Reset
    inout IO_CLK,
    inout IO_RST_N,
    // JTAG interface -- not hooked up at the moment
    // inout               IO_DPS0, // IO_JTCK,    IO_SDCK
    // inout               IO_DPS3, // IO_JTMS,    IO_SDCSB
    // inout               IO_DPS1, // IO_JTDI,    IO_SDSDI
    // inout               IO_DPS4, // IO_JTRST_N,
    // inout               IO_DPS5, // IO_JSRST_N,
    // inout               IO_DPS2, // IO_JTDO,    IO_SDO
    // inout               IO_DPS6, // JTAG=1,     SPI=0
    // inout               IO_DPS7, // BOOTSTRAP=1
    // UART interface
    inout IO_URX,
    inout IO_UTX,
    // USB interface
    inout IO_USB_DP0,
    inout IO_USB_DN0,
    inout IO_USB_SENSE0,
    inout IO_USB_DNPULLUP0,
    inout IO_USB_DPPULLUP0,
    // GPIO x 16 interface
    inout IO_GP0,
    inout IO_GP1,
    inout IO_GP2,
    inout IO_GP3,
    inout IO_GP4,
    inout IO_GP5,
    inout IO_GP6,
    inout IO_GP7,
    inout IO_GP8,
    inout IO_GP9,
    inout IO_GP10,
    inout IO_GP11,
    inout IO_GP12,
    inout IO_GP13,
    inout IO_GP14,
    inout IO_GP15
);

  //////////////////////
  // Padring Instance //
  //////////////////////

  logic clk, clk_usb_48mhz, rst_n;
  logic [padctrl_reg_pkg::NMioPads-1:0][padctrl_reg_pkg::AttrDw-1:0] mio_attr;
  logic [padctrl_reg_pkg::NDioPads-1:0][padctrl_reg_pkg::AttrDw-1:0] dio_attr;
  logic [padctrl_reg_pkg::NMioPads-1:0] mio_out_core, mio_out_padring;
  logic [padctrl_reg_pkg::NMioPads-1:0] mio_oe_core, mio_oe_padring;
  logic [padctrl_reg_pkg::NMioPads-1:0] mio_in_core, mio_in_padring;
  logic [padctrl_reg_pkg::NDioPads-1:0] dio_out_core, dio_out_padring;
  logic [padctrl_reg_pkg::NDioPads-1:0] dio_oe_core, dio_oe_padring;
  logic [padctrl_reg_pkg::NDioPads-1:0] dio_in_core, dio_in_padring;

  padring #(
      // MIOs 31:20 are currently not
      // connected to pads and hence tied off
      .ConnectMioIn(32'h0000FFFF),
      .ConnectMioOut(32'h0000FFFF),
      // Tied off DIOs:
      // 2: usbdev_d
      // 3: usbdev_suspend
      // 4: usbdev_tx_mode
      // 7: usbdev_se
      // 11-14: SPI / JTAG
      .ConnectDioIn(15'h0763),
      .ConnectDioOut(15'h0763)
  ) padring (
      // Clk / Rst
      .clk_pad_i(1'b0),
      .clk_usb_48mhz_pad_i(1'b0),
      .rst_pad_ni(1'b0),
      .clk_o(),
      .clk_usb_48mhz_o(),
      .rst_no(),
      // MIO Pads
      .mio_pad_io({
        16'bz,  // Note that 31:16 are currently not mapped
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
      }),
      // DIO Pads
      .dio_pad_io({
        4'bz,
        IO_URX,
        IO_UTX,
        IO_USB_SENSE0,
        1'bz,  // usbdev_se0
        IO_USB_DPPULLUP0,
        IO_USB_DNPULLUP0,
        1'bz,  // usbdev_tx_mode
        1'bz,  // usbdev_suspend
        1'bz,  // usbdev_d
        IO_USB_DP0,
        IO_USB_DN0
      }),
      // Muxed IOs
      .mio_in_o(mio_in_padring),
      .mio_out_i(mio_out_padring),
      .mio_oe_i(mio_oe_padring),
      // Dedicated IOs
      .dio_in_o(dio_in_padring),
      .dio_out_i(dio_out_padring),
      .dio_oe_i(dio_oe_padring),
      // Pad Attributes
      .mio_attr_i(mio_attr),
      .dio_attr_i(dio_attr)
  );

  //////////////////////
  // JTAG Overlay Mux //
  //////////////////////

  // Unlike nexysvideo, there is currently no dedicated
  // JTAG port available, hence tie off.
  logic jtag_trst_n, jtag_srst_n;
  logic jtag_tck, jtag_tms, jtag_tdi, jtag_tdo;

  assign jtag_trst_n = 1'b1;
  assign jtag_srst_n = 1'b1;
  assign jtag_tck = 1'b0;
  assign jtag_tms = 1'b0;
  assign jtag_tdi = 1'b0;

  assign mio_in_core = mio_in_padring;
  assign mio_out_padring = mio_out_core;
  assign mio_oe_padring = mio_oe_core;
  assign dio_in_core = dio_in_padring;
  assign dio_out_padring = dio_out_core;
  assign dio_oe_padring = dio_oe_core;

  //////////////////
  // PLL for FPGA //
  //////////////////

  clkgen_xil7series clkgen (
      .IO_CLK,
      .IO_RST_N,
      .clk_sys  (clk),
      .clk_48MHz(clk_usb_48mhz),
      .rst_sys_n(rst_n)
  );

  //////////////////////
  // Top-level design //
  //////////////////////

  top_earlgrey #(
      .IbexPipeLine(1),
      .BootRomInitFile(BootRomInitFile)
  ) top_earlgrey (
      // Clocks, resets
      .clk_i          (clk),
      .rst_ni         (rst_n),
      .clk_fixed_i    (clk),
      .clk_usb_48mhz_i(clk_usb_48mhz),

      // JTAG
      .jtag_tck_i  (jtag_tck),
      .jtag_tms_i  (jtag_tms),
      .jtag_trst_ni(jtag_trst_n),
      .jtag_tdi_i  (jtag_tdi),
      .jtag_tdo_o  (jtag_tdo),

      // Multiplexed I/O
      .mio_in_i (mio_in_core),
      .mio_out_o(mio_out_core),
      .mio_oe_o (mio_oe_core),

      // Dedicated I/O
      .dio_in_i (dio_in_core),
      .dio_out_o(dio_out_core),
      .dio_oe_o (dio_oe_core),

      // Pad attributes
      .mio_attr_o(mio_attr),
      .dio_attr_o(dio_attr),

      // DFT signals
      .scanmode_i(1'b0)
  );

endmodule : top_earlgrey_artys7
