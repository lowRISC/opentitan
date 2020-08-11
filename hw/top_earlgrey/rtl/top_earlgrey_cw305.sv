// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module top_earlgrey_cw305 #(
    // Path to a VMEM file containing the contents of the boot ROM, which will be
    // baked into the FPGA bitstream.
    parameter BootRomInitFile = "boot_rom_fpga_nexysvideo.32.vmem"
) (
    // Clock and Reset
    inout  IO_CLK,
    inout  IO_RST_N,
    // JTAG interface
    inout  IO_DPS0,  // IO_JTCK,    IO_SDCK
    inout  IO_DPS3,  // IO_JTMS,    IO_SDCSB
    inout  IO_DPS1,  // IO_JTDI,    IO_SDSDI
    inout  IO_DPS4,  // IO_JTRST_N,
    inout  IO_DPS5,  // IO_JSRST_N,
    inout  IO_DPS2,  // IO_JTDO,    IO_SDO
    inout  IO_DPS6,  // JTAG=1,     SPI=0
    inout  IO_DPS7,  // BOOTSTRAP=1
    // UART interface
    inout  IO_URX,
    inout  IO_UTX,
    // USB interface
    inout  IO_USB_DP0,
    inout  IO_USB_DN0,
    inout  IO_USB_SENSE0,
    inout  IO_USB_DNPULLUP0,
    inout  IO_USB_DPPULLUP0,
    // GPIO x 16 interface
    inout  IO_GP0,
    inout  IO_GP1,
    inout  IO_GP2,
    inout  IO_GP3,
    inout  IO_GP4,
    inout  IO_GP5,
    inout  IO_GP6,
    inout  IO_GP7,
    output IO_GP8,  // XXX: rename as LED
    output IO_GP9,  // XXX: rename as LED
    output IO_GP10,  // XXX: rename as LED
    inout  IO_GP11,
    inout  IO_GP12,
    inout  IO_GP13,
    inout  IO_GP14,
    inout  IO_GP15,
    // chipwhisperer IO
    output TIO_CLKOUT
);

  import top_earlgrey_pkg::*;

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

  reg io_utx_reg;
  always @(posedge clk) begin
    io_utx_reg <<= (IO_UTX == 1'bz) ? 0 : IO_UTX;
  end
  assign IO_GP8 = io_utx_reg;

  reg io_urx_reg;
  always @(posedge clk) begin
    io_urx_reg <<= (IO_URX == 1'bz) ? 0 : IO_URX;
  end
  assign IO_GP9 = io_urx_reg;

  assign IO_GP10 = 1'b1;

  assign TIO_CLKOUT = clk;

  padring #(
      // MIOs 31:20 are currently not
      // connected to pads and hence tied off
      .ConnectMioIn(32'h000FF8FF),
      .ConnectMioOut(32'h000FF8FF),
      // Tied off DIOs:
      // 2: usbdev_d
      // 3: usbdev_suspend
      // 4: usbdev_tx_mode
      // 7: usbdev_se
      .ConnectDioIn(15'h7F63),
      .ConnectDioOut(15'h7F63)
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
        12'bz,  // Note that 31:20 are currently not mapped
        IO_DPS5,  // Use GPIO19 to pass JTAG_SRST
        IO_DPS4,  // Use GPIO18 to pass JTAG_TRST
        IO_DPS7,  // Use GPIO17 to pass rom boot_strap indication
        IO_DPS6,  // Use GPIO16 to pass SPI/JTAG control flag
        IO_GP15,
        IO_GP14,
        IO_GP13,
        IO_GP12,
        IO_GP11,
        1'bz,
        1'bz,
        1'bz,
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
        IO_DPS0,  // SCK, JTAG_TCK
        IO_DPS3,  // CSB, JTAG_TMS
        IO_DPS1,  // SDI, JTAG_TDI
        IO_DPS2,  // SDO, JTAG_TDO
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

  logic jtag_trst_n, jtag_srst_n;
  logic jtag_tck, jtag_tms, jtag_tdi, jtag_tdo;

  localparam int NumIOs = padctrl_reg_pkg::NMioPads + padctrl_reg_pkg::NDioPads;

  // This specifies the tie-off values of the muxed MIO/DIOs
  // when the JTAG is active. SPI CSB is active low.
  localparam logic [NumIOs-1:0] TieOffValues = NumIOs
      '(1'b1 << (padctrl_reg_pkg::NMioPads + top_earlgrey_pkg::TopEarlgreyDioPinSpiDeviceCsb));

  // TODO: this is a temporary solution. JTAG will eventually be selected and
  // qualified inside the pinmux, based on strap and lifecycle state.
  // Parameterizeable JTAG overlay mux.
  // Unaffected indices are just passed through.
  jtag_mux #(
      .NumIOs(NumIOs),
      .TieOffValues(TieOffValues),
      .JtagEnIdx(16),  // MIO 16
      .JtagEnPolarity(1),
      .TckIdx(padctrl_reg_pkg::NMioPads + top_earlgrey_pkg::TopEarlgreyDioPinSpiDeviceSck),
      .TmsIdx(padctrl_reg_pkg::NMioPads + top_earlgrey_pkg::TopEarlgreyDioPinSpiDeviceCsb),
      .TrstIdx(18),  // MIO 18
      .SrstIdx(19),  // MIO 19
      .TdiIdx(padctrl_reg_pkg::NMioPads + top_earlgrey_pkg::TopEarlgreyDioPinSpiDeviceSdi),
      .TdoIdx(padctrl_reg_pkg::NMioPads + top_earlgrey_pkg::TopEarlgreyDioPinSpiDeviceSdo)
  ) jtag_mux (
      // To JTAG inside core
      .jtag_tck_o   (jtag_tck),
      .jtag_tms_o   (jtag_tms),
      .jtag_trst_no (jtag_trst_n),
      .jtag_srst_no (jtag_srst_n),
      .jtag_tdi_o   (jtag_tdi),
      .jtag_tdo_i   (jtag_tdo),
      // To core side
      .out_core_i   ({dio_out_core, mio_out_core}),
      .oe_core_i    ({dio_oe_core, mio_oe_core}),
      .in_core_o    ({dio_in_core, mio_in_core}),
      // To padring side
      .out_padring_o({dio_out_padring, mio_out_padring}),
      .oe_padring_o ({dio_oe_padring, mio_oe_padring}),
      .in_padring_i ({dio_in_padring, mio_in_padring})
  );

  //////////////////
  // PLL for FPGA //
  //////////////////

  clkgen_xil7series #(
      .AddClkBuf(0)
  ) clkgen (
      .IO_CLK,
      .IO_RST_N (IO_RST_N & jtag_srst_n),
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
      .rst_ni         (rst_n),
      .clkmgr_clk_main(clk),
      .clkmgr_clk_io  (clk),
      .clkmgr_clk_usb (clk_usb_48mhz),
      .clkmgr_clk_aon (clk),

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

endmodule : top_earlgrey_cw305
