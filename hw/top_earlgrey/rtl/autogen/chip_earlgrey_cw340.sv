// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_earlgrey/data/top_earlgrey.hjson
//                -o hw/top_earlgrey/


`include "bkdr_loader.svh"

module chip_earlgrey_cw340 #(
  parameter bit BkdrLoaderEn = 1'b1,
  // Path to a VMEM file containing the contents of the boot ROM, which will be
  // baked into the FPGA bitstream.
  parameter BootRomInitFile = "test_rom_fpga_cw340.32.vmem"
) (
  // Dedicated Pads
  inout POR_N, // Manual Pad
  inout SPI_HOST_D0, // Dedicated Pad for spi_host0_sd
  inout SPI_HOST_D1, // Dedicated Pad for spi_host0_sd
  inout SPI_HOST_D2, // Dedicated Pad for spi_host0_sd
  inout SPI_HOST_D3, // Dedicated Pad for spi_host0_sd
  inout SPI_HOST_CLK, // Dedicated Pad for spi_host0_sck
  inout SPI_HOST_CS_L, // Dedicated Pad for spi_host0_csb
  inout SPI_DEV_D0, // Dedicated Pad for spi_device_sd
  inout SPI_DEV_D1, // Dedicated Pad for spi_device_sd
  inout SPI_DEV_D2, // Dedicated Pad for spi_device_sd
  inout SPI_DEV_D3, // Dedicated Pad for spi_device_sd
  inout SPI_DEV_CLK, // Dedicated Pad for spi_device_sck
  inout SPI_DEV_CS_L, // Dedicated Pad for spi_device_csb
  inout IOR8, // Dedicated Pad for sysrst_ctrl_ec_rst_l
  inout IOR9, // Dedicated Pad for sysrst_ctrl_flash_wp_l
  inout IO_CLK, // Manual Pad
  inout IO_USB_CONNECT, // Manual Pad
  inout IO_USB_DP_TX, // Manual Pad
  inout IO_USB_DN_TX, // Manual Pad
  inout IO_USB_D_RX, // Manual Pad
  inout IO_USB_DP_RX, // Manual Pad
  inout IO_USB_DN_RX, // Manual Pad
  inout IO_USB_OE_N, // Manual Pad
  inout IO_USB_SPEED, // Manual Pad
  inout IO_USB_SUSPEND, // Manual Pad
  inout IO_CLKOUT, // Manual Pad
  inout IO_TRIGGER, // Manual Pad

  // Muxed Pads
  inout IOA0, // MIO Pad 0
  inout IOA1, // MIO Pad 1
  `INOUT_AO IOA2, // MIO Pad 2
  `INOUT_AO IOA3, // MIO Pad 3
  inout IOA4, // MIO Pad 4
  inout IOA5, // MIO Pad 5
  inout IOA6, // MIO Pad 6
  inout IOA7, // MIO Pad 7
  inout IOA8, // MIO Pad 8
  inout IOB0, // MIO Pad 9
  inout IOB1, // MIO Pad 10
  inout IOB2, // MIO Pad 11
  inout IOB3, // MIO Pad 12
  inout IOB4, // MIO Pad 13
  inout IOB5, // MIO Pad 14
  inout IOB6, // MIO Pad 15
  inout IOB7, // MIO Pad 16
  inout IOB8, // MIO Pad 17
  inout IOB9, // MIO Pad 18
  inout IOB10, // MIO Pad 19
  inout IOB11, // MIO Pad 20
  inout IOB12, // MIO Pad 21
  inout IOC0, // MIO Pad 22
  inout IOC1, // MIO Pad 23
  inout IOC2, // MIO Pad 24
  inout IOC3, // MIO Pad 25
  inout IOC4, // MIO Pad 26
  inout IOC5, // MIO Pad 27
  inout IOC6, // MIO Pad 28
  inout IOC7, // MIO Pad 29
  inout IOC8, // MIO Pad 30
  inout IOC9, // MIO Pad 31
  inout IOC10, // MIO Pad 32
  inout IOC11, // MIO Pad 33
  inout IOC12, // MIO Pad 34
  inout IOR0, // MIO Pad 35
  inout IOR1, // MIO Pad 36
  inout IOR2, // MIO Pad 37
  inout IOR3, // MIO Pad 38
  inout IOR4, // MIO Pad 39
  inout IOR5, // MIO Pad 40
  inout IOR6, // MIO Pad 41
  inout IOR7, // MIO Pad 42
  inout IOR10, // MIO Pad 43
  inout IOR11, // MIO Pad 44
  inout IOR12, // MIO Pad 45
  inout IOR13  // MIO Pad 46
);

  import top_earlgrey_pkg::*;
  import prim_pad_wrapper_pkg::*;

  ////////////////////////////
  // Special Signal Indices //
  ////////////////////////////

  localparam int Tap0PadIdx = 30;
  localparam int Tap1PadIdx = 27;
  localparam int Dft0PadIdx = 40;
  localparam int Dft1PadIdx = 42;
  localparam int TckPadIdx = 38;
  localparam int TmsPadIdx = 35;
  localparam int TrstNPadIdx = 39;
  localparam int TdiPadIdx = 37;
  localparam int TdoPadIdx = 36;

  // DFT and Debug signal positions in the pinout.
  localparam pinmux_pkg::target_cfg_t PinmuxTargetCfg = '{
    tck_idx:           TckPadIdx,
    tms_idx:           TmsPadIdx,
    trst_idx:          TrstNPadIdx,
    tdi_idx:           TdiPadIdx,
    tdo_idx:           TdoPadIdx,
    tap_strap0_idx:    Tap0PadIdx,
    tap_strap1_idx:    Tap1PadIdx,
    dft_strap0_idx:    Dft0PadIdx,
    dft_strap1_idx:    Dft1PadIdx,
    // TODO: check whether there is a better way to pass these USB-specific params
    usb_dp_idx:        DioUsbdevUsbDp,
    usb_dn_idx:        DioUsbdevUsbDn,
    usb_sense_idx:     MioInUsbdevSense,
    // Pad types for attribute WARL behavior
    dio_pad_type: {
      BidirStd, // DIO spi_host0_csb
      BidirStd, // DIO spi_host0_sck
      InputStd, // DIO spi_device_csb
      InputStd, // DIO spi_device_sck
      BidirOd, // DIO sysrst_ctrl_flash_wp_l
      BidirOd, // DIO sysrst_ctrl_ec_rst_l
      BidirStd, // DIO spi_device_sd
      BidirStd, // DIO spi_device_sd
      BidirStd, // DIO spi_device_sd
      BidirStd, // DIO spi_device_sd
      BidirStd, // DIO spi_host0_sd
      BidirStd, // DIO spi_host0_sd
      BidirStd, // DIO spi_host0_sd
      BidirStd, // DIO spi_host0_sd
      BidirStd, // DIO usbdev_usb_dn
      BidirStd  // DIO usbdev_usb_dp
    },
    mio_pad_type: {
      BidirOd, // MIO Pad 46
      BidirOd, // MIO Pad 45
      BidirOd, // MIO Pad 44
      BidirOd, // MIO Pad 43
      BidirStd, // MIO Pad 42
      BidirStd, // MIO Pad 41
      BidirStd, // MIO Pad 40
      BidirStd, // MIO Pad 39
      BidirStd, // MIO Pad 38
      BidirStd, // MIO Pad 37
      BidirStd, // MIO Pad 36
      BidirStd, // MIO Pad 35
      BidirOd, // MIO Pad 34
      BidirOd, // MIO Pad 33
      BidirOd, // MIO Pad 32
      BidirStd, // MIO Pad 31
      BidirStd, // MIO Pad 30
      BidirStd, // MIO Pad 29
      BidirStd, // MIO Pad 28
      BidirStd, // MIO Pad 27
      BidirStd, // MIO Pad 26
      BidirStd, // MIO Pad 25
      BidirStd, // MIO Pad 24
      BidirStd, // MIO Pad 23
      BidirStd, // MIO Pad 22
      BidirOd, // MIO Pad 21
      BidirOd, // MIO Pad 20
      BidirOd, // MIO Pad 19
      BidirOd, // MIO Pad 18
      BidirStd, // MIO Pad 17
      BidirStd, // MIO Pad 16
      BidirStd, // MIO Pad 15
      BidirStd, // MIO Pad 14
      BidirStd, // MIO Pad 13
      BidirStd, // MIO Pad 12
      BidirStd, // MIO Pad 11
      BidirStd, // MIO Pad 10
      BidirStd, // MIO Pad 9
      BidirOd, // MIO Pad 8
      BidirOd, // MIO Pad 7
      BidirOd, // MIO Pad 6
      BidirStd, // MIO Pad 5
      BidirStd, // MIO Pad 4
      BidirStd, // MIO Pad 3
      BidirStd, // MIO Pad 2
      BidirStd, // MIO Pad 1
      BidirStd  // MIO Pad 0
    },
    // Pad scan roles
    dio_scan_role: {
      scan_role_pkg::DioPadSpiHostCsLScanRole, // DIO spi_host0_csb
      scan_role_pkg::DioPadSpiHostClkScanRole, // DIO spi_host0_sck
      scan_role_pkg::DioPadSpiDevCsLScanRole, // DIO spi_device_csb
      scan_role_pkg::DioPadSpiDevClkScanRole, // DIO spi_device_sck
      scan_role_pkg::DioPadIor9ScanRole, // DIO sysrst_ctrl_flash_wp_l
      scan_role_pkg::DioPadIor8ScanRole, // DIO sysrst_ctrl_ec_rst_l
      scan_role_pkg::DioPadSpiDevD3ScanRole, // DIO spi_device_sd
      scan_role_pkg::DioPadSpiDevD2ScanRole, // DIO spi_device_sd
      scan_role_pkg::DioPadSpiDevD1ScanRole, // DIO spi_device_sd
      scan_role_pkg::DioPadSpiDevD0ScanRole, // DIO spi_device_sd
      scan_role_pkg::DioPadSpiHostD3ScanRole, // DIO spi_host0_sd
      scan_role_pkg::DioPadSpiHostD2ScanRole, // DIO spi_host0_sd
      scan_role_pkg::DioPadSpiHostD1ScanRole, // DIO spi_host0_sd
      scan_role_pkg::DioPadSpiHostD0ScanRole, // DIO spi_host0_sd
      NoScan, // DIO usbdev_usb_dn
      NoScan // DIO usbdev_usb_dp
    },
    mio_scan_role: {
      scan_role_pkg::MioPadIor13ScanRole,
      scan_role_pkg::MioPadIor12ScanRole,
      scan_role_pkg::MioPadIor11ScanRole,
      scan_role_pkg::MioPadIor10ScanRole,
      scan_role_pkg::MioPadIor7ScanRole,
      scan_role_pkg::MioPadIor6ScanRole,
      scan_role_pkg::MioPadIor5ScanRole,
      scan_role_pkg::MioPadIor4ScanRole,
      scan_role_pkg::MioPadIor3ScanRole,
      scan_role_pkg::MioPadIor2ScanRole,
      scan_role_pkg::MioPadIor1ScanRole,
      scan_role_pkg::MioPadIor0ScanRole,
      scan_role_pkg::MioPadIoc12ScanRole,
      scan_role_pkg::MioPadIoc11ScanRole,
      scan_role_pkg::MioPadIoc10ScanRole,
      scan_role_pkg::MioPadIoc9ScanRole,
      scan_role_pkg::MioPadIoc8ScanRole,
      scan_role_pkg::MioPadIoc7ScanRole,
      scan_role_pkg::MioPadIoc6ScanRole,
      scan_role_pkg::MioPadIoc5ScanRole,
      scan_role_pkg::MioPadIoc4ScanRole,
      scan_role_pkg::MioPadIoc3ScanRole,
      scan_role_pkg::MioPadIoc2ScanRole,
      scan_role_pkg::MioPadIoc1ScanRole,
      scan_role_pkg::MioPadIoc0ScanRole,
      scan_role_pkg::MioPadIob12ScanRole,
      scan_role_pkg::MioPadIob11ScanRole,
      scan_role_pkg::MioPadIob10ScanRole,
      scan_role_pkg::MioPadIob9ScanRole,
      scan_role_pkg::MioPadIob8ScanRole,
      scan_role_pkg::MioPadIob7ScanRole,
      scan_role_pkg::MioPadIob6ScanRole,
      scan_role_pkg::MioPadIob5ScanRole,
      scan_role_pkg::MioPadIob4ScanRole,
      scan_role_pkg::MioPadIob3ScanRole,
      scan_role_pkg::MioPadIob2ScanRole,
      scan_role_pkg::MioPadIob1ScanRole,
      scan_role_pkg::MioPadIob0ScanRole,
      scan_role_pkg::MioPadIoa8ScanRole,
      scan_role_pkg::MioPadIoa7ScanRole,
      scan_role_pkg::MioPadIoa6ScanRole,
      scan_role_pkg::MioPadIoa5ScanRole,
      scan_role_pkg::MioPadIoa4ScanRole,
      scan_role_pkg::MioPadIoa3ScanRole,
      scan_role_pkg::MioPadIoa2ScanRole,
      scan_role_pkg::MioPadIoa1ScanRole,
      scan_role_pkg::MioPadIoa0ScanRole
    }
  };

  ////////////////////////
  // Signal definitions //
  ////////////////////////


  pad_attr_t [pinmux_reg_pkg::NMioPads-1:0] mio_attr;
  pad_attr_t [pinmux_reg_pkg::NDioPads-1:0] dio_attr;

  logic [pinmux_reg_pkg::NMioPads-1:0] mio_out;
  logic [pinmux_reg_pkg::NMioPads-1:0] mio_oe;
  logic [pinmux_reg_pkg::NMioPads-1:0] mio_in;
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_out;
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_oe;
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_in;

  logic                          [3:0] mux_iob_sel;
  logic [pinmux_reg_pkg::NMioPads-1:0] mio_in_raw;
  logic                         [26:0] dio_in_raw;

  logic unused_mio_in_raw;
  logic unused_dio_in_raw;
  assign unused_mio_in_raw = ^mio_in_raw;
  assign unused_dio_in_raw = ^dio_in_raw;

  // Manual pads
  logic manual_in_por_n, manual_out_por_n, manual_oe_por_n;
  logic manual_in_io_clk, manual_out_io_clk, manual_oe_io_clk;
  logic manual_in_io_usb_connect, manual_out_io_usb_connect, manual_oe_io_usb_connect;
  logic manual_in_io_usb_dp_tx, manual_out_io_usb_dp_tx, manual_oe_io_usb_dp_tx;
  logic manual_in_io_usb_dn_tx, manual_out_io_usb_dn_tx, manual_oe_io_usb_dn_tx;
  logic manual_in_io_usb_d_rx, manual_out_io_usb_d_rx, manual_oe_io_usb_d_rx;
  logic manual_in_io_usb_dp_rx, manual_out_io_usb_dp_rx, manual_oe_io_usb_dp_rx;
  logic manual_in_io_usb_dn_rx, manual_out_io_usb_dn_rx, manual_oe_io_usb_dn_rx;
  logic manual_in_io_usb_oe_n, manual_out_io_usb_oe_n, manual_oe_io_usb_oe_n;
  logic manual_in_io_usb_speed, manual_out_io_usb_speed, manual_oe_io_usb_speed;
  logic manual_in_io_usb_suspend, manual_out_io_usb_suspend, manual_oe_io_usb_suspend;
  logic manual_in_io_clkout, manual_out_io_clkout, manual_oe_io_clkout;
  logic manual_in_io_trigger, manual_out_io_trigger, manual_oe_io_trigger;

  pad_attr_t manual_attr_por_n;
  pad_attr_t manual_attr_io_clk;
  pad_attr_t manual_attr_io_usb_connect;
  pad_attr_t manual_attr_io_usb_dp_tx;
  pad_attr_t manual_attr_io_usb_dn_tx;
  pad_attr_t manual_attr_io_usb_d_rx;
  pad_attr_t manual_attr_io_usb_dp_rx;
  pad_attr_t manual_attr_io_usb_dn_rx;
  pad_attr_t manual_attr_io_usb_oe_n;
  pad_attr_t manual_attr_io_usb_speed;
  pad_attr_t manual_attr_io_usb_suspend;
  pad_attr_t manual_attr_io_clkout;
  pad_attr_t manual_attr_io_trigger;

  // Power state from AST to USB
  ast_pkg::ast_pwst_t ast_pwst_h;

  // AST ADC analog inputs and direct analog pad-short outputs.
  ast_pkg::awire_t ast_adc_a0_a, ast_adc_a1_a;
  ast_pkg::awire_t ast2pad_t0_a, ast2pad_t1_a;
  // Tie-off ADC inputs. Leave the direct pad-short outputs unused.
  assign ast_adc_a0_a = '0;
  assign ast_adc_a1_a = '0;
  logic unused_ast_analog;
  assign unused_ast_analog = ^{ast2pad_t0_a, ast2pad_t1_a};

  /////////////////////////
  // Stubbed pad tie-off //
  /////////////////////////

  // Only signals going to non-custom pads need to be tied off.
  logic [66:0] unused_sig;
  //////////////////////
  // Padring Instance //
  //////////////////////

  // AST signals needed in padring - must be decleared here
  logic padring_scan_clk;
  prim_mubi_pkg::mubi4_t scanmode;

  padring #(
    // Padring specific counts may differ from pinmux config due
    // to custom, stubbed or added pads.
    .NDioPads(27),
    .NMioPads(47),
    .DioPadType ({
      BidirStd, // IO_TRIGGER
      BidirStd, // IO_CLKOUT
      BidirStd, // IO_USB_SUSPEND
      BidirStd, // IO_USB_SPEED
      BidirStd, // IO_USB_OE_N
      BidirStd, // IO_USB_DN_RX
      BidirStd, // IO_USB_DP_RX
      BidirStd, // IO_USB_D_RX
      BidirStd, // IO_USB_DN_TX
      BidirStd, // IO_USB_DP_TX
      BidirStd, // IO_USB_CONNECT
      InputStd, // IO_CLK
      BidirOd, // IOR9
      BidirOd, // IOR8
      InputStd, // SPI_DEV_CS_L
      InputStd, // SPI_DEV_CLK
      BidirStd, // SPI_DEV_D3
      BidirStd, // SPI_DEV_D2
      BidirStd, // SPI_DEV_D1
      BidirStd, // SPI_DEV_D0
      BidirStd, // SPI_HOST_CS_L
      BidirStd, // SPI_HOST_CLK
      BidirStd, // SPI_HOST_D3
      BidirStd, // SPI_HOST_D2
      BidirStd, // SPI_HOST_D1
      BidirStd, // SPI_HOST_D0
      InputStd  // POR_N
    }),
    .MioPadType ({
      BidirOd, // IOR13
      BidirOd, // IOR12
      BidirOd, // IOR11
      BidirOd, // IOR10
      BidirStd, // IOR7
      BidirStd, // IOR6
      BidirStd, // IOR5
      BidirStd, // IOR4
      BidirStd, // IOR3
      BidirStd, // IOR2
      BidirStd, // IOR1
      BidirStd, // IOR0
      BidirOd, // IOC12
      BidirOd, // IOC11
      BidirOd, // IOC10
      BidirStd, // IOC9
      BidirStd, // IOC8
      BidirStd, // IOC7
      BidirStd, // IOC6
      BidirStd, // IOC5
      BidirStd, // IOC4
      BidirStd, // IOC3
      BidirStd, // IOC2
      BidirStd, // IOC1
      BidirStd, // IOC0
      BidirOd, // IOB12
      BidirOd, // IOB11
      BidirOd, // IOB10
      BidirOd, // IOB9
      BidirStd, // IOB8
      BidirStd, // IOB7
      BidirStd, // IOB6
      BidirStd, // IOB5
      BidirStd, // IOB4
      BidirStd, // IOB3
      BidirStd, // IOB2
      BidirStd, // IOB1
      BidirStd, // IOB0
      BidirOd, // IOA8
      BidirOd, // IOA7
      BidirOd, // IOA6
      BidirStd, // IOA5
      BidirStd, // IOA4
      BidirStd, // IOA3
      BidirStd, // IOA2
      BidirStd, // IOA1
      BidirStd  // IOA0
    })
  ) u_padring (
    // This is only used for scan and DFT purposes
    .clk_scan_i(padring_scan_clk),
    .scanmode_i(scanmode),

    .mux_iob_sel_i(mux_iob_sel),
    .dio_in_raw_o (dio_in_raw ),

    // Chip IOs
    .dio_pad_io ({
      IO_TRIGGER,
      IO_CLKOUT,
      IO_USB_SUSPEND,
      IO_USB_SPEED,
      IO_USB_OE_N,
      IO_USB_DN_RX,
      IO_USB_DP_RX,
      IO_USB_D_RX,
      IO_USB_DN_TX,
      IO_USB_DP_TX,
      IO_USB_CONNECT,
      IO_CLK,
      IOR9,
      IOR8,
      SPI_DEV_CS_L,
      SPI_DEV_CLK,
      SPI_DEV_D3,
      SPI_DEV_D2,
      SPI_DEV_D1,
      SPI_DEV_D0,
      SPI_HOST_CS_L,
      SPI_HOST_CLK,
      SPI_HOST_D3,
      SPI_HOST_D2,
      SPI_HOST_D1,
      SPI_HOST_D0,
      POR_N
    }),

    .mio_pad_io ({
      IOR13,
      IOR12,
      IOR11,
      IOR10,
      IOR7,
      IOR6,
      IOR5,
      IOR4,
      IOR3,
      IOR2,
      IOR1,
      IOR0,
      IOC12,
      IOC11,
      IOC10,
      IOC9,
      IOC8,
      IOC7,
      IOC6,
      IOC5,
      IOC4,
      IOC3,
      IOC2,
      IOC1,
      IOC0,
      IOB12,
      IOB11,
      IOB10,
      IOB9,
      IOB8,
      IOB7,
      IOB6,
      IOB5,
      IOB4,
      IOB3,
      IOB2,
      IOB1,
      IOB0,
      IOA8,
      IOA7,
      IOA6,
      IOA5,
      IOA4,
`ifdef ANALOGSIM
      '0,
`else
      IOA3,
`endif
`ifdef ANALOGSIM
      '0,
`else
      IOA2,
`endif
      IOA1,
      IOA0
    }),

    // Core-facing
    .dio_in_o ({
        manual_in_io_trigger,
        manual_in_io_clkout,
        manual_in_io_usb_suspend,
        manual_in_io_usb_speed,
        manual_in_io_usb_oe_n,
        manual_in_io_usb_dn_rx,
        manual_in_io_usb_dp_rx,
        manual_in_io_usb_d_rx,
        manual_in_io_usb_dn_tx,
        manual_in_io_usb_dp_tx,
        manual_in_io_usb_connect,
        manual_in_io_clk,
        dio_in[DioSysrstCtrlFlashWpL],
        dio_in[DioSysrstCtrlEcRstL],
        dio_in[DioSpiDeviceCsb],
        dio_in[DioSpiDeviceSck],
        dio_in[DioSpiDeviceSd3],
        dio_in[DioSpiDeviceSd2],
        dio_in[DioSpiDeviceSd1],
        dio_in[DioSpiDeviceSd0],
        dio_in[DioSpiHost0Csb],
        dio_in[DioSpiHost0Sck],
        dio_in[DioSpiHost0Sd3],
        dio_in[DioSpiHost0Sd2],
        dio_in[DioSpiHost0Sd1],
        dio_in[DioSpiHost0Sd0],
        manual_in_por_n
      }),
    .dio_out_i ({
        manual_out_io_trigger,
        manual_out_io_clkout,
        manual_out_io_usb_suspend,
        manual_out_io_usb_speed,
        manual_out_io_usb_oe_n,
        manual_out_io_usb_dn_rx,
        manual_out_io_usb_dp_rx,
        manual_out_io_usb_d_rx,
        manual_out_io_usb_dn_tx,
        manual_out_io_usb_dp_tx,
        manual_out_io_usb_connect,
        manual_out_io_clk,
        dio_out[DioSysrstCtrlFlashWpL],
        dio_out[DioSysrstCtrlEcRstL],
        dio_out[DioSpiDeviceCsb],
        dio_out[DioSpiDeviceSck],
        dio_out[DioSpiDeviceSd3],
        dio_out[DioSpiDeviceSd2],
        dio_out[DioSpiDeviceSd1],
        dio_out[DioSpiDeviceSd0],
        dio_out[DioSpiHost0Csb],
        dio_out[DioSpiHost0Sck],
        dio_out[DioSpiHost0Sd3],
        dio_out[DioSpiHost0Sd2],
        dio_out[DioSpiHost0Sd1],
        dio_out[DioSpiHost0Sd0],
        manual_out_por_n
      }),
    .dio_oe_i ({
        manual_oe_io_trigger,
        manual_oe_io_clkout,
        manual_oe_io_usb_suspend,
        manual_oe_io_usb_speed,
        manual_oe_io_usb_oe_n,
        manual_oe_io_usb_dn_rx,
        manual_oe_io_usb_dp_rx,
        manual_oe_io_usb_d_rx,
        manual_oe_io_usb_dn_tx,
        manual_oe_io_usb_dp_tx,
        manual_oe_io_usb_connect,
        manual_oe_io_clk,
        dio_oe[DioSysrstCtrlFlashWpL],
        dio_oe[DioSysrstCtrlEcRstL],
        dio_oe[DioSpiDeviceCsb],
        dio_oe[DioSpiDeviceSck],
        dio_oe[DioSpiDeviceSd3],
        dio_oe[DioSpiDeviceSd2],
        dio_oe[DioSpiDeviceSd1],
        dio_oe[DioSpiDeviceSd0],
        dio_oe[DioSpiHost0Csb],
        dio_oe[DioSpiHost0Sck],
        dio_oe[DioSpiHost0Sd3],
        dio_oe[DioSpiHost0Sd2],
        dio_oe[DioSpiHost0Sd1],
        dio_oe[DioSpiHost0Sd0],
        manual_oe_por_n
      }),
    .dio_attr_i ({
        manual_attr_io_trigger,
        manual_attr_io_clkout,
        manual_attr_io_usb_suspend,
        manual_attr_io_usb_speed,
        manual_attr_io_usb_oe_n,
        manual_attr_io_usb_dn_rx,
        manual_attr_io_usb_dp_rx,
        manual_attr_io_usb_d_rx,
        manual_attr_io_usb_dn_tx,
        manual_attr_io_usb_dp_tx,
        manual_attr_io_usb_connect,
        manual_attr_io_clk,
        dio_attr[DioSysrstCtrlFlashWpL],
        dio_attr[DioSysrstCtrlEcRstL],
        dio_attr[DioSpiDeviceCsb],
        dio_attr[DioSpiDeviceSck],
        dio_attr[DioSpiDeviceSd3],
        dio_attr[DioSpiDeviceSd2],
        dio_attr[DioSpiDeviceSd1],
        dio_attr[DioSpiDeviceSd0],
        dio_attr[DioSpiHost0Csb],
        dio_attr[DioSpiHost0Sck],
        dio_attr[DioSpiHost0Sd3],
        dio_attr[DioSpiHost0Sd2],
        dio_attr[DioSpiHost0Sd1],
        dio_attr[DioSpiHost0Sd0],
        manual_attr_por_n
      }),

    .mio_in_o (mio_in[46:0]),
    .mio_out_i (mio_out[46:0]),
    .mio_oe_i (mio_oe[46:0]),
    .mio_attr_i (mio_attr[46:0]),
    .mio_in_raw_o (mio_in_raw[46:0])
  );
  // TODO: generalize this USB mux code and align with other tops.

  // Only use the UPHY on CW310, which does not support pin flipping.
  logic usb_dp_pullup_en;
  logic usb_rx_d;
  logic usb_rx_enable;

  // DioUsbdevUsbDn
  assign manual_attr_io_usb_dn_tx = '0;
  assign manual_out_io_usb_dn_tx = dio_out[DioUsbdevUsbDn];
  assign manual_oe_io_usb_dn_tx = 1'b1;
  assign dio_in[DioUsbdevUsbDn] = manual_in_io_usb_dn_rx;
  // DioUsbdevUsbDp
  assign manual_attr_io_usb_dp_tx = '0;
  assign manual_out_io_usb_dp_tx = dio_out[DioUsbdevUsbDp];
  assign manual_oe_io_usb_dp_tx = 1'b1;
  assign dio_in[DioUsbdevUsbDp] = manual_in_io_usb_dp_rx;

  assign manual_attr_io_usb_oe_n = '0;
  assign manual_out_io_usb_oe_n = ~dio_oe[DioUsbdevUsbDp];
  assign manual_oe_io_usb_oe_n = 1'b1;

  // DioUsbdevD
  assign manual_attr_io_usb_d_rx = '0;
  assign usb_rx_d = manual_in_io_usb_d_rx;

  // Pull-up / soft connect pin
  assign manual_attr_io_usb_connect = '0;
  assign manual_out_io_usb_connect = usb_dp_pullup_en;
  assign manual_oe_io_usb_connect = 1'b1;

  // Set SPD to full-speed
  assign manual_attr_io_usb_speed = '0;
  assign manual_out_io_usb_speed = 1'b1;
  assign manual_oe_io_usb_speed = 1'b1;

  // TUSB1106 low-power mode
  assign manual_attr_io_usb_suspend = '0;
  assign manual_out_io_usb_suspend = !usb_rx_enable;
  assign manual_oe_io_usb_suspend = 1'b1;

  logic unused_usb_sigs;
  assign unused_usb_sigs = ^{
    manual_in_io_usb_connect,
    manual_in_io_usb_oe_n,
    manual_in_io_usb_speed,
    manual_in_io_usb_suspend,
    // DP and DN are broken out into multiple unidirectional pins
    dio_oe[DioUsbdevUsbDp],
    dio_oe[DioUsbdevUsbDn],
    dio_attr[DioUsbdevUsbDp],
    dio_attr[DioUsbdevUsbDn]
  };

  /////////////////////
  // Memory Backdoor //
  /////////////////////

  // Multiplexed I/O routed through the backdoor loader
  pad_attr_t [pinmux_reg_pkg::NMioPads-1:0] mio_bkdr_attr;
  logic      [pinmux_reg_pkg::NMioPads-1:0] mio_bkdr_out;
  logic      [pinmux_reg_pkg::NMioPads-1:0] mio_bkdr_oe;
  logic      [pinmux_reg_pkg::NMioPads-1:0] mio_bkdr_in;

  if (BkdrLoaderEn) begin : gen_bkdr

    // Get TAP strap signals from pad frame
    logic tap_strap0;
    logic tap_strap1;
    logic bkdr_ena;
    logic rst_n;

    // Main JTAG port
    jtag_pkg::jtag_req_t jtag_req_i;
    jtag_pkg::jtag_rsp_t jtag_rsp_o;

    // D/S JTAG port
    jtag_pkg::jtag_req_t jtag_req_o;
    jtag_pkg::jtag_rsp_t jtag_rsp_i;

    // Backdoor ports
    bkdr_loader_pkg::bkdr_req_t [bkdr_loader_reg_pkg::NumBkdrTgts-1:0] bkdr_req;
    bkdr_loader_pkg::bkdr_rsp_t [bkdr_loader_reg_pkg::NumBkdrTgts-1:0] bkdr_rsp;

    bkdr_loader i_bkdr_loader (
      .clk_i      (clk_main),
      .rst_ni     (bkdr_rst_n),
      .bkdr_ena_i (bkdr_ena),
      .jtag_req_i (jtag_req_i),
      .jtag_rsp_o (jtag_rsp_o),
      .jtag_req_o (jtag_req_o),
      .jtag_rsp_i (jtag_rsp_i),
      .fpga_info_i(fpga_info),
      .bkdr_req_o (bkdr_req),
      .bkdr_rsp_i (bkdr_rsp),
      .rst_no     (rst_n)
    );

    // Connect requests
    `BKDR_LOADER_CONNECT_REQS

    // Connect responses
    `BKDR_LOADER_CONNECT_RSPS

    always_comb begin : proc_conn_bkdr
      // Through-connection
      mio_attr    = mio_bkdr_attr;
      mio_out     = mio_bkdr_out;
      mio_oe      = mio_bkdr_oe;
      mio_bkdr_in = mio_in;

      // Connect backdoor JTAG input
      jtag_req_i.tck      = mio_in[TckPadIdx];
      jtag_req_i.tms      = mio_in[TmsPadIdx];
      jtag_req_i.trst_n   = mio_in[TrstNPadIdx];
      jtag_req_i.tdi      = mio_in[TdiPadIdx];
      mio_out[TdoPadIdx]  = jtag_rsp_o.tdo;
      mio_oe[TdoPadIdx]   = jtag_rsp_o.tdo_oe;
      mio_attr[TdoPadIdx] = '0;

      // Connect backdoor JTAG output
      mio_bkdr_in[TckPadIdx]   = jtag_req_o.tck;
      mio_bkdr_in[TmsPadIdx]   = jtag_req_o.tms;
      mio_bkdr_in[TrstNPadIdx] = jtag_req_o.trst_n;
      mio_bkdr_in[TdiPadIdx]   = jtag_req_o.tdi;
      jtag_rsp_i.tdo           = mio_bkdr_out[TdoPadIdx];
      jtag_rsp_i.tdo_oe        = mio_bkdr_oe[TdoPadIdx];
    end

    // Connect TAP strap signals to pad frame
    assign tap_strap0 = mio_in[Tap0PadIdx];
    assign tap_strap1 = mio_in[Tap1PadIdx];

    // Bkdr loader is activated if both tap_strap signals are set to 1'b1.
    assign bkdr_ena = tap_strap0 && tap_strap1;

  end else begin : gen_no_bkdr
    assign mio_attr    = mio_bkdr_attr;
    assign mio_out     = mio_bkdr_out;
    assign mio_oe      = mio_bkdr_oe;
    assign mio_bkdr_in = mio_in;
    assign bkdr_rst_n  = manual_in_por_n;
  end

  //////////////////
  // PLL for FPGA //
  //////////////////

  assign manual_attr_io_clk = '0;
  assign manual_out_io_clk = 1'b0;
  assign manual_oe_io_clk = 1'b0;
  assign manual_attr_por_n = '0;
  assign manual_out_por_n = 1'b0;
  assign manual_oe_por_n = 1'b0;

  // the rst_ni pin only goes to AST
  // the rest of the logic generates reset based on the 'pok' signal.
  // for verilator purposes, make these two the same.
  prim_mubi_pkg::mubi4_t lc_clk_bypass;   // TODO Tim

  ////////////////////////
  // AST related wiring //
  ////////////////////////
  logic clk_ast_ext;
  prim_mubi_pkg::mubi4_t cg_en_ast_ext;
  // This clock gate is never used inside the top. It is a topgen artifact of an external clock.
  assign cg_en_ast_ext = prim_mubi_pkg::MuBi4False;

  ast_pkg::clks_osc_byp_t clks_osc_byp;

  // Debug connections
  logic [ast_pkg::Pad2AstInWidth-1:0] padmux2ast;

  // TODO: Hook this up when FPGA pads are updated
  assign clk_ast_ext = '0;
  assign padmux2ast = '0;

  logic bkdr_rst_n;
  logic clk_main, clk_io, clk_usb_48mhz, clk_aon;
  clkgen_xil_ultrascale # (
    .AddClkBuf(0)
  ) clkgen (
    .clk_i(manual_in_io_clk),
    .rst_ni(manual_in_por_n),
    .clk_main_o(clk_main),
    .clk_io_o(clk_io),
    .clk_48MHz_o(clk_usb_48mhz),
    .clk_aon_o(clk_aon),
    .rst_no(bkdr_rst_n)
  );

  logic [31:0] fpga_info;
  usr_access_xil7series u_info (
    .info_o(fpga_info)
  );

  assign clks_osc_byp = '{
    usb: clk_usb_48mhz,
    sys: clk_main,
    io:  clk_io,
    aon: clk_aon
  };

  // Tie-off supply voltage test signals
  ast_pkg::ast_vx_supp_t ast_vx_supp;
  assign ast_vx_supp = '{
    vcc:    1'b1,
    vcaon:  1'b1,
    vcmain: 1'b1,
    vioa:   1'b1,
    viob:   1'b1
  };

  // flash observation (only for englishbreakfast)
  logic [7:0] flash_obs;
  assign flash_obs = '0;

  // Tie-off observation signals
  ast_pkg::ast_obs_bus_t ast_obs;
  assign ast_obs = '{
    fla_obs: flash_obs,
    otp_obs: '0,
    otm_obs: '0,
    usb_obs: '0
  };

  // Feed the same bypass struct to both PDs. This is a limitation as topgen cannot distribute the
  // same external signal to multiple IP ports from the top. The 'top' signals are local to their
  // power domain. Note these are only relevant for FPGA and verilator. But we always connect them
  // as topgen does not support conditional port generation.
  ast_pkg::clks_osc_byp_t clk_osc_byp_pd_main;
  ast_pkg::clks_osc_byp_t clk_osc_byp_pd_aon;
  assign clk_osc_byp_pd_main = clks_osc_byp;
  assign clk_osc_byp_pd_aon  = clks_osc_byp;

  // AST power states are unused
  logic unused_ast_pwst_h;
  assign unused_ast_pwst_h = ^ast_pwst_h;
  ///////////////////////////////////////
  // top_earlgrey: power domains //
  ///////////////////////////////////////
  top_earlgrey #(
    .SecAesMasking(1'b1),
    .SecAesSBoxImpl(aes_pkg::SBoxImplDom),
    .SecAesStartTriggerDelay(0),
    .SecAesAllowForcingMasks(1'b1),
    .CsrngSBoxImpl(aes_pkg::SBoxImplLut),
    .OtbnRegFile(otbn_pkg::RegFileFPGA),
    .SecOtbnSkipUrndReseedAtStart(1'b0),
    .RvCoreIbexPipeLine(1),
    .UsbdevRcvrWakeTimeUs(10000),
    .SramCtrlRetInstrExec(0),
    .KmacEnMasking(1),
    .KmacSwKeyMasked(1),
    .KeymgrDpeKmacEnMasking(1),
    .RvCoreIbexSecureIbex(1),
    .RomCtrlBootRomInitFile(BootRomInitFile),
    .RvCoreIbexRegFile(ibex_pkg::RegFileFPGA),
    .SramCtrlMainInstrExec(1),
    .PinmuxTargetCfg(PinmuxTargetCfg)
  ) top_earlgrey (
    // Unmanaged external clocks
    .clk_ast_ext_i  (clk_ast_ext),
    .cg_en_ast_ext_i(cg_en_ast_ext),

    // Manual DFT signals
    .padring_scan_clk_o(padring_scan_clk),

    // Multiplexed I/O to backdoor
    .mio_in_i (mio_bkdr_in ),
    .mio_out_o(mio_bkdr_out),
    .mio_oe_o (mio_bkdr_oe ),

    // Dedicated I/O
    .dio_in_i (dio_in ),
    .dio_out_o(dio_out),
    .dio_oe_o (dio_oe ),

    // Pad attributes
    .mio_attr_o(mio_bkdr_attr),
    .dio_attr_o(dio_attr),

    // Regular ports (auto-generated)
    .manual_in_por_n_i            (rst_n              ),
    .scanmode_o                   (scanmode           ),
    .scan_en_o                    (                   ),
    .scan_rst_n_o                 (                   ),
    .usb_io_pu_cal_o              (                   ),
    .padmux2ast_i                 (padmux2ast         ),
    .mux_iob_sel_o                (mux_iob_sel        ),
    .ast_vx_supp_i                (ast_vx_supp        ),
    .ast_obs_i                    (ast_obs            ),
    .ast_adc_a0_a_i               (ast_adc_a0_a       ),
    .ast_adc_a1_a_i               (ast_adc_a1_a       ),
    .ast2pad_t0_a_o               (ast2pad_t0_a       ),
    .ast2pad_t1_a_o               (ast2pad_t1_a       ),
    .clk_osc_byp_pd_main_i        (clk_osc_byp_pd_main),
    .clk_osc_byp_pd_aon_i         (clk_osc_byp_pd_aon ),
    .ast_pwst_h_o                 (ast_pwst_h         ),
    .dft_hold_tap_sel_i           ('0                 ),
    .usb_dp_pullup_en_o           (usb_dp_pullup_en   ),
    .usb_dn_pullup_en_o           (                   ),
    .rram_test_analog_io          ('0                 ),
    .fpga_info_i                  (fpga_info          ),
    .sensor_ctrl_manual_pad_attr_o(                   ),
    .usbdev_usb_rx_d_i            (usb_rx_d           ),
    .usbdev_usb_tx_d_o            (                   ),
    .usbdev_usb_tx_se0_o          (                   ),
    .usbdev_usb_tx_use_d_se0_o    (                   ),
    .usbdev_usb_rx_enable_o       (usb_rx_enable      )
  );


  /////////////////////////////////////////////////////
  // ChipWhisperer CW310/305 Capture Board Interface //
  /////////////////////////////////////////////////////
  // This is used to interface OpenTitan as a target with a capture board trough the ChipWhisperer
  // 20-pin connector. This is used for SCA/FI experiments only.

  logic unused_inputs;
  assign unused_inputs = manual_in_io_clkout ^ manual_in_io_trigger;

  // Synchronous clock output to capture board.
  assign manual_out_io_clkout = manual_in_io_clk;
  assign manual_oe_io_clkout = 1'b1;

  // Capture trigger.
  // We use the clkmgr_idle signal of the IP of interest to form a precise capture trigger.
  // GPIO[11:10] is used for selecting the IP of interest. The encoding is as follows (see
  // hint_names_e enum in clkmgr_pkg.sv for details).
  //
  // IP              - GPIO[11:10] - Index for clkmgr_idle
  // -------------------------------------------------------------
  //  AES            -   00       -  0
  //  HMAC           -   01       -  1 - not implemented on CW305
  //  KMAC           -   10       -  2 - not implemented on CW305
  //  OTBN           -   11       -  3 - not implemented on CW305
  //
  // GPIO9 is used for gating the selected capture trigger in software. Alternatively, GPIO8
  // can be used to implement a less precise but fully software-controlled capture trigger
  // similar to what can be done on ASIC.
  //
  // Note that on the CW305, GPIO[9,8] are connected to LED[5(Green),7(Red)].

  prim_mubi_pkg::mubi4_t clk_trans_idle, manual_in_io_clk_idle;

  clkmgr_pkg::hint_names_e trigger_sel;
  always_comb begin : trigger_sel_mux
    unique case ({mio_out[MioOutGpioGpio11], mio_out[MioOutGpioGpio10]})
      2'b00:   trigger_sel = clkmgr_pkg::HintMainAes;
      2'b01:   trigger_sel = clkmgr_pkg::HintMainHmac;
      2'b10:   trigger_sel = clkmgr_pkg::HintMainKmac;
      2'b11:   trigger_sel = clkmgr_pkg::HintMainOtbn;
      default: trigger_sel = clkmgr_pkg::HintMainAes;
    endcase;
  end
  assign clk_trans_idle = top_earlgrey.earlgrey_pd_aon.u_clkmgr.idle_i[trigger_sel];

  logic clk_io_div4_trigger_hw_en, manual_in_io_clk_trigger_hw_en;
  logic clk_io_div4_trigger_hw_oe, manual_in_io_clk_trigger_hw_oe;
  logic clk_io_div4_trigger_sw_en, manual_in_io_clk_trigger_sw_en;
  logic clk_io_div4_trigger_sw_oe, manual_in_io_clk_trigger_sw_oe;
  assign clk_io_div4_trigger_hw_en = mio_out[MioOutGpioGpio9];
  assign clk_io_div4_trigger_hw_oe = mio_oe[MioOutGpioGpio9];
  assign clk_io_div4_trigger_sw_en = mio_out[MioOutGpioGpio8];
  assign clk_io_div4_trigger_sw_oe = mio_oe[MioOutGpioGpio8];

  // Synchronize signals to manual_in_io_clk.
  prim_flop_2sync #(
    .Width ($bits(clk_trans_idle) + 4)
  ) u_sync_trigger (
    .clk_i (manual_in_io_clk),
    .rst_ni(manual_in_por_n),
    .d_i   ({clk_trans_idle,
             clk_io_div4_trigger_hw_en,
             clk_io_div4_trigger_hw_oe,
             clk_io_div4_trigger_sw_en,
             clk_io_div4_trigger_sw_oe}),
    .q_o   ({manual_in_io_clk_idle,
             manual_in_io_clk_trigger_hw_en,
             manual_in_io_clk_trigger_hw_oe,
             manual_in_io_clk_trigger_sw_en,
             manual_in_io_clk_trigger_sw_oe})
  );

  // Generate the actual trigger signal as trigger_sw OR trigger_hw.
  assign manual_attr_io_trigger = '0;
  assign manual_oe_io_trigger  =
      manual_in_io_clk_trigger_sw_oe | manual_in_io_clk_trigger_hw_oe;
  assign manual_out_io_trigger =
      manual_in_io_clk_trigger_sw_en | (manual_in_io_clk_trigger_hw_en &
          prim_mubi_pkg::mubi4_test_false_strict(manual_in_io_clk_idle));
endmodule
