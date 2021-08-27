// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_earlgrey/data/top_earlgrey.hjson \
//                -o hw/top_earlgrey/ \
//                --rnd_cnst_seed 4881560218908238235

module chip_earlgrey_nexysvideo #(
  // Path to a VMEM file containing the contents of the boot ROM, which will be
  // baked into the FPGA bitstream.
  parameter BootRomInitFile = "boot_rom_fpga_nexysvideo.32.vmem",
  // Path to a VMEM file containing the contents of the emulated OTP, which will be
  // baked into the FPGA bitstream.
  parameter OtpCtrlMemInitFile = "otp_img_fpga_nexysvideo.vmem"
) (
  // Dedicated Pads
  inout POR_N, // Manual Pad
  inout USB_P, // Manual Pad
  inout USB_N, // Manual Pad
  inout SPI_DEV_D0, // Dedicated Pad for spi_device_sd
  inout SPI_DEV_D1, // Dedicated Pad for spi_device_sd
  inout SPI_DEV_CLK, // Dedicated Pad for spi_device_sck
  inout SPI_DEV_CS_L, // Dedicated Pad for spi_device_csb
  inout IO_CLK, // Manual Pad
  inout IO_JSRST_N, // Manual Pad
  inout IO_USB_SENSE0, // Manual Pad
  inout IO_USB_DNPULLUP0, // Manual Pad
  inout IO_USB_DPPULLUP0, // Manual Pad
  inout IO_UPHY_DP_TX, // Manual Pad
  inout IO_UPHY_DN_TX, // Manual Pad
  inout IO_UPHY_DP_RX, // Manual Pad
  inout IO_UPHY_DN_RX, // Manual Pad
  inout IO_UPHY_D_RX, // Manual Pad
  inout IO_UPHY_OE_N, // Manual Pad
  inout IO_UPHY_SENSE, // Manual Pad
  inout IO_UPHY_DPPULLUP, // Manual Pad

  // Muxed Pads
  inout IOA0, // MIO Pad 0
  inout IOA1, // MIO Pad 1
  inout IOA2, // MIO Pad 2
  inout IOA3, // MIO Pad 3
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
  inout IOC2, // MIO Pad 24
  inout IOC3, // MIO Pad 25
  inout IOC4, // MIO Pad 26
  inout IOC5, // MIO Pad 27
  inout IOC6, // MIO Pad 28
  inout IOC7, // MIO Pad 29
  inout IOC8, // MIO Pad 30
  inout IOC9, // MIO Pad 31
  inout IOC10, // MIO Pad 32
  inout IOC11  // MIO Pad 33
);

  import top_earlgrey_pkg::*;
  import prim_pad_wrapper_pkg::*;

  ////////////////////////////
  // Special Signal Indices //
  ////////////////////////////

  parameter int Tap0PadIdx = 22;
  parameter int Tap1PadIdx = 16;
  parameter int Dft0PadIdx = 23;
  parameter int Dft1PadIdx = 34;
  parameter int TckPadIdx = 59;
  parameter int TmsPadIdx = 60;
  parameter int TrstNPadIdx = 18;
  parameter int TdiPadIdx = 51;
  parameter int TdoPadIdx = 52;

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
    usb_dp_idx:        DioUsbdevDp,
    usb_dn_idx:        DioUsbdevDn,
    usb_dp_pullup_idx: DioUsbdevDpPullup,
    usb_dn_pullup_idx: DioUsbdevDnPullup,
    // Pad types for attribute WARL behavior
    dio_pad_type: {
      BidirOd, // DIO sysrst_ctrl_aon_flash_wp_l
      BidirTol, // DIO usbdev_rx_enable
      BidirTol, // DIO usbdev_suspend
      BidirTol, // DIO usbdev_tx_mode_se
      BidirTol, // DIO usbdev_dn_pullup
      BidirTol, // DIO usbdev_dp_pullup
      BidirTol, // DIO usbdev_se0
      BidirStd, // DIO spi_host0_csb
      BidirStd, // DIO spi_host0_sck
      BidirTol, // DIO usbdev_sense
      InputStd, // DIO spi_device_csb
      InputStd, // DIO spi_device_sck
      BidirOd, // DIO sysrst_ctrl_aon_ec_rst_l
      BidirTol, // DIO usbdev_dn
      BidirTol, // DIO usbdev_dp
      BidirTol, // DIO usbdev_d
      BidirStd, // DIO spi_device_sd
      BidirStd, // DIO spi_device_sd
      BidirStd, // DIO spi_device_sd
      BidirStd, // DIO spi_device_sd
      BidirStd, // DIO spi_host0_sd
      BidirStd, // DIO spi_host0_sd
      BidirStd, // DIO spi_host0_sd
      BidirStd  // DIO spi_host0_sd
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
  logic [pinmux_reg_pkg::NMioPads-1:0] mio_in_raw;
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_out;
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_oe;
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_in;

  logic unused_mio_in_raw;
  assign unused_mio_in_raw = ^mio_in_raw;

  // Manual pads
  logic manual_in_por_n, manual_out_por_n, manual_oe_por_n;
  logic manual_in_usb_p, manual_out_usb_p, manual_oe_usb_p;
  logic manual_in_usb_n, manual_out_usb_n, manual_oe_usb_n;
  logic manual_in_io_clk, manual_out_io_clk, manual_oe_io_clk;
  logic manual_in_io_jsrst_n, manual_out_io_jsrst_n, manual_oe_io_jsrst_n;
  logic manual_in_io_usb_sense0, manual_out_io_usb_sense0, manual_oe_io_usb_sense0;
  logic manual_in_io_usb_dnpullup0, manual_out_io_usb_dnpullup0, manual_oe_io_usb_dnpullup0;
  logic manual_in_io_usb_dppullup0, manual_out_io_usb_dppullup0, manual_oe_io_usb_dppullup0;
  logic manual_in_io_uphy_dp_tx, manual_out_io_uphy_dp_tx, manual_oe_io_uphy_dp_tx;
  logic manual_in_io_uphy_dn_tx, manual_out_io_uphy_dn_tx, manual_oe_io_uphy_dn_tx;
  logic manual_in_io_uphy_dp_rx, manual_out_io_uphy_dp_rx, manual_oe_io_uphy_dp_rx;
  logic manual_in_io_uphy_dn_rx, manual_out_io_uphy_dn_rx, manual_oe_io_uphy_dn_rx;
  logic manual_in_io_uphy_d_rx, manual_out_io_uphy_d_rx, manual_oe_io_uphy_d_rx;
  logic manual_in_io_uphy_oe_n, manual_out_io_uphy_oe_n, manual_oe_io_uphy_oe_n;
  logic manual_in_io_uphy_sense, manual_out_io_uphy_sense, manual_oe_io_uphy_sense;
  logic manual_in_io_uphy_dppullup, manual_out_io_uphy_dppullup, manual_oe_io_uphy_dppullup;

  pad_attr_t manual_attr_por_n;
  pad_attr_t manual_attr_usb_p;
  pad_attr_t manual_attr_usb_n;
  pad_attr_t manual_attr_io_clk;
  pad_attr_t manual_attr_io_jsrst_n;
  pad_attr_t manual_attr_io_usb_sense0;
  pad_attr_t manual_attr_io_usb_dnpullup0;
  pad_attr_t manual_attr_io_usb_dppullup0;
  pad_attr_t manual_attr_io_uphy_dp_tx;
  pad_attr_t manual_attr_io_uphy_dn_tx;
  pad_attr_t manual_attr_io_uphy_dp_rx;
  pad_attr_t manual_attr_io_uphy_dn_rx;
  pad_attr_t manual_attr_io_uphy_d_rx;
  pad_attr_t manual_attr_io_uphy_oe_n;
  pad_attr_t manual_attr_io_uphy_sense;
  pad_attr_t manual_attr_io_uphy_dppullup;

  /////////////////////////
  // Stubbed pad tie-off //
  /////////////////////////

  // Only signals going to non-custom pads need to be tied off.
  logic [69:0] unused_sig;
  assign dio_in[DioSpiHost0Sd0] = 1'b0;
  assign unused_sig[9] = dio_out[DioSpiHost0Sd0] ^ dio_oe[DioSpiHost0Sd0];
  assign dio_in[DioSpiHost0Sd1] = 1'b0;
  assign unused_sig[10] = dio_out[DioSpiHost0Sd1] ^ dio_oe[DioSpiHost0Sd1];
  assign dio_in[DioSpiHost0Sd2] = 1'b0;
  assign unused_sig[11] = dio_out[DioSpiHost0Sd2] ^ dio_oe[DioSpiHost0Sd2];
  assign dio_in[DioSpiHost0Sd3] = 1'b0;
  assign unused_sig[12] = dio_out[DioSpiHost0Sd3] ^ dio_oe[DioSpiHost0Sd3];
  assign dio_in[DioSpiHost0Sck] = 1'b0;
  assign unused_sig[13] = dio_out[DioSpiHost0Sck] ^ dio_oe[DioSpiHost0Sck];
  assign dio_in[DioSpiHost0Csb] = 1'b0;
  assign unused_sig[14] = dio_out[DioSpiHost0Csb] ^ dio_oe[DioSpiHost0Csb];
  assign dio_in[DioSpiDeviceSd2] = 1'b0;
  assign unused_sig[17] = dio_out[DioSpiDeviceSd2] ^ dio_oe[DioSpiDeviceSd2];
  assign dio_in[DioSpiDeviceSd3] = 1'b0;
  assign unused_sig[18] = dio_out[DioSpiDeviceSd3] ^ dio_oe[DioSpiDeviceSd3];
  assign mio_in[19] = 1'b0;
  assign mio_in_raw[19] = 1'b0;
  assign unused_sig[40] = mio_out[19] ^ mio_oe[19];
  assign mio_in[20] = 1'b0;
  assign mio_in_raw[20] = 1'b0;
  assign unused_sig[41] = mio_out[20] ^ mio_oe[20];
  assign mio_in[21] = 1'b0;
  assign mio_in_raw[21] = 1'b0;
  assign unused_sig[42] = mio_out[21] ^ mio_oe[21];
  assign mio_in[22] = 1'b0;
  assign mio_in_raw[22] = 1'b0;
  assign unused_sig[43] = mio_out[22] ^ mio_oe[22];
  assign mio_in[23] = 1'b0;
  assign mio_in_raw[23] = 1'b0;
  assign unused_sig[44] = mio_out[23] ^ mio_oe[23];
  assign mio_in[34] = 1'b0;
  assign mio_in_raw[34] = 1'b0;
  assign unused_sig[55] = mio_out[34] ^ mio_oe[34];
  assign mio_in[35] = 1'b0;
  assign mio_in_raw[35] = 1'b0;
  assign unused_sig[56] = mio_out[35] ^ mio_oe[35];
  assign mio_in[36] = 1'b0;
  assign mio_in_raw[36] = 1'b0;
  assign unused_sig[57] = mio_out[36] ^ mio_oe[36];
  assign mio_in[37] = 1'b0;
  assign mio_in_raw[37] = 1'b0;
  assign unused_sig[58] = mio_out[37] ^ mio_oe[37];
  assign mio_in[38] = 1'b0;
  assign mio_in_raw[38] = 1'b0;
  assign unused_sig[59] = mio_out[38] ^ mio_oe[38];
  assign mio_in[39] = 1'b0;
  assign mio_in_raw[39] = 1'b0;
  assign unused_sig[60] = mio_out[39] ^ mio_oe[39];
  assign mio_in[40] = 1'b0;
  assign mio_in_raw[40] = 1'b0;
  assign unused_sig[61] = mio_out[40] ^ mio_oe[40];
  assign mio_in[41] = 1'b0;
  assign mio_in_raw[41] = 1'b0;
  assign unused_sig[62] = mio_out[41] ^ mio_oe[41];
  assign mio_in[42] = 1'b0;
  assign mio_in_raw[42] = 1'b0;
  assign unused_sig[63] = mio_out[42] ^ mio_oe[42];
  assign dio_in[DioSysrstCtrlAonEcRstL] = 1'b0;
  assign unused_sig[64] = dio_out[DioSysrstCtrlAonEcRstL] ^ dio_oe[DioSysrstCtrlAonEcRstL];
  assign dio_in[DioSysrstCtrlAonFlashWpL] = 1'b0;
  assign unused_sig[65] = dio_out[DioSysrstCtrlAonFlashWpL] ^ dio_oe[DioSysrstCtrlAonFlashWpL];
  assign mio_in[43] = 1'b0;
  assign mio_in_raw[43] = 1'b0;
  assign unused_sig[66] = mio_out[43] ^ mio_oe[43];
  assign mio_in[44] = 1'b0;
  assign mio_in_raw[44] = 1'b0;
  assign unused_sig[67] = mio_out[44] ^ mio_oe[44];
  assign mio_in[45] = 1'b0;
  assign mio_in_raw[45] = 1'b0;
  assign unused_sig[68] = mio_out[45] ^ mio_oe[45];
  assign mio_in[46] = 1'b0;
  assign mio_in_raw[46] = 1'b0;
  assign unused_sig[69] = mio_out[46] ^ mio_oe[46];

  //////////////////////
  // Padring Instance //
  //////////////////////


  padring #(
    // Padring specific counts may differ from pinmux config due
    // to custom, stubbed or added pads.
    .NDioPads(20),
    .NMioPads(29),
    .DioPadType ({
      BidirStd, // IO_UPHY_DPPULLUP
      BidirStd, // IO_UPHY_SENSE
      BidirStd, // IO_UPHY_OE_N
      BidirStd, // IO_UPHY_D_RX
      BidirStd, // IO_UPHY_DN_RX
      BidirStd, // IO_UPHY_DP_RX
      BidirStd, // IO_UPHY_DN_TX
      BidirStd, // IO_UPHY_DP_TX
      BidirStd, // IO_USB_DPPULLUP0
      BidirStd, // IO_USB_DNPULLUP0
      BidirStd, // IO_USB_SENSE0
      InputStd, // IO_JSRST_N
      InputStd, // IO_CLK
      InputStd, // SPI_DEV_CS_L
      InputStd, // SPI_DEV_CLK
      BidirStd, // SPI_DEV_D1
      BidirStd, // SPI_DEV_D0
      BidirTol, // USB_N
      BidirTol, // USB_P
      InputStd  // POR_N
    }),
    .MioPadType ({
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
    .clk_scan_i   ( 1'b0                  ),
    .scanmode_i   ( lc_ctrl_pkg::Off      ),
    .dio_in_raw_o ( ),
    // Chip IOs
    .dio_pad_io ({
      IO_UPHY_DPPULLUP,
      IO_UPHY_SENSE,
      IO_UPHY_OE_N,
      IO_UPHY_D_RX,
      IO_UPHY_DN_RX,
      IO_UPHY_DP_RX,
      IO_UPHY_DN_TX,
      IO_UPHY_DP_TX,
      IO_USB_DPPULLUP0,
      IO_USB_DNPULLUP0,
      IO_USB_SENSE0,
      IO_JSRST_N,
      IO_CLK,
      SPI_DEV_CS_L,
      SPI_DEV_CLK,
      SPI_DEV_D1,
      SPI_DEV_D0,
      USB_N,
      USB_P,
      POR_N
    }),

    .mio_pad_io ({
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
      IOA3,
      IOA2,
      IOA1,
      IOA0
    }),

    // Core-facing
    .dio_in_o ({
        manual_in_io_uphy_dppullup,
        manual_in_io_uphy_sense,
        manual_in_io_uphy_oe_n,
        manual_in_io_uphy_d_rx,
        manual_in_io_uphy_dn_rx,
        manual_in_io_uphy_dp_rx,
        manual_in_io_uphy_dn_tx,
        manual_in_io_uphy_dp_tx,
        manual_in_io_usb_dppullup0,
        manual_in_io_usb_dnpullup0,
        manual_in_io_usb_sense0,
        manual_in_io_jsrst_n,
        manual_in_io_clk,
        dio_in[DioSpiDeviceCsb],
        dio_in[DioSpiDeviceSck],
        dio_in[DioSpiDeviceSd1],
        dio_in[DioSpiDeviceSd0],
        manual_in_usb_n,
        manual_in_usb_p,
        manual_in_por_n
      }),
    .dio_out_i ({
        manual_out_io_uphy_dppullup,
        manual_out_io_uphy_sense,
        manual_out_io_uphy_oe_n,
        manual_out_io_uphy_d_rx,
        manual_out_io_uphy_dn_rx,
        manual_out_io_uphy_dp_rx,
        manual_out_io_uphy_dn_tx,
        manual_out_io_uphy_dp_tx,
        manual_out_io_usb_dppullup0,
        manual_out_io_usb_dnpullup0,
        manual_out_io_usb_sense0,
        manual_out_io_jsrst_n,
        manual_out_io_clk,
        dio_out[DioSpiDeviceCsb],
        dio_out[DioSpiDeviceSck],
        dio_out[DioSpiDeviceSd1],
        dio_out[DioSpiDeviceSd0],
        manual_out_usb_n,
        manual_out_usb_p,
        manual_out_por_n
      }),
    .dio_oe_i ({
        manual_oe_io_uphy_dppullup,
        manual_oe_io_uphy_sense,
        manual_oe_io_uphy_oe_n,
        manual_oe_io_uphy_d_rx,
        manual_oe_io_uphy_dn_rx,
        manual_oe_io_uphy_dp_rx,
        manual_oe_io_uphy_dn_tx,
        manual_oe_io_uphy_dp_tx,
        manual_oe_io_usb_dppullup0,
        manual_oe_io_usb_dnpullup0,
        manual_oe_io_usb_sense0,
        manual_oe_io_jsrst_n,
        manual_oe_io_clk,
        dio_oe[DioSpiDeviceCsb],
        dio_oe[DioSpiDeviceSck],
        dio_oe[DioSpiDeviceSd1],
        dio_oe[DioSpiDeviceSd0],
        manual_oe_usb_n,
        manual_oe_usb_p,
        manual_oe_por_n
      }),
    .dio_attr_i ({
        manual_attr_io_uphy_dppullup,
        manual_attr_io_uphy_sense,
        manual_attr_io_uphy_oe_n,
        manual_attr_io_uphy_d_rx,
        manual_attr_io_uphy_dn_rx,
        manual_attr_io_uphy_dp_rx,
        manual_attr_io_uphy_dn_tx,
        manual_attr_io_uphy_dp_tx,
        manual_attr_io_usb_dppullup0,
        manual_attr_io_usb_dnpullup0,
        manual_attr_io_usb_sense0,
        manual_attr_io_jsrst_n,
        manual_attr_io_clk,
        dio_attr[DioSpiDeviceCsb],
        dio_attr[DioSpiDeviceSck],
        dio_attr[DioSpiDeviceSd1],
        dio_attr[DioSpiDeviceSd0],
        manual_attr_usb_n,
        manual_attr_usb_p,
        manual_attr_por_n
      }),

    .mio_in_o ({
        mio_in[33:24],
        mio_in[18:0]
      }),
    .mio_out_i ({
        mio_out[33:24],
        mio_out[18:0]
      }),
    .mio_oe_i ({
        mio_oe[33:24],
        mio_oe[18:0]
      }),
    .mio_attr_i ({
        mio_attr[33:24],
        mio_attr[18:0]
      }),
    .mio_in_raw_o ({
        mio_in_raw[33:24],
        mio_in_raw[18:0]
      })
  );




  /////////////////////
  // USB Overlay Mux //
  /////////////////////

  // TODO: generalize this USB mux code and align with other tops.

  // Software can enable the pinflip feature inside usbdev.
  // The example hello_usbdev does this based on GPIO0 (a switch on the board)
  //
  // Here, we use the state of the DN pullup to effectively undo the
  // swapping such that the PCB always sees the unflipped D+/D-. We
  // could do the same inside the .xdc file but then two FPGA
  // bitstreams would be needed for testing.
  //
  // dio_in/out/oe map is: PADS <- _padring <- JTAG mux -> _umux -> USB mux -> _core

  // Split out for differential PHY testing

  // Outputs always drive and just copy the value
  // Let them go to the normal place too because it won't do any harm
  // and it simplifies the changes needed

  // The output enable for IO_USB_DNPULLUP0 is used to decide whether we need to undo the swapping.
  logic undo_swap;
  assign undo_swap = dio_oe[DioUsbdevDnPullup];

  // GPIO[2] = Switch 2 on board is used to select using the UPHY
  // Keep GPIO[1] for selecting differential in sw
  logic use_uphy;
  assign use_uphy = mio_in[MioPadIoa2];

  // DioUsbdevDn
  assign manual_attr_usb_n = '0;
  assign manual_attr_io_uphy_dn_tx = '0;

  assign manual_out_io_uphy_dn_tx = manual_out_usb_n;
  assign manual_out_usb_n = undo_swap ? dio_out[DioUsbdevDp] :
                                        dio_out[DioUsbdevDn];

  assign manual_oe_io_uphy_dn_tx = manual_oe_usb_n;
  assign manual_oe_usb_n = undo_swap ? dio_oe[DioUsbdevDp] :
                                       dio_oe[DioUsbdevDn];

  assign dio_in[DioUsbdevDn] = use_uphy ?
                               (undo_swap ? manual_in_io_uphy_dp_rx :
                                            manual_in_io_uphy_dn_rx) :
                               (undo_swap ? manual_in_usb_p :
                                            manual_in_usb_n);
  // DioUsbdevDp
  assign manual_attr_usb_p = '0;
  assign manual_attr_io_uphy_dp_tx = '0;

  assign manual_out_io_uphy_dp_tx = manual_out_usb_p;
  assign manual_out_usb_p = undo_swap ? dio_out[DioUsbdevDn] :
                                       dio_out[DioUsbdevDp];

  assign manual_oe_io_uphy_dp_tx = manual_oe_usb_p;
  assign manual_oe_usb_p = undo_swap ? dio_oe[DioUsbdevDn] :
                                       dio_oe[DioUsbdevDp];
  assign dio_in[DioUsbdevDp] = use_uphy ?
                               (undo_swap ? manual_in_io_uphy_dn_rx :
                                            manual_in_io_uphy_dp_rx) :
                               (undo_swap ? manual_in_usb_n :
                                            manual_in_usb_p);
  // DioUsbdevD
  // This is not connected at the moment
  logic unused_out_usb_d;
  assign unused_out_usb_d = dio_out[DioUsbdevD] ^
                            dio_oe[DioUsbdevD];
  assign dio_in[DioUsbdevD] = use_uphy ?
                              (undo_swap ? ~manual_in_io_uphy_d_rx :
                                            manual_in_io_uphy_d_rx) :
                              // This is not connected at the moment
                              (undo_swap ? 1'b1 : 1'b0);
  assign manual_out_io_uphy_d_rx = 1'b0;
  assign manual_oe_io_uphy_d_rx = 1'b0;

  // DioUsbdevDnPullup
  assign manual_attr_io_usb_dnpullup0 = '0;
  assign manual_out_io_usb_dnpullup0 = undo_swap ? dio_out[DioUsbdevDpPullup] :
                                                   dio_out[DioUsbdevDnPullup];
  assign manual_oe_io_usb_dnpullup0 = undo_swap ? dio_oe[DioUsbdevDpPullup] :
                                                  dio_oe[DioUsbdevDnPullup];
  assign dio_in[DioUsbdevDnPullup] = manual_in_io_usb_dnpullup0;

  // DioUsbdevDpPullup
  assign manual_attr_io_usb_dppullup0 = '0;
  assign manual_out_io_usb_dppullup0 = undo_swap ? dio_out[DioUsbdevDnPullup] :
                                                   dio_out[DioUsbdevDpPullup];
  assign manual_oe_io_usb_dppullup0 = undo_swap ? dio_oe[DioUsbdevDnPullup] :
                                                  dio_oe[DioUsbdevDpPullup];
  assign dio_in[DioUsbdevDpPullup] = manual_in_io_usb_dppullup0;

  // DioUsbdevSense
  assign manual_out_io_usb_sense0 = dio_out[DioUsbdevSense];
  assign manual_oe_io_usb_sense0  = dio_oe[DioUsbdevSense];
  assign dio_in[DioUsbdevSense] = use_uphy ? manual_in_io_uphy_sense :
                                             manual_in_io_usb_sense0;
  assign manual_out_io_uphy_sense = 1'b0;
  assign manual_oe_io_uphy_sense = 1'b0;

  // DioUsbdevRxEnable
  assign dio_in[DioUsbdevRxEnable] = 1'b0;

  // Additional outputs for uphy
  assign manual_oe_io_uphy_dppullup = 1'b1;
  assign manual_out_io_uphy_dppullup = manual_out_io_usb_dppullup0 &
                                       manual_oe_io_usb_dppullup0;

  logic unused_in_io_uphy_dppullup;
  assign unused_in_io_uphy_dppullup = manual_in_io_uphy_dppullup;

  assign manual_oe_io_uphy_oe_n = 1'b1;
  assign manual_out_io_uphy_oe_n = ~manual_oe_usb_p;

  logic unused_in_io_uphy_oe_n;
  assign unused_in_io_uphy_oe_n = manual_in_io_uphy_oe_n;



  //////////////////
  // PLL for FPGA //
  //////////////////

  assign manual_out_io_clk = 1'b0;
  assign manual_oe_io_clk = 1'b0;
  assign manual_out_por_n = 1'b0;
  assign manual_oe_por_n = 1'b0;
  assign manual_out_io_jsrst_n = 1'b0;
  assign manual_oe_io_jsrst_n = 1'b0;

  logic clk_main, clk_usb_48mhz, clk_aon, rst_n;
  clkgen_xil7series # (
    .AddClkBuf(0)
  ) clkgen (
    .clk_i(manual_in_io_clk),
    .rst_ni(manual_in_por_n),
    .jtag_srst_ni(manual_in_io_jsrst_n),
    .clk_main_o(clk_main),
    .clk_48MHz_o(clk_usb_48mhz),
    .clk_aon_o(clk_aon),
    .rst_no(rst_n)
  );

  //////////////////////
  // Top-level design //
  //////////////////////
  pwrmgr_pkg::pwr_ast_rsp_t ast_base_pwr;
  ast_pkg::ast_alert_req_t ast_base_alerts;
  ast_pkg::ast_status_t ast_base_status;

  assign ast_base_pwr.slow_clk_val = 1'b1;
  assign ast_base_pwr.core_clk_val = 1'b1;
  assign ast_base_pwr.io_clk_val   = 1'b1;
  assign ast_base_pwr.usb_clk_val  = 1'b1;
  assign ast_base_pwr.main_pok     = 1'b1;

  ast_pkg::ast_dif_t silent_alert = '{
                                       p: 1'b0,
                                       n: 1'b1
                                     };

  assign ast_base_alerts.alerts = {ast_pkg::NumAlerts{silent_alert}};
  assign ast_base_status.io_pok = {ast_pkg::NumIoRails{1'b1}};

  // the rst_ni pin only goes to AST
  // the rest of the logic generates reset based on the 'pok' signal.
  // for verilator purposes, make these two the same.
  lc_ctrl_pkg::lc_tx_t lc_clk_bypass;

// TODO: align this with ASIC version to minimize the duplication.
// Also need to add AST simulation and FPGA emulation models for things like entropy source -
// otherwise Verilator / FPGA will hang.
  top_earlgrey #(
    .AesMasking(1'b0),
    .AesSBoxImpl(aes_pkg::SBoxImplLut),
    .KmacEnMasking(1'b0),
    .KeymgrKmacEnMasking(0),
    .SecAesStartTriggerDelay(0),
    .SecAesAllowForcingMasks(1'b0),
    .SecAesSkipPRNGReseeding(1'b0),
    .EntropySrcStub(1'b1),
    .CsrngSBoxImpl(aes_pkg::SBoxImplLut),
    .OtbnRegFile(otbn_pkg::RegFileFPGA),
    .OtbnStub(1'b1),
    .OtpCtrlMemInitFile(OtpCtrlMemInitFile),
    .RomCtrlBootRomInitFile(BootRomInitFile),
    .RvCoreIbexRegFile(ibex_pkg::RegFileFPGA),
    .RvCoreIbexPipeLine(1),
    .RvCoreIbexSecureIbex(0),
    .SramCtrlRetAonInstrExec(0),
    .SramCtrlMainInstrExec(1),
    .PinmuxAonTargetCfg(PinmuxTargetCfg)
  ) top_earlgrey (
    .por_n_i                      ( {rst_n, rst_n}   ),
    .clk_main_i                   ( clk_main         ),
    .clk_io_i                     ( clk_main         ),
    .clk_usb_i                    ( clk_usb_48mhz    ),
    .clk_aon_i                    ( clk_aon          ),
    .clks_ast_o                   (                  ),
    .clk_main_jitter_en_o         (                  ),
    .rsts_ast_o                   (                  ),
    .pwrmgr_ast_req_o             (                  ),
    .pwrmgr_ast_rsp_i             ( ast_base_pwr     ),
    .usbdev_usb_ref_val_o         (                  ),
    .usbdev_usb_ref_pulse_o       (                  ),
    .ast_edn_req_i                ( '0               ),
    .ast_edn_rsp_o                (                  ),
    .flash_bist_enable_i          ( lc_ctrl_pkg::Off ),
    .flash_power_down_h_i         ( 1'b0             ),
    .flash_power_ready_h_i        ( 1'b1             ),
    .ast_clk_byp_req_o            ( lc_clk_bypass    ),
    .ast_clk_byp_ack_i            ( lc_clk_bypass    ),

    .ast_tl_req_o                 (                  ),
    .ast_tl_rsp_i                 ( '0               ),
    .otp_ctrl_otp_ast_pwr_seq_o   (                  ),
    .otp_ctrl_otp_ast_pwr_seq_h_i ( '0               ),
    .otp_alert_o                  (                  ),
    .sensor_ctrl_ast_alert_req_i  ( ast_base_alerts  ),
    .sensor_ctrl_ast_alert_rsp_o  (                  ),
    .sensor_ctrl_ast_status_i     ( ast_base_status  ),
    .es_rng_req_o                 (                  ),
    .es_rng_rsp_i                 ( '0               ),
    .es_rng_fips_o                (                  ),
    .ast2pinmux_i                 ( '0               ),

    // Multiplexed I/O
    .mio_in_i        ( mio_in   ),
    .mio_out_o       ( mio_out  ),
    .mio_oe_o        ( mio_oe   ),

    // Dedicated I/O
    .dio_in_i        ( dio_in   ),
    .dio_out_o       ( dio_out  ),
    .dio_oe_o        ( dio_oe   ),

    // Pad attributes
    .mio_attr_o      ( mio_attr      ),
    .dio_attr_o      ( dio_attr      ),

    // Memory attributes
    .ram_1p_cfg_i    ( '0 ),
    .ram_2p_cfg_i    ( '0 ),
    .rom_cfg_i       ( '0 ),

    // DFT signals
    .dft_hold_tap_sel_i ( '0               ),
    .scan_rst_ni        ( 1'b1             ),
    .scan_en_i          ( 1'b0             ),
    .scanmode_i         ( lc_ctrl_pkg::Off )
  );


endmodule : chip_earlgrey_nexysvideo
