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
  parameter BootRomInitFile = "test_rom_fpga_nexysvideo.32.vmem",
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
  inout IO_USB_DNPULLUP0, // Manual Pad
  inout IO_USB_DPPULLUP0, // Manual Pad
  inout IO_UPHY_DP_TX, // Manual Pad
  inout IO_UPHY_DN_TX, // Manual Pad
  inout IO_UPHY_DP_RX, // Manual Pad
  inout IO_UPHY_DN_RX, // Manual Pad
  inout IO_UPHY_D_RX, // Manual Pad
  inout IO_UPHY_OE_N, // Manual Pad
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
  inout IOC11, // MIO Pad 33
  inout IOR0, // MIO Pad 35
  inout IOR1  // MIO Pad 36
);

  import top_earlgrey_pkg::*;
  import prim_pad_wrapper_pkg::*;

  ////////////////////////////
  // Special Signal Indices //
  ////////////////////////////

  localparam int Tap0PadIdx = 22;
  localparam int Tap1PadIdx = 16;
  localparam int Dft0PadIdx = 23;
  localparam int Dft1PadIdx = 34;
  localparam int TckPadIdx = 59;
  localparam int TmsPadIdx = 60;
  localparam int TrstNPadIdx = 18;
  localparam int TdiPadIdx = 53;
  localparam int TdoPadIdx = 54;

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
      BidirOd, // DIO sysrst_ctrl_aon_flash_wp_l
      BidirOd, // DIO sysrst_ctrl_aon_ec_rst_l
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
  logic manual_in_io_usb_dnpullup0, manual_out_io_usb_dnpullup0, manual_oe_io_usb_dnpullup0;
  logic manual_in_io_usb_dppullup0, manual_out_io_usb_dppullup0, manual_oe_io_usb_dppullup0;
  logic manual_in_io_uphy_dp_tx, manual_out_io_uphy_dp_tx, manual_oe_io_uphy_dp_tx;
  logic manual_in_io_uphy_dn_tx, manual_out_io_uphy_dn_tx, manual_oe_io_uphy_dn_tx;
  logic manual_in_io_uphy_dp_rx, manual_out_io_uphy_dp_rx, manual_oe_io_uphy_dp_rx;
  logic manual_in_io_uphy_dn_rx, manual_out_io_uphy_dn_rx, manual_oe_io_uphy_dn_rx;
  logic manual_in_io_uphy_d_rx, manual_out_io_uphy_d_rx, manual_oe_io_uphy_d_rx;
  logic manual_in_io_uphy_oe_n, manual_out_io_uphy_oe_n, manual_oe_io_uphy_oe_n;
  logic manual_in_io_uphy_dppullup, manual_out_io_uphy_dppullup, manual_oe_io_uphy_dppullup;

  pad_attr_t manual_attr_por_n;
  pad_attr_t manual_attr_usb_p;
  pad_attr_t manual_attr_usb_n;
  pad_attr_t manual_attr_io_clk;
  pad_attr_t manual_attr_io_jsrst_n;
  pad_attr_t manual_attr_io_usb_dnpullup0;
  pad_attr_t manual_attr_io_usb_dppullup0;
  pad_attr_t manual_attr_io_uphy_dp_tx;
  pad_attr_t manual_attr_io_uphy_dn_tx;
  pad_attr_t manual_attr_io_uphy_dp_rx;
  pad_attr_t manual_attr_io_uphy_dn_rx;
  pad_attr_t manual_attr_io_uphy_d_rx;
  pad_attr_t manual_attr_io_uphy_oe_n;
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

  ast_pkg::ast_clks_t ast_base_clks;


  padring #(
    // Padring specific counts may differ from pinmux config due
    // to custom, stubbed or added pads.
    .NDioPads(18),
    .NMioPads(31),
    .DioPadType ({
      BidirStd, // IO_UPHY_DPPULLUP
      BidirStd, // IO_UPHY_OE_N
      BidirStd, // IO_UPHY_D_RX
      BidirStd, // IO_UPHY_DN_RX
      BidirStd, // IO_UPHY_DP_RX
      BidirStd, // IO_UPHY_DN_TX
      BidirStd, // IO_UPHY_DP_TX
      BidirStd, // IO_USB_DPPULLUP0
      BidirStd, // IO_USB_DNPULLUP0
      InputStd, // IO_JSRST_N
      InputStd, // IO_CLK
      InputStd, // SPI_DEV_CS_L
      InputStd, // SPI_DEV_CLK
      BidirStd, // SPI_DEV_D1
      BidirStd, // SPI_DEV_D0
      DualBidirTol, // USB_N
      DualBidirTol, // USB_P
      InputStd  // POR_N
    }),
    .MioPadType ({
      BidirStd, // IOR1
      BidirStd, // IOR0
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
    .scanmode_i   ( prim_mubi_pkg::MuBi4False ),
    .dio_in_raw_o ( ),
    // Chip IOs
    .dio_pad_io ({
      IO_UPHY_DPPULLUP,
      IO_UPHY_OE_N,
      IO_UPHY_D_RX,
      IO_UPHY_DN_RX,
      IO_UPHY_DP_RX,
      IO_UPHY_DN_TX,
      IO_UPHY_DP_TX,
      IO_USB_DPPULLUP0,
      IO_USB_DNPULLUP0,
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
      IOR1,
      IOR0,
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
        manual_in_io_uphy_oe_n,
        manual_in_io_uphy_d_rx,
        manual_in_io_uphy_dn_rx,
        manual_in_io_uphy_dp_rx,
        manual_in_io_uphy_dn_tx,
        manual_in_io_uphy_dp_tx,
        manual_in_io_usb_dppullup0,
        manual_in_io_usb_dnpullup0,
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
        manual_out_io_uphy_oe_n,
        manual_out_io_uphy_d_rx,
        manual_out_io_uphy_dn_rx,
        manual_out_io_uphy_dp_rx,
        manual_out_io_uphy_dn_tx,
        manual_out_io_uphy_dp_tx,
        manual_out_io_usb_dppullup0,
        manual_out_io_usb_dnpullup0,
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
        manual_oe_io_uphy_oe_n,
        manual_oe_io_uphy_d_rx,
        manual_oe_io_uphy_dn_rx,
        manual_oe_io_uphy_dp_rx,
        manual_oe_io_uphy_dn_tx,
        manual_oe_io_uphy_dp_tx,
        manual_oe_io_usb_dppullup0,
        manual_oe_io_usb_dnpullup0,
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
        manual_attr_io_uphy_oe_n,
        manual_attr_io_uphy_d_rx,
        manual_attr_io_uphy_dn_rx,
        manual_attr_io_uphy_dp_rx,
        manual_attr_io_uphy_dn_tx,
        manual_attr_io_uphy_dp_tx,
        manual_attr_io_usb_dppullup0,
        manual_attr_io_usb_dnpullup0,
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
        mio_in[36:35],
        mio_in[33:24],
        mio_in[18:0]
      }),
    .mio_out_i ({
        mio_out[36:35],
        mio_out[33:24],
        mio_out[18:0]
      }),
    .mio_oe_i ({
        mio_oe[36:35],
        mio_oe[33:24],
        mio_oe[18:0]
      }),
    .mio_attr_i ({
        mio_attr[36:35],
        mio_attr[33:24],
        mio_attr[18:0]
      }),
    .mio_in_raw_o ({
        mio_in_raw[36:35],
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
  logic usb_dp_pullup_en;
  logic usb_dn_pullup_en;
  logic usb_rx_d;
  logic usb_tx_d;
  logic usb_tx_se0;
  logic usb_tx_use_d_se0;
  logic usb_suspend;
  logic usb_rx_enable;

  // The value for IO_USB_DNPULLUP0 is used to decide whether we need to undo the swapping.
  logic undo_swap;
  assign undo_swap = usb_dn_pullup_en;

  // GPIO[2] = Switch 2 on board is used to select using the UPHY
  // Keep GPIO[1] for selecting differential in sw
  logic use_uphy;
  assign use_uphy = mio_in[MioPadIoa2];

  // DioUsbdevUsbDn
  assign manual_attr_usb_n = '0;
  assign manual_attr_io_uphy_dn_tx = '0;

  assign manual_out_io_uphy_dn_tx = manual_out_usb_n;
  assign manual_out_usb_n = undo_swap ? dio_out[DioUsbdevUsbDp] :
                                        dio_out[DioUsbdevUsbDn];

  assign manual_oe_io_uphy_dn_tx = manual_oe_usb_n;
  assign manual_oe_usb_n = undo_swap ? dio_oe[DioUsbdevUsbDp] :
                                       dio_oe[DioUsbdevUsbDn];

  assign dio_in[DioUsbdevUsbDn] = use_uphy ?
                                  (undo_swap ? manual_in_io_uphy_dp_rx :
                                               manual_in_io_uphy_dn_rx) :
                                  (undo_swap ? manual_in_usb_p :
                                               manual_in_usb_n);
  // DioUsbdevUsbDp
  assign manual_attr_usb_p = '0;
  assign manual_attr_io_uphy_dp_tx = '0;

  assign manual_out_io_uphy_dp_tx = manual_out_usb_p;
  assign manual_out_usb_p = undo_swap ? dio_out[DioUsbdevUsbDn] :
                                        dio_out[DioUsbdevUsbDp];

  assign manual_oe_io_uphy_dp_tx = manual_oe_usb_p;
  assign manual_oe_usb_p = undo_swap ? dio_oe[DioUsbdevUsbDn] :
                                       dio_oe[DioUsbdevUsbDp];
  assign dio_in[DioUsbdevUsbDp] = use_uphy ?
                                  (undo_swap ? manual_in_io_uphy_dn_rx :
                                               manual_in_io_uphy_dp_rx) :
                                  (undo_swap ? manual_in_usb_n :
                                               manual_in_usb_p);
  // UsbdevD
  // This is not connected at the moment
  logic unused_out_usb_d;
  assign unused_out_usb_d = usb_tx_d;
  assign usb_rx_d = use_uphy ?
                              (undo_swap ? ~manual_in_io_uphy_d_rx :
                                            manual_in_io_uphy_d_rx) :
                              // This is not connected at the moment
                              (undo_swap ? 1'b1 : 1'b0);
  assign manual_out_io_uphy_d_rx = 1'b0;
  assign manual_oe_io_uphy_d_rx = 1'b0;

  // UsbdevDnPullup
  assign manual_attr_io_usb_dnpullup0 = '0;
  assign manual_out_io_usb_dnpullup0 = usb_dn_pullup_en;
  assign manual_oe_io_usb_dnpullup0 = undo_swap ? usb_dp_pullup_en : usb_dn_pullup_en;

  // DioUsbdevDpPullup
  assign manual_attr_io_usb_dppullup0 = '0;
  assign manual_out_io_usb_dppullup0 = usb_dp_pullup_en;
  assign manual_oe_io_usb_dppullup0 = undo_swap ? usb_dn_pullup_en : usb_dp_pullup_en;

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



  //////////////////////////////////
  // AST - Common for all targets //
  //////////////////////////////////

  // pwrmgr interface
  pwrmgr_pkg::pwr_ast_req_t base_ast_pwr;
  pwrmgr_pkg::pwr_ast_rsp_t ast_base_pwr;

  // assorted ast status
  ast_pkg::ast_pwst_t ast_pwst;
  ast_pkg::ast_pwst_t ast_pwst_h;

  // TLUL interface
  tlul_pkg::tl_h2d_t base_ast_bus;
  tlul_pkg::tl_d2h_t ast_base_bus;

  // synchronization clocks / rests
  clkmgr_pkg::clkmgr_out_t clkmgr_aon_clocks;
  rstmgr_pkg::rstmgr_out_t rstmgr_aon_resets;

  // external clock
  logic ext_clk;

  // monitored clock
  logic sck_monitor;

  // observe interface
  logic [7:0] fla_obs;
  logic [7:0] otp_obs;
  ast_pkg::ast_obs_ctrl_t obs_ctrl;

  // otp power sequence
  otp_ctrl_pkg::otp_ast_req_t otp_ctrl_otp_ast_pwr_seq;
  otp_ctrl_pkg::otp_ast_rsp_t otp_ctrl_otp_ast_pwr_seq_h;

  logic usb_ref_pulse;
  logic usb_ref_val;

  // adc
  ast_pkg::adc_ast_req_t adc_req;
  ast_pkg::adc_ast_rsp_t adc_rsp;

  // entropy source interface
  // The entropy source pacakge definition should eventually be moved to es
  entropy_src_pkg::entropy_src_rng_req_t es_rng_req;
  entropy_src_pkg::entropy_src_rng_rsp_t es_rng_rsp;
  logic es_rng_fips;

  // entropy distribution network
  edn_pkg::edn_req_t ast_edn_edn_req;
  edn_pkg::edn_rsp_t ast_edn_edn_rsp;

  // alerts interface
  ast_pkg::ast_alert_rsp_t ast_alert_rsp;
  ast_pkg::ast_alert_req_t ast_alert_req;

  // Flash connections
  prim_mubi_pkg::mubi4_t flash_bist_enable;
  logic flash_power_down_h;
  logic flash_power_ready_h;

  // clock bypass req/ack
  prim_mubi_pkg::mubi4_t io_clk_byp_req;
  prim_mubi_pkg::mubi4_t io_clk_byp_ack;
  prim_mubi_pkg::mubi4_t all_clk_byp_req;
  prim_mubi_pkg::mubi4_t all_clk_byp_ack;
  prim_mubi_pkg::mubi4_t hi_speed_sel;
  prim_mubi_pkg::mubi4_t div_step_down_req;

  // DFT connections
  logic scan_en;
  lc_ctrl_pkg::lc_tx_t dft_en;
  pinmux_pkg::dft_strap_test_req_t dft_strap_test;

  // Debug connections
  logic [ast_pkg::Ast2PadOutWidth-1:0] ast2pinmux;
  logic [ast_pkg::Pad2AstInWidth-1:0] pad2ast;

  // Jitter enable
  prim_mubi_pkg::mubi4_t jen;

  // reset domain connections
  import rstmgr_pkg::PowerDomains;
  import rstmgr_pkg::DomainAonSel;
  import rstmgr_pkg::Domain0Sel;

  // Memory configuration connections
  ast_pkg::spm_rm_t ast_ram_1p_cfg;
  ast_pkg::spm_rm_t ast_rf_cfg;
  ast_pkg::spm_rm_t ast_rom_cfg;
  ast_pkg::dpm_rm_t ast_ram_2p_fcfg;
  ast_pkg::dpm_rm_t ast_ram_2p_lcfg;

  prim_ram_1p_pkg::ram_1p_cfg_t ram_1p_cfg;
  prim_ram_2p_pkg::ram_2p_cfg_t ram_2p_cfg;
  prim_rom_pkg::rom_cfg_t rom_cfg;

  // conversion from ast structure to memory centric structures
  assign ram_1p_cfg = '{
    ram_cfg: '{
                cfg_en: ast_ram_1p_cfg.marg_en,
                cfg:    ast_ram_1p_cfg.marg
              },
    rf_cfg:  '{
                cfg_en: ast_rf_cfg.marg_en,
                cfg:    ast_rf_cfg.marg
              }
  };

  assign ram_2p_cfg = '{
    a_ram_fcfg: '{
                   cfg_en: ast_ram_2p_fcfg.marg_en_a,
                   cfg:    ast_ram_2p_fcfg.marg_a
                 },
    a_ram_lcfg: '{
                   cfg_en: ast_ram_2p_lcfg.marg_en_a,
                   cfg:    ast_ram_2p_lcfg.marg_a
                 },
    b_ram_fcfg: '{
                   cfg_en: ast_ram_2p_fcfg.marg_en_b,
                   cfg:    ast_ram_2p_fcfg.marg_b
                 },
    b_ram_lcfg: '{
                   cfg_en: ast_ram_2p_lcfg.marg_en_b,
                   cfg:    ast_ram_2p_lcfg.marg_b
                 }
  };

  assign rom_cfg = '{
    cfg_en: ast_rom_cfg.marg_en,
    cfg: ast_rom_cfg.marg
  };


  //////////////////////////////////
  // AST - Custom for targets     //
  //////////////////////////////////


  // TODO: Hook this up when FPGA pads are updated
  assign ext_clk = '0;
  assign pad2ast = '0;

  assign ast_base_pwr.main_pok = base_ast_pwr.main_pd_n;

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

  logic [31:0] fpga_info;
  usr_access_xil7series u_info (
    .info_o(fpga_info)
  );

  ast_pkg::clks_osc_byp_t clks_osc_byp;
  assign clks_osc_byp = '{
    usb: clk_usb_48mhz,
    sys: clk_main,
    io:  clk_main,
    aon: clk_aon
  };


  ast #(
    .EntropyStreams(ast_pkg::EntropyStreams),
    .AdcChannels(ast_pkg::AdcChannels),
    .AdcDataWidth(ast_pkg::AdcDataWidth),
    .UsbCalibWidth(ast_pkg::UsbCalibWidth),
    .Ast2PadOutWidth(ast_pkg::Ast2PadOutWidth),
    .Pad2AstInWidth(ast_pkg::Pad2AstInWidth)
  ) u_ast (
    // external POR
    .por_ni                ( rst_n ),

    // USB IO Pull-up Calibration Setting
    .usb_io_pu_cal_o       ( ),

    // clocks' oschillator bypass for FPGA
    .clk_osc_byp_i         ( clks_osc_byp ),

    // adc
    .adc_a0_ai             ( '0 ),
    .adc_a1_ai             ( '0 ),

    // Direct short to PAD
    .ast2pad_t0_ao         (  ),
    .ast2pad_t1_ao         (  ),

    // clocks and resets supplied for detection
    .sns_clks_i            ( clkmgr_aon_clocks    ),
    .sns_rsts_i            ( rstmgr_aon_resets    ),
    .sns_spi_ext_clk_i     ( sck_monitor          ),
    // tlul
    .tl_i                  ( base_ast_bus ),
    .tl_o                  ( ast_base_bus ),
    // init done indication
    .ast_init_done_o       ( ast_init_done ),
    // buffered clocks & resets
    .clk_ast_tlul_i (clkmgr_aon_clocks.clk_io_div4_secure),
    .clk_ast_adc_i (clkmgr_aon_clocks.clk_aon_secure),
    .clk_ast_alert_i (clkmgr_aon_clocks.clk_io_div4_secure),
    .clk_ast_es_i (clkmgr_aon_clocks.clk_main_secure),
    .clk_ast_rng_i (clkmgr_aon_clocks.clk_main_secure),
    .clk_ast_usb_i (clkmgr_aon_clocks.clk_usb_secure),
    .rst_ast_tlul_ni (rstmgr_aon_resets.rst_lc_io_div4_n[rstmgr_pkg::Domain0Sel]),
    .rst_ast_adc_ni (rstmgr_aon_resets.rst_sys_aon_n[rstmgr_pkg::DomainAonSel]),
    .rst_ast_alert_ni (rstmgr_aon_resets.rst_lc_io_div4_n[rstmgr_pkg::Domain0Sel]),
    .rst_ast_es_ni (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel]),
    .rst_ast_rng_ni (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel]),
    .rst_ast_usb_ni (rstmgr_aon_resets.rst_usbif_n[rstmgr_pkg::Domain0Sel]),
    .clk_ast_ext_i         ( ext_clk ),

    // pok test for FPGA
    .vcc_supp_i            ( 1'b1 ),
    .vcaon_supp_i          ( 1'b1 ),
    .vcmain_supp_i         ( 1'b1 ),
    .vioa_supp_i           ( 1'b1 ),
    .viob_supp_i           ( 1'b1 ),
    // pok
    .ast_pwst_o            ( ast_pwst ),
    .ast_pwst_h_o          ( ast_pwst_h ),
    // main regulator
    .main_env_iso_en_i     ( base_ast_pwr.pwr_clamp_env ),
    .main_pd_ni            ( base_ast_pwr.main_pd_n ),
    // pdm control (flash)/otp
    .flash_power_down_h_o  ( flash_power_down_h ),
    .flash_power_ready_h_o ( flash_power_ready_h ),
    .otp_power_seq_i       ( otp_ctrl_otp_ast_pwr_seq ),
    .otp_power_seq_h_o     ( otp_ctrl_otp_ast_pwr_seq_h ),
    // system source clock
    .clk_src_sys_en_i      ( base_ast_pwr.core_clk_en ),
    // need to add function in clkmgr
    .clk_src_sys_jen_i     ( jen ),
    .clk_src_sys_o         ( ast_base_clks.clk_sys  ),
    .clk_src_sys_val_o     ( ast_base_pwr.core_clk_val ),
    // aon source clock
    .clk_src_aon_o         ( ast_base_clks.clk_aon ),
    .clk_src_aon_val_o     ( ast_base_pwr.slow_clk_val ),
    // io source clock
    .clk_src_io_en_i       ( base_ast_pwr.io_clk_en ),
    .clk_src_io_o          ( ast_base_clks.clk_io ),
    .clk_src_io_val_o      ( ast_base_pwr.io_clk_val ),
    .clk_src_io_48m_o      ( div_step_down_req ),
    // usb source clock
    .usb_ref_pulse_i       ( usb_ref_pulse ),
    .usb_ref_val_i         ( usb_ref_val ),
    .clk_src_usb_en_i      ( base_ast_pwr.usb_clk_en ),
    .clk_src_usb_o         ( ast_base_clks.clk_usb ),
    .clk_src_usb_val_o     ( ast_base_pwr.usb_clk_val ),
    // adc
    .adc_pd_i              ( adc_req.pd ),
    .adc_chnsel_i          ( adc_req.channel_sel ),
    .adc_d_o               ( adc_rsp.data ),
    .adc_d_val_o           ( adc_rsp.data_valid ),
    // rng
    .rng_en_i              ( es_rng_req.rng_enable ),
    .rng_fips_i            ( es_rng_fips ),
    .rng_val_o             ( es_rng_rsp.rng_valid ),
    .rng_b_o               ( es_rng_rsp.rng_b ),
    // entropy
    .entropy_rsp_i         ( ast_edn_edn_rsp ),
    .entropy_req_o         ( ast_edn_edn_req ),
    // alerts
    .fla_alert_src_i       ( flash_alert    ),
    .otp_alert_src_i       ( otp_alert      ),
    .alert_rsp_i           ( ast_alert_rsp  ),
    .alert_req_o           ( ast_alert_req  ),
    // dft
    .dft_strap_test_i      ( dft_strap_test   ),
    .lc_dft_en_i           ( dft_en           ),
    .fla_obs_i             ( fla_obs ),
    .otp_obs_i             ( otp_obs ),
    .otm_obs_i             ( '0 ),
    .usb_obs_i             ( usb_diff_rx_obs ),
    .obs_ctrl_o            ( obs_ctrl ),
    // pinmux related
    .padmux2ast_i          ( pad2ast    ),
    .ast2padmux_o          ( ast2pinmux ),
    .ext_freq_is_96m_i     ( hi_speed_sel ),
    .all_clk_byp_req_i     ( all_clk_byp_req  ),
    .all_clk_byp_ack_o     ( all_clk_byp_ack  ),
    .io_clk_byp_req_i      ( io_clk_byp_req   ),
    .io_clk_byp_ack_o      ( io_clk_byp_ack   ),
    .flash_bist_en_o       ( flash_bist_enable ),
    // Memory configuration connections
    .dpram_rmf_o           ( ast_ram_2p_fcfg ),
    .dpram_rml_o           ( ast_ram_2p_lcfg ),
    .spram_rm_o            ( ast_ram_1p_cfg  ),
    .sprgf_rm_o            ( ast_rf_cfg      ),
    .sprom_rm_o            ( ast_rom_cfg     ),
    // scan
    .dft_scan_md_o         ( scanmode ),
    .scan_shift_en_o       ( scan_en ),
    .scan_reset_no         ( scan_rst_n )
  );




  //////////////////
  // PLL for FPGA //
  //////////////////

  assign manual_out_io_clk = 1'b0;
  assign manual_oe_io_clk = 1'b0;
  assign manual_out_por_n = 1'b0;
  assign manual_oe_por_n = 1'b0;
  assign manual_out_io_jsrst_n = 1'b0;
  assign manual_oe_io_jsrst_n = 1'b0;


  //////////////////////
  // Top-level design //
  //////////////////////

  // the rst_ni pin only goes to AST
  // the rest of the logic generates reset based on the 'pok' signal.
  // for verilator purposes, make these two the same.
  prim_mubi_pkg::mubi4_t lc_clk_bypass;   // TODO Tim

// TODO: align this with ASIC version to minimize the duplication.
// Also need to add AST simulation and FPGA emulation models for things like entropy source -
// otherwise Verilator / FPGA will hang.
  top_earlgrey #(
    .SecAesMasking(1'b0),
    .SecAesSBoxImpl(aes_pkg::SBoxImplLut),
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
    .por_n_i                      ( {rst_n, rst_n}        ),
    .clk_main_i                   ( ast_base_clks.clk_sys ),
    .clk_io_i                     ( ast_base_clks.clk_io  ),
    .clk_usb_i                    ( ast_base_clks.clk_usb ),
    .clk_aon_i                    ( ast_base_clks.clk_aon ),
    .clks_ast_o                   ( clkmgr_aon_clocks     ),
    .clk_main_jitter_en_o         ( jen                   ),
    .rsts_ast_o                   ( rstmgr_aon_resets     ),
    .sck_monitor_o                ( sck_monitor           ),
    .pwrmgr_ast_req_o             ( base_ast_pwr          ),
    .pwrmgr_ast_rsp_i             ( ast_base_pwr          ),
    .usb_dp_pullup_en_o           ( usb_dp_pullup_en      ),
    .usb_dn_pullup_en_o           ( usb_dn_pullup_en      ),
    .usbdev_usb_rx_d_i            ( usb_rx_d              ),
    .usbdev_usb_tx_d_o            ( usb_tx_d              ),
    .usbdev_usb_tx_se0_o          ( usb_tx_se0            ),
    .usbdev_usb_tx_use_d_se0_o    ( usb_tx_use_d_se0      ),
    .usbdev_usb_suspend_o         ( usb_suspend           ),
    .usbdev_usb_rx_enable_o       ( usb_rx_enable         ),
    .usbdev_usb_ref_val_o         ( usb_ref_val           ),
    .usbdev_usb_ref_pulse_o       ( usb_ref_pulse         ),
    .ast_edn_req_i                ( ast_edn_edn_req       ),
    .ast_edn_rsp_o                ( ast_edn_edn_rsp       ),
    .obs_ctrl_i                   ( obs_ctrl              ),
    .flash_bist_enable_i          ( flash_bist_enable     ),
    .flash_power_down_h_i         ( 1'b0                  ),
    .flash_power_ready_h_i        ( 1'b1                  ),
    .flash_obs_o                  ( flash_obs             ),
    .io_clk_byp_req_o             ( io_clk_byp_req        ),
    .io_clk_byp_ack_i             ( io_clk_byp_ack        ),
    .all_clk_byp_req_o            ( all_clk_byp_req       ),
    .all_clk_byp_ack_i            ( all_clk_byp_ack       ),
    .hi_speed_sel_o               ( hi_speed_sel          ),
    .div_step_down_req_i          ( div_step_down_req     ),
    .fpga_info_i                  ( fpga_info             ),
    .ast_tl_req_o                 ( base_ast_bus               ),
    .ast_tl_rsp_i                 ( ast_base_bus               ),
    .adc_req_o                    ( adc_req                    ),
    .adc_rsp_i                    ( adc_rsp                    ),
    .otp_ctrl_otp_ast_pwr_seq_o   ( otp_ctrl_otp_ast_pwr_seq   ),
    .otp_ctrl_otp_ast_pwr_seq_h_i ( otp_ctrl_otp_ast_pwr_seq_h ),
    .otp_alert_o                  ( otp_alert                  ),
    .otp_obs_o                    ( otp_obs                    ),
    .sensor_ctrl_ast_alert_req_i  ( ast_alert_req              ),
    .sensor_ctrl_ast_alert_rsp_o  ( ast_alert_rsp              ),
    .sensor_ctrl_ast_status_i     ( ast_pwst.io_pok            ),
    .es_rng_req_o                 ( es_rng_req                 ),
    .es_rng_rsp_i                 ( es_rng_rsp                 ),
    .es_rng_fips_o                ( es_rng_fips                ),
    .ast2pinmux_i                 ( ast2pinmux                 ),
    .ast_init_done_i              ( ast_init_done              ),

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
    .scanmode_i         ( prim_mubi_pkg::MuBi4False )
  );


endmodule : chip_earlgrey_nexysvideo
