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

module chip_earlgrey_asic (
  // Dedicated Pads
  inout POR_N, // Manual Pad
  inout USB_P, // Manual Pad
  inout USB_N, // Manual Pad
  inout CC1, // Manual Pad
  inout CC2, // Manual Pad
  inout FLASH_TEST_VOLT, // Manual Pad
  inout FLASH_TEST_MODE0, // Manual Pad
  inout FLASH_TEST_MODE1, // Manual Pad
  inout OTP_EXT_VOLT, // Manual Pad
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
  inout IOR8, // Dedicated Pad for sysrst_ctrl_aon_ec_rst_l
  inout IOR9, // Dedicated Pad for sysrst_ctrl_aon_flash_wp_l

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

  parameter int Tap0PadIdx = 30;
  parameter int Tap1PadIdx = 27;
  parameter int Dft0PadIdx = 25;
  parameter int Dft1PadIdx = 26;
  parameter int TckPadIdx = 38;
  parameter int TmsPadIdx = 35;
  parameter int TrstNPadIdx = 39;
  parameter int TdiPadIdx = 37;
  parameter int TdoPadIdx = 36;

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
  logic manual_in_cc1, manual_out_cc1, manual_oe_cc1;
  logic manual_in_cc2, manual_out_cc2, manual_oe_cc2;
  logic manual_in_flash_test_volt, manual_out_flash_test_volt, manual_oe_flash_test_volt;
  logic manual_in_flash_test_mode0, manual_out_flash_test_mode0, manual_oe_flash_test_mode0;
  logic manual_in_flash_test_mode1, manual_out_flash_test_mode1, manual_oe_flash_test_mode1;
  logic manual_in_otp_ext_volt, manual_out_otp_ext_volt, manual_oe_otp_ext_volt;

  pad_attr_t manual_attr_por_n;
  pad_attr_t manual_attr_usb_p;
  pad_attr_t manual_attr_usb_n;
  pad_attr_t manual_attr_cc1;
  pad_attr_t manual_attr_cc2;
  pad_attr_t manual_attr_flash_test_volt;
  pad_attr_t manual_attr_flash_test_mode0;
  pad_attr_t manual_attr_flash_test_mode1;
  pad_attr_t manual_attr_otp_ext_volt;


  //////////////////////
  // Padring Instance //
  //////////////////////

  // AST signals needed in padring
  ast_pkg::ast_clks_t ast_base_clks;
  logic scan_rst_n;
  lc_ctrl_pkg::lc_tx_t scanmode;

  padring #(
    // Padring specific counts may differ from pinmux config due
    // to custom, stubbed or added pads.
    .NDioPads(23),
    .NMioPads(47),
    .PhysicalPads(1),
    .NIoBanks(int'(IoBankCount)),
    .DioScanRole ({
      scan_role_pkg::DioPadIor9ScanRole,
      scan_role_pkg::DioPadIor8ScanRole,
      scan_role_pkg::DioPadSpiDevCsLScanRole,
      scan_role_pkg::DioPadSpiDevClkScanRole,
      scan_role_pkg::DioPadSpiDevD3ScanRole,
      scan_role_pkg::DioPadSpiDevD2ScanRole,
      scan_role_pkg::DioPadSpiDevD1ScanRole,
      scan_role_pkg::DioPadSpiDevD0ScanRole,
      scan_role_pkg::DioPadSpiHostCsLScanRole,
      scan_role_pkg::DioPadSpiHostClkScanRole,
      scan_role_pkg::DioPadSpiHostD3ScanRole,
      scan_role_pkg::DioPadSpiHostD2ScanRole,
      scan_role_pkg::DioPadSpiHostD1ScanRole,
      scan_role_pkg::DioPadSpiHostD0ScanRole,
      scan_role_pkg::DioPadOtpExtVoltScanRole,
      scan_role_pkg::DioPadFlashTestMode1ScanRole,
      scan_role_pkg::DioPadFlashTestMode0ScanRole,
      scan_role_pkg::DioPadFlashTestVoltScanRole,
      scan_role_pkg::DioPadCc2ScanRole,
      scan_role_pkg::DioPadCc1ScanRole,
      scan_role_pkg::DioPadUsbNScanRole,
      scan_role_pkg::DioPadUsbPScanRole,
      scan_role_pkg::DioPadPorNScanRole
    }),
    .MioScanRole ({
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
    }),
    .DioPadBank ({
      IoBankVcc, // IOR9
      IoBankVcc, // IOR8
      IoBankVioa, // SPI_DEV_CS_L
      IoBankVioa, // SPI_DEV_CLK
      IoBankVioa, // SPI_DEV_D3
      IoBankVioa, // SPI_DEV_D2
      IoBankVioa, // SPI_DEV_D1
      IoBankVioa, // SPI_DEV_D0
      IoBankVioa, // SPI_HOST_CS_L
      IoBankVioa, // SPI_HOST_CLK
      IoBankVioa, // SPI_HOST_D3
      IoBankVioa, // SPI_HOST_D2
      IoBankVioa, // SPI_HOST_D1
      IoBankVioa, // SPI_HOST_D0
      IoBankVcc, // OTP_EXT_VOLT
      IoBankVcc, // FLASH_TEST_MODE1
      IoBankVcc, // FLASH_TEST_MODE0
      IoBankVcc, // FLASH_TEST_VOLT
      IoBankAvcc, // CC2
      IoBankAvcc, // CC1
      IoBankVcc, // USB_N
      IoBankVcc, // USB_P
      IoBankVcc  // POR_N
    }),
    .MioPadBank ({
      IoBankVcc, // IOR13
      IoBankVcc, // IOR12
      IoBankVcc, // IOR11
      IoBankVcc, // IOR10
      IoBankVcc, // IOR7
      IoBankVcc, // IOR6
      IoBankVcc, // IOR5
      IoBankVcc, // IOR4
      IoBankVcc, // IOR3
      IoBankVcc, // IOR2
      IoBankVcc, // IOR1
      IoBankVcc, // IOR0
      IoBankVcc, // IOC12
      IoBankVcc, // IOC11
      IoBankVcc, // IOC10
      IoBankVcc, // IOC9
      IoBankVcc, // IOC8
      IoBankVcc, // IOC7
      IoBankVcc, // IOC6
      IoBankVcc, // IOC5
      IoBankVcc, // IOC4
      IoBankVcc, // IOC3
      IoBankVcc, // IOC2
      IoBankVcc, // IOC1
      IoBankVcc, // IOC0
      IoBankViob, // IOB12
      IoBankViob, // IOB11
      IoBankViob, // IOB10
      IoBankViob, // IOB9
      IoBankViob, // IOB8
      IoBankViob, // IOB7
      IoBankViob, // IOB6
      IoBankViob, // IOB5
      IoBankViob, // IOB4
      IoBankViob, // IOB3
      IoBankViob, // IOB2
      IoBankViob, // IOB1
      IoBankViob, // IOB0
      IoBankVioa, // IOA8
      IoBankVioa, // IOA7
      IoBankVioa, // IOA6
      IoBankVioa, // IOA5
      IoBankVioa, // IOA4
      IoBankVioa, // IOA3
      IoBankVioa, // IOA2
      IoBankVioa, // IOA1
      IoBankVioa  // IOA0
    }),
    .DioPadType ({
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
      AnalogIn1, // OTP_EXT_VOLT
      InputStd, // FLASH_TEST_MODE1
      InputStd, // FLASH_TEST_MODE0
      AnalogIn0, // FLASH_TEST_VOLT
      InputStd, // CC2
      InputStd, // CC1
      BidirTol, // USB_N
      BidirTol, // USB_P
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
    .clk_scan_i   ( ast_base_clks.clk_sys ),
    .scanmode_i   ( scanmode              ),
    .dio_in_raw_o ( ),
    // Chip IOs
    .dio_pad_io ({
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
      OTP_EXT_VOLT,
      FLASH_TEST_MODE1,
      FLASH_TEST_MODE0,
      FLASH_TEST_VOLT,
      CC2,
      CC1,
      USB_N,
      USB_P,
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
      IOA3,
      IOA2,
      IOA1,
      IOA0
    }),

    // Core-facing
    .dio_in_o ({
        dio_in[DioSysrstCtrlAonFlashWpL],
        dio_in[DioSysrstCtrlAonEcRstL],
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
        manual_in_otp_ext_volt,
        manual_in_flash_test_mode1,
        manual_in_flash_test_mode0,
        manual_in_flash_test_volt,
        manual_in_cc2,
        manual_in_cc1,
        manual_in_usb_n,
        manual_in_usb_p,
        manual_in_por_n
      }),
    .dio_out_i ({
        dio_out[DioSysrstCtrlAonFlashWpL],
        dio_out[DioSysrstCtrlAonEcRstL],
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
        manual_out_otp_ext_volt,
        manual_out_flash_test_mode1,
        manual_out_flash_test_mode0,
        manual_out_flash_test_volt,
        manual_out_cc2,
        manual_out_cc1,
        manual_out_usb_n,
        manual_out_usb_p,
        manual_out_por_n
      }),
    .dio_oe_i ({
        dio_oe[DioSysrstCtrlAonFlashWpL],
        dio_oe[DioSysrstCtrlAonEcRstL],
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
        manual_oe_otp_ext_volt,
        manual_oe_flash_test_mode1,
        manual_oe_flash_test_mode0,
        manual_oe_flash_test_volt,
        manual_oe_cc2,
        manual_oe_cc1,
        manual_oe_usb_n,
        manual_oe_usb_p,
        manual_oe_por_n
      }),
    .dio_attr_i ({
        dio_attr[DioSysrstCtrlAonFlashWpL],
        dio_attr[DioSysrstCtrlAonEcRstL],
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
        manual_attr_otp_ext_volt,
        manual_attr_flash_test_mode1,
        manual_attr_flash_test_mode0,
        manual_attr_flash_test_volt,
        manual_attr_cc2,
        manual_attr_cc1,
        manual_attr_usb_n,
        manual_attr_usb_p,
        manual_attr_por_n
      }),

    .mio_in_o (mio_in[46:0]),
    .mio_out_i (mio_out[46:0]),
    .mio_oe_i (mio_oe[46:0]),
    .mio_attr_i (mio_attr[46:0]),
    .mio_in_raw_o (mio_in_raw[46:0])
  );





  //////////////////////////////////
  // Manual Pad / Signal Tie-offs //
  //////////////////////////////////

  assign manual_out_por_n = 1'b0;
  assign manual_oe_por_n = 1'b0;

  assign manual_out_cc1 = 1'b0;
  assign manual_oe_cc1 = 1'b0;
  assign manual_out_cc2 = 1'b0;
  assign manual_oe_cc2 = 1'b0;

  assign manual_out_flash_test_mode0 = 1'b0;
  assign manual_oe_flash_test_mode0 = 1'b0;
  assign manual_out_flash_test_mode1 = 1'b0;
  assign manual_oe_flash_test_mode1 = 1'b0;
  assign manual_out_flash_test_volt = 1'b0;
  assign manual_oe_flash_test_volt = 1'b0;
  assign manual_out_otp_ext_volt = 1'b0;
  assign manual_oe_otp_ext_volt = 1'b0;

  // These pad attributes currently tied off permanently (these are all input-only pads).
  assign manual_attr_por_n = '0;
  assign manual_attr_cc1 = '0;
  assign manual_attr_cc2 = '0;
  assign manual_attr_flash_test_mode0 = '0;
  assign manual_attr_flash_test_mode1 = '0;
  assign manual_attr_flash_test_volt = '0;
  assign manual_attr_otp_ext_volt = '0;

  logic unused_manual_sigs;
  assign unused_manual_sigs = ^{
    manual_in_cc2,
    manual_in_cc1,
    manual_in_flash_test_volt,
    manual_in_flash_test_mode0,
    manual_in_flash_test_mode1,
    manual_in_otp_ext_volt
  };

  ///////////////////////////////
  // Differential USB Receiver //
  ///////////////////////////////

  // TODO: generalize this USB mux code and align with other tops.

  // Connect the DP pad
  assign dio_in[DioUsbdevDp] = manual_in_usb_p;
  assign manual_out_usb_p = dio_out[DioUsbdevDp];
  assign manual_oe_usb_p = dio_oe[DioUsbdevDp];
  assign manual_attr_usb_p = dio_attr[DioUsbdevDp];

  // Connect the DN pad
  assign dio_in[DioUsbdevDn] = manual_in_usb_n;
  assign manual_out_usb_n = dio_out[DioUsbdevDn];
  assign manual_oe_usb_n = dio_oe[DioUsbdevDn];
  assign manual_attr_usb_n = dio_attr[DioUsbdevDn];

  // Pullups
  logic usb_pullup_p_en, usb_pullup_n_en;
  assign usb_pullup_p_en = dio_out[DioUsbdevDpPullup];
  assign usb_pullup_n_en = dio_out[DioUsbdevDnPullup];

  logic usb_rx_enable;
  assign usb_rx_enable = dio_out[DioUsbdevRxEnable];

  logic [ast_pkg::UsbCalibWidth-1:0] usb_io_pu_cal;

  // pwrmgr interface
  pwrmgr_pkg::pwr_ast_req_t base_ast_pwr;
  pwrmgr_pkg::pwr_ast_rsp_t ast_base_pwr;

  prim_usb_diff_rx #(
    .CalibW(ast_pkg::UsbCalibWidth)
  ) u_prim_usb_diff_rx (
    .input_pi      ( USB_P                 ),
    .input_ni      ( USB_N                 ),
    .input_en_i    ( usb_rx_enable         ),
    .core_pok_h_i  ( ast_pwst_h.aon_pok    ),
    .pullup_p_en_i ( usb_pullup_p_en       ),
    .pullup_n_en_i ( usb_pullup_n_en       ),
    .calibration_i ( usb_io_pu_cal         ),
    .input_o       ( dio_in[DioUsbdevD]    )
  );

  // Tie-off unused signals
  assign dio_in[DioUsbdevSense] = 1'b0;
  assign dio_in[DioUsbdevSe0] = 1'b0;
  assign dio_in[DioUsbdevDpPullup] = 1'b0;
  assign dio_in[DioUsbdevDnPullup] = 1'b0;
  assign dio_in[DioUsbdevTxModeSe] = 1'b0;
  assign dio_in[DioUsbdevSuspend] = 1'b0;
  assign dio_in[DioUsbdevRxEnable] = 1'b0;

  logic unused_usb_sigs;
  assign unused_usb_sigs = ^{
    // Sense
    dio_out[DioUsbdevSense],
    dio_oe[DioUsbdevSense],
    dio_attr[DioUsbdevSense],
    // SE0
    dio_out[DioUsbdevSe0],
    dio_oe[DioUsbdevSe0],
    dio_attr[DioUsbdevSe0],
    // TX Mode
    dio_out[DioUsbdevTxModeSe],
    dio_oe[DioUsbdevTxModeSe],
    dio_attr[DioUsbdevTxModeSe],
    // Suspend
    dio_out[DioUsbdevSuspend],
    dio_oe[DioUsbdevSuspend],
    dio_attr[DioUsbdevSuspend],
    // Rx enable
    dio_oe[DioUsbdevRxEnable],
    dio_attr[DioUsbdevRxEnable],
    // D is used as an input only
    dio_out[DioUsbdevD],
    dio_oe[DioUsbdevD],
    dio_attr[DioUsbdevD],
    // Pullup/down
    dio_oe[DioUsbdevDpPullup],
    dio_oe[DioUsbdevDnPullup],
    dio_attr[DioUsbdevDpPullup],
    dio_attr[DioUsbdevDnPullup]
  };

  //////////////////////
  // AST              //
  //////////////////////
  // TLUL interface
  tlul_pkg::tl_h2d_t base_ast_bus;
  tlul_pkg::tl_d2h_t ast_base_bus;

  // assorted ast status
  ast_pkg::ast_pwst_t ast_pwst;
  ast_pkg::ast_pwst_t ast_pwst_h;

  assign ast_base_pwr.main_pok = ast_pwst.main_pok;

  // synchronization clocks / rests
  clkmgr_pkg::clkmgr_ast_out_t clks_ast;
  rstmgr_pkg::rstmgr_ast_out_t rsts_ast;

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
  lc_ctrl_pkg::lc_tx_t flash_bist_enable;
  logic flash_power_down_h;
  logic flash_power_ready_h;

  // Life cycle clock bypass req/ack
  lc_ctrl_pkg::lc_tx_t ast_clk_byp_req;
  lc_ctrl_pkg::lc_tx_t ast_clk_byp_ack;

  // DFT connections
  logic scan_en;
  lc_ctrl_pkg::lc_tx_t dft_en;
  pinmux_pkg::dft_strap_test_req_t dft_strap_test;

  // Debug connections
  logic [ast_pkg::Ast2PadOutWidth-1:0] ast2pinmux;
  logic [ast_pkg::Pad2AstInWidth-1:0] pad2ast;

  assign pad2ast = {
                     mio_in_raw[MioPadIoc3],
                     mio_in_raw[MioPadIob8],
                     mio_in_raw[MioPadIob7],
                     mio_in_raw[MioPadIob2],
                     mio_in_raw[MioPadIob1],
                     mio_in_raw[MioPadIob0]
                   };


  // Jitter enable
  logic jen;

  // reset domain connections
  import rstmgr_pkg::PowerDomains;
  import rstmgr_pkg::DomainAonSel;
  import rstmgr_pkg::Domain0Sel;

  // external clock comes in at a fixed position
  logic ext_clk;
  assign ext_clk = mio_in_raw[MioPadIoc6];

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


  // AST does not use all clocks / resets forwarded to it
  logic unused_slow_clk_en;
  logic unused_usb_clk_aon;
  logic unused_usb_clk_io_div4;
  logic unused_adc_clk_aon;
  assign unused_slow_clk_en = base_ast_pwr.slow_clk_en;
  assign unused_usb_clk_aon = clks_ast.clk_ast_usbdev_aon_peri;
  assign unused_usb_clk_io_div4 = clks_ast.clk_ast_usbdev_io_div4_peri;
  assign unused_adc_clk_aon = clks_ast.clk_ast_adc_ctrl_aon_aon_peri;

  logic [PowerDomains-1:0] unused_usb_rst;
  logic [PowerDomains-1:0] unused_usb_usbif_rst;
  logic [PowerDomains-1:0] unused_usb_sys_aon_rst;
  logic [PowerDomains-1:0] unused_adc_ctrl_sys_aon_rst;
  logic [PowerDomains-1:0] unused_ast_rst;
  logic [PowerDomains-1:0] unused_sensor_ctrl_rst;
  logic [PowerDomains-1:0] unused_adc_ctrl_rst;
  logic [PowerDomains-1:0] unused_entropy_sys_rst;
  logic [PowerDomains-1:0] unused_edn_sys_rst;
  assign unused_usb_rst = rsts_ast.rst_ast_usbdev_usb_n;
  assign unused_usb_sys_aon_rst = rsts_ast.rst_ast_usbdev_sys_aon_n;
  assign unused_usb_usbif_rst = rsts_ast.rst_ast_usbdev_usbif_n;
  assign unused_adc_ctrl_sys_aon_rst = rsts_ast.rst_ast_adc_ctrl_aon_sys_aon_n;
  assign unused_ast_rst = rsts_ast.rst_ast_ast_lc_io_div4_n;
  assign unused_sensor_ctrl_rst = rsts_ast.rst_ast_sensor_ctrl_aon_lc_io_div4_n;
  assign unused_adc_ctrl_rst = rsts_ast.rst_ast_adc_ctrl_aon_sys_io_div4_n;
  assign unused_entropy_sys_rst = rsts_ast.rst_ast_entropy_src_sys_n;
  assign unused_edn_sys_rst = rsts_ast.rst_ast_edn0_sys_n;

  logic unused_pwr_clamp;
  assign unused_pwr_clamp = base_ast_pwr.pwr_clamp;

  ast_pkg::ast_dif_t flash_alert;
  ast_pkg::ast_dif_t otp_alert;
  logic ast_init_done;

  ast #(
    .EntropyStreams(ast_pkg::EntropyStreams),
    .AdcChannels(ast_pkg::AdcChannels),
    .AdcDataWidth(ast_pkg::AdcDataWidth),
    .UsbCalibWidth(ast_pkg::UsbCalibWidth),
    .Ast2PadOutWidth(ast_pkg::Ast2PadOutWidth),
    .Pad2AstInWidth(ast_pkg::Pad2AstInWidth)
  ) u_ast (
    // tlul
    .tl_i                  ( base_ast_bus ),
    .tl_o                  ( ast_base_bus ),
    // init done indication
    .ast_init_done_o       ( ast_init_done ),
    // buffered clocks & resets
    // Reset domain connection is manual at the moment
    .clk_ast_adc_i         ( clks_ast.clk_ast_adc_ctrl_aon_io_div4_peri ),
    .rst_ast_adc_ni        ( rsts_ast.rst_ast_adc_ctrl_aon_sys_io_div4_n[DomainAonSel] ),
    .clk_ast_alert_i       ( clks_ast.clk_ast_sensor_ctrl_aon_io_div4_secure ),
    .rst_ast_alert_ni      ( rsts_ast.rst_ast_sensor_ctrl_aon_lc_io_div4_n[DomainAonSel] ),
    .clk_ast_es_i          ( clks_ast.clk_ast_edn0_main_secure ),
    .rst_ast_es_ni         ( rsts_ast.rst_ast_edn0_sys_n[Domain0Sel] ),
    .clk_ast_rng_i         ( clks_ast.clk_ast_entropy_src_main_secure ),
    .rst_ast_rng_ni        ( rsts_ast.rst_ast_entropy_src_sys_n[Domain0Sel] ),
    .clk_ast_tlul_i        ( clks_ast.clk_ast_ast_io_div4_secure ),
    .rst_ast_tlul_ni       ( rsts_ast.rst_ast_ast_lc_io_div4_n[DomainAonSel] ),
    .clk_ast_usb_i         ( clks_ast.clk_ast_usbdev_usb_peri ),
    .rst_ast_usb_ni        ( rsts_ast.rst_ast_usbdev_usbif_n[Domain0Sel] ),
    .clk_ast_ext_i         ( ext_clk ),
    .por_ni                ( manual_in_por_n ),
    // clocks' oschillator bypass for FPGA
    .clk_osc_byp_i         ( '0 ),
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
    // usb source clock
    .usb_ref_pulse_i       ( usb_ref_pulse ),
    .usb_ref_val_i         ( usb_ref_val ),
    .clk_src_usb_en_i      ( base_ast_pwr.usb_clk_en ),
    .clk_src_usb_o         ( ast_base_clks.clk_usb ),
    .clk_src_usb_val_o     ( ast_base_pwr.usb_clk_val ),
    // USB IO Pull-up Calibration Setting
    .usb_io_pu_cal_o       ( usb_io_pu_cal ),
    // adc
    .adc_a0_ai             ( CC1 ),
    .adc_a1_ai             ( CC2 ),
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
    // pinmux related
    .padmux2ast_i          ( pad2ast    ),
    .ast2padmux_o          ( ast2pinmux ),
    // Direct short to PAD
    .pad2ast_t0_ai         ( IOA4 ),
    .pad2ast_t1_ai         ( IOA5 ),
    .ast2pad_t0_ao         ( IOA2 ),
    .ast2pad_t1_ao         ( IOA3 ),
    .lc_clk_byp_req_i      ( ast_clk_byp_req   ),
    .lc_clk_byp_ack_o      ( ast_clk_byp_ack   ),
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

  //////////////////////
  // Top-level design //
  //////////////////////

  top_earlgrey #(
    .PinmuxAonTargetCfg(PinmuxTargetCfg)
  ) top_earlgrey (
    // ast connections
    .por_n_i                      ( ast_pwst.aon_pok           ),
    .clk_main_i                   ( ast_base_clks.clk_sys      ),
    .clk_io_i                     ( ast_base_clks.clk_io       ),
    .clk_usb_i                    ( ast_base_clks.clk_usb      ),
    .clk_aon_i                    ( ast_base_clks.clk_aon      ),
    .clks_ast_o                   ( clks_ast                   ),
    .clk_main_jitter_en_o         ( jen                        ),
    .rsts_ast_o                   ( rsts_ast                   ),
    .pwrmgr_ast_req_o             ( base_ast_pwr               ),
    .pwrmgr_ast_rsp_i             ( ast_base_pwr               ),
    .sensor_ctrl_ast_alert_req_i  ( ast_alert_req              ),
    .sensor_ctrl_ast_alert_rsp_o  ( ast_alert_rsp              ),
    .sensor_ctrl_ast_status_i     ( ast_pwst.io_pok            ),
    .usbdev_usb_ref_val_o         ( usb_ref_pulse              ),
    .usbdev_usb_ref_pulse_o       ( usb_ref_val                ),
    .ast_tl_req_o                 ( base_ast_bus               ),
    .ast_tl_rsp_i                 ( ast_base_bus               ),
    .adc_req_o                    ( adc_req                    ),
    .adc_rsp_i                    ( adc_rsp                    ),
    .ast_edn_req_i                ( ast_edn_edn_req            ),
    .ast_edn_rsp_o                ( ast_edn_edn_rsp            ),
    .otp_ctrl_otp_ast_pwr_seq_o   ( otp_ctrl_otp_ast_pwr_seq   ),
    .otp_ctrl_otp_ast_pwr_seq_h_i ( otp_ctrl_otp_ast_pwr_seq_h ),
    .otp_alert_o                  ( otp_alert                  ),
    .flash_bist_enable_i          ( flash_bist_enable          ),
    .flash_power_down_h_i         ( flash_power_down_h         ),
    .flash_power_ready_h_i        ( flash_power_ready_h        ),
    .flash_alert_o                ( flash_alert                ),
    .es_rng_req_o                 ( es_rng_req                 ),
    .es_rng_rsp_i                 ( es_rng_rsp                 ),
    .es_rng_fips_o                ( es_rng_fips                ),
    .ast_clk_byp_req_o            ( ast_clk_byp_req            ),
    .ast_clk_byp_ack_i            ( ast_clk_byp_ack            ),
    .ast2pinmux_i                 ( ast2pinmux                 ),
    .ast_init_done_i              ( ast_init_done              ),

    // Flash test mode voltages
    .flash_test_mode_a_io         ( {FLASH_TEST_MODE1,
                                     FLASH_TEST_MODE0}         ),
    .flash_test_voltage_h_io      ( FLASH_TEST_VOLT            ),

    // OTP external voltage
    .otp_ext_voltage_h_io         ( OTP_EXT_VOLT               ),

    // Multiplexed I/O
    .mio_in_i                     ( mio_in                     ),
    .mio_out_o                    ( mio_out                    ),
    .mio_oe_o                     ( mio_oe                     ),

    // Dedicated I/O
    .dio_in_i                     ( dio_in                     ),
    .dio_out_o                    ( dio_out                    ),
    .dio_oe_o                     ( dio_oe                     ),

    // Pad attributes
    .mio_attr_o                   ( mio_attr                   ),
    .dio_attr_o                   ( dio_attr                   ),

    // Memory attributes
    .ram_1p_cfg_i                 ( ram_1p_cfg                 ),
    .ram_2p_cfg_i                 ( ram_2p_cfg                 ),
    .rom_cfg_i                    ( rom_cfg                    ),

    // DFT signals
    .ast_lc_dft_en_o              ( dft_en                     ),
    .dft_strap_test_o             ( dft_strap_test             ),
    .dft_hold_tap_sel_i           ( '0                         ),
    .scan_rst_ni                  ( scan_rst_n                 ),
    .scan_en_i                    ( scan_en                    ),
    .scanmode_i                   ( scanmode                   )
  );



endmodule : chip_earlgrey_asic
