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
  inout IOR8, // Dedicated Pad for sysrst_ctrl_aon_ec_rst_out_l
  inout IOR9, // Dedicated Pad for sysrst_ctrl_aon_pwrb_out

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

  // TODO: this is temporary and will be removed in the future.
  // This specifies the tie-off values of the muxed MIO/DIOs
  // when the JTAG is active. SPI CSB is active low.
  localparam logic [pinmux_pkg::NumIOs-1:0] TieOffValues = pinmux_pkg::NumIOs'(1'b1 << (
      pinmux_reg_pkg::NMioPads + DioSpiDeviceCsb));

  // DFT and Debug signal positions in the pinout.
  localparam pinmux_pkg::target_cfg_t PinmuxTargetCfg = '{
    const_sampling:    1'b1,
    tie_offs:          TieOffValues, // TODO: can we remove this and just set it to zero?
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
    usb_dn_pullup_idx: DioUsbdevDnPullup
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

  // Manual pads
  logic manual_in_por_n, manual_out_por_n, manual_oe_por_n;
  logic manual_in_usb_p, manual_out_usb_p, manual_oe_usb_p;
  logic manual_in_usb_n, manual_out_usb_n, manual_oe_usb_n;
  logic manual_in_cc1, manual_out_cc1, manual_oe_cc1;
  logic manual_in_cc2, manual_out_cc2, manual_oe_cc2;
  logic manual_in_flash_test_volt, manual_out_flash_test_volt, manual_oe_flash_test_volt;
  logic manual_in_flash_test_mode0, manual_out_flash_test_mode0, manual_oe_flash_test_mode0;
  logic manual_in_flash_test_mode1, manual_out_flash_test_mode1, manual_oe_flash_test_mode1;

  pad_attr_t manual_attr_por_n;
  pad_attr_t manual_attr_usb_p;
  pad_attr_t manual_attr_usb_n;
  pad_attr_t manual_attr_cc1;
  pad_attr_t manual_attr_cc2;
  pad_attr_t manual_attr_flash_test_volt;
  pad_attr_t manual_attr_flash_test_mode0;
  pad_attr_t manual_attr_flash_test_mode1;


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
    .NDioPads(22),
    .NMioPads(47),
    // TODO: need to add ScanRole parameters
    .PhysicalPads(1),
    .NIoBanks(IoBankCount),
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
  // TODO: wire this up to AST. Hint: the top_<name>_pkg contains
  // generated parameters that can be used to index pads by name.
    .dio_in_raw_o ( ),
    .mio_in_raw_o ( ),
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
        dio_in[DioSysrstCtrlAonPwrbOut],
        dio_in[DioSysrstCtrlAonEcRstOutL],
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
        dio_out[DioSysrstCtrlAonPwrbOut],
        dio_out[DioSysrstCtrlAonEcRstOutL],
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
        dio_oe[DioSysrstCtrlAonPwrbOut],
        dio_oe[DioSysrstCtrlAonEcRstOutL],
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
        dio_attr[DioSysrstCtrlAonPwrbOut],
        dio_attr[DioSysrstCtrlAonEcRstOutL],
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
        manual_attr_flash_test_mode1,
        manual_attr_flash_test_mode0,
        manual_attr_flash_test_volt,
        manual_attr_cc2,
        manual_attr_cc1,
        manual_attr_usb_n,
        manual_attr_usb_p,
        manual_attr_por_n
      }),

    .mio_in_o ({
        mio_in[46],
        mio_in[45],
        mio_in[44],
        mio_in[43],
        mio_in[42],
        mio_in[41],
        mio_in[40],
        mio_in[39],
        mio_in[38],
        mio_in[37],
        mio_in[36],
        mio_in[35],
        mio_in[34],
        mio_in[33],
        mio_in[32],
        mio_in[31],
        mio_in[30],
        mio_in[29],
        mio_in[28],
        mio_in[27],
        mio_in[26],
        mio_in[25],
        mio_in[24],
        mio_in[23],
        mio_in[22],
        mio_in[21],
        mio_in[20],
        mio_in[19],
        mio_in[18],
        mio_in[17],
        mio_in[16],
        mio_in[15],
        mio_in[14],
        mio_in[13],
        mio_in[12],
        mio_in[11],
        mio_in[10],
        mio_in[9],
        mio_in[8],
        mio_in[7],
        mio_in[6],
        mio_in[5],
        mio_in[4],
        mio_in[3],
        mio_in[2],
        mio_in[1],
        mio_in[0]
      }),
    .mio_out_i ({
        mio_out[46],
        mio_out[45],
        mio_out[44],
        mio_out[43],
        mio_out[42],
        mio_out[41],
        mio_out[40],
        mio_out[39],
        mio_out[38],
        mio_out[37],
        mio_out[36],
        mio_out[35],
        mio_out[34],
        mio_out[33],
        mio_out[32],
        mio_out[31],
        mio_out[30],
        mio_out[29],
        mio_out[28],
        mio_out[27],
        mio_out[26],
        mio_out[25],
        mio_out[24],
        mio_out[23],
        mio_out[22],
        mio_out[21],
        mio_out[20],
        mio_out[19],
        mio_out[18],
        mio_out[17],
        mio_out[16],
        mio_out[15],
        mio_out[14],
        mio_out[13],
        mio_out[12],
        mio_out[11],
        mio_out[10],
        mio_out[9],
        mio_out[8],
        mio_out[7],
        mio_out[6],
        mio_out[5],
        mio_out[4],
        mio_out[3],
        mio_out[2],
        mio_out[1],
        mio_out[0]
      }),
    .mio_oe_i ({
        mio_oe[46],
        mio_oe[45],
        mio_oe[44],
        mio_oe[43],
        mio_oe[42],
        mio_oe[41],
        mio_oe[40],
        mio_oe[39],
        mio_oe[38],
        mio_oe[37],
        mio_oe[36],
        mio_oe[35],
        mio_oe[34],
        mio_oe[33],
        mio_oe[32],
        mio_oe[31],
        mio_oe[30],
        mio_oe[29],
        mio_oe[28],
        mio_oe[27],
        mio_oe[26],
        mio_oe[25],
        mio_oe[24],
        mio_oe[23],
        mio_oe[22],
        mio_oe[21],
        mio_oe[20],
        mio_oe[19],
        mio_oe[18],
        mio_oe[17],
        mio_oe[16],
        mio_oe[15],
        mio_oe[14],
        mio_oe[13],
        mio_oe[12],
        mio_oe[11],
        mio_oe[10],
        mio_oe[9],
        mio_oe[8],
        mio_oe[7],
        mio_oe[6],
        mio_oe[5],
        mio_oe[4],
        mio_oe[3],
        mio_oe[2],
        mio_oe[1],
        mio_oe[0]
      }),
    .mio_attr_i ({
        mio_attr[46],
        mio_attr[45],
        mio_attr[44],
        mio_attr[43],
        mio_attr[42],
        mio_attr[41],
        mio_attr[40],
        mio_attr[39],
        mio_attr[38],
        mio_attr[37],
        mio_attr[36],
        mio_attr[35],
        mio_attr[34],
        mio_attr[33],
        mio_attr[32],
        mio_attr[31],
        mio_attr[30],
        mio_attr[29],
        mio_attr[28],
        mio_attr[27],
        mio_attr[26],
        mio_attr[25],
        mio_attr[24],
        mio_attr[23],
        mio_attr[22],
        mio_attr[21],
        mio_attr[20],
        mio_attr[19],
        mio_attr[18],
        mio_attr[17],
        mio_attr[16],
        mio_attr[15],
        mio_attr[14],
        mio_attr[13],
        mio_attr[12],
        mio_attr[11],
        mio_attr[10],
        mio_attr[9],
        mio_attr[8],
        mio_attr[7],
        mio_attr[6],
        mio_attr[5],
        mio_attr[4],
        mio_attr[3],
        mio_attr[2],
        mio_attr[1],
        mio_attr[0]
      })
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

  assign manual_out_flash_test_volt = 1'b0;
  assign manual_oe_flash_test_volt = 1'b0;

  // These pad attributes currently tied off permanently (these are all input-only pads).
  assign manual_attr_por_n = '0;
  assign manual_attr_cc1 = '0;
  assign manual_attr_cc2 = '0;
  assign manual_attr_flash_test_volt = '0;

  logic unused_manual_sigs;
  assign unused_manual_sigs = ^{
    manual_in_cc2,
    manual_in_cc1,
    manual_in_flash_test_volt
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
  assign usb_pullup_p_en = dio_out[DioUsbdevDpPullup] & dio_oe[DioUsbdevDpPullup];
  assign usb_pullup_n_en = dio_out[DioUsbdevDnPullup] & dio_oe[DioUsbdevDnPullup];

  // TODO(#5925): connect this to AST?
  logic usbdev_aon_usb_rx_enable;
  logic [ast_pkg::UsbCalibWidth-1:0] usb_io_pu_cal;
  assign usbdev_aon_usb_rx_enable = 1'b0;

  prim_usb_diff_rx #(
    .CalibW(ast_pkg::UsbCalibWidth)
  ) u_prim_usb_diff_rx (
    .input_pi      ( USB_P                    ),
    .input_ni      ( USB_N                    ),
    .input_en_i    ( usbdev_aon_usb_rx_enable ),
    .core_pok_i    ( ast_base_pwr.main_pok    ),
    .pullup_p_en_i ( usb_pullup_p_en          ),
    .pullup_n_en_i ( usb_pullup_n_en          ),
    .calibration_i ( usb_io_pu_cal            ),
    .input_o       ( dio_in[DioUsbdevD]  )
  );

  // Tie-off unused signals
  assign dio_in[DioUsbdevSense] = 1'b0;
  assign dio_in[DioUsbdevSe0] = 1'b0;
  assign dio_in[DioUsbdevTxModeSe] = 1'b0;
  assign dio_in[DioUsbdevSuspend] = 1'b0;

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
    // D is used as an input only
    dio_out[DioUsbdevD],
    dio_oe[DioUsbdevD],
    dio_attr[DioUsbdevD]
  };

  //////////////////////
  // AST              //
  //////////////////////
  // TLUL interface
  tlul_pkg::tl_h2d_t base_ast_bus;
  tlul_pkg::tl_d2h_t ast_base_bus;

  // assorted ast status
  ast_pkg::ast_status_t ast_status;

  // ast clocks and resets
  logic aon_pok;

  // pwrmgr interface
  pwrmgr_pkg::pwr_ast_req_t base_ast_pwr;
  pwrmgr_pkg::pwr_ast_rsp_t ast_base_pwr;

  // synchronization clocks / rests
  clkmgr_pkg::clkmgr_ast_out_t clks_ast;
  rstmgr_pkg::rstmgr_ast_out_t rsts_ast;

  // otp power sequence
  otp_ctrl_pkg::otp_ast_req_t otp_ctrl_otp_ast_pwr_seq;
  otp_ctrl_pkg::otp_ast_rsp_t otp_ctrl_otp_ast_pwr_seq_h;

  logic usb_ref_pulse;
  logic usb_ref_val;

  // adc
  // The adc package definition should eventually be moved to the adc module
  ast_pkg::adc_ast_req_t adc_i;
  ast_pkg::adc_ast_rsp_t adc_o;

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
  logic [ast_pkg::Pad2AstInWidth-1:0] pinmux2ast;

  // Jitter enable
  logic jen;

  // Alert connections
  import sensor_ctrl_reg_pkg::AsSel;
  import sensor_ctrl_reg_pkg::CgSel;
  import sensor_ctrl_reg_pkg::GdSel;
  import sensor_ctrl_reg_pkg::TsHiSel;
  import sensor_ctrl_reg_pkg::TsLoSel;
  import sensor_ctrl_reg_pkg::LsSel;
  import sensor_ctrl_reg_pkg::OtSel;

  // reset domain connections
  import rstmgr_pkg::PowerDomains;
  import rstmgr_pkg::DomainAonSel;
  import rstmgr_pkg::Domain0Sel;

  // adc connections
  ast_pkg::adc_ast_req_t adc_req;
  ast_pkg::adc_ast_rsp_t adc_rsp;

  // TODO: need to mux the external clock.
  logic ext_clk;
  assign ext_clk = 1'b0;

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
  assign unused_slow_clk_en = base_ast_pwr.slow_clk_en;
  assign unused_usb_clk_aon = clks_ast.clk_ast_usbdev_aon_peri;
  assign unused_usb_clk_io_div4 = clks_ast.clk_ast_usbdev_io_div4_peri;

  logic unused_usb_usb_rst;
  logic [PowerDomains-1:0] unused_usb_sys_io_div4_rst;
  logic [PowerDomains-1:0] unused_usb_sys_aon_rst;
  logic unused_ast_sys_io_div4_rst;
  logic unused_sensor_ctrl_sys_io_div4_rst;
  logic unused_adc_ctrl_sys_io_div4_rst;
  logic unused_entropy_sys_rst;
  logic unused_edn_sys_rst;
  assign unused_usb_usb_rst = rsts_ast.rst_ast_usbdev_usb_n[DomainAonSel];
  assign unused_usb_sys_io_div4_rst = rsts_ast.rst_ast_usbdev_sys_io_div4_n;
  assign unused_usb_sys_aon_rst = rsts_ast.rst_ast_usbdev_sys_aon_n;
  assign unused_ast_sys_io_div4_rst =
    rsts_ast.rst_ast_ast_sys_io_div4_n[Domain0Sel];
  assign unused_sensor_ctrl_sys_io_div4_rst =
    rsts_ast.rst_ast_sensor_ctrl_aon_sys_io_div4_n[Domain0Sel];
  assign unused_adc_ctrl_sys_io_div4_rst =
    rsts_ast.rst_ast_adc_ctrl_aon_sys_io_div4_n[Domain0Sel];
  assign unused_entropy_sys_rst = rsts_ast.rst_ast_entropy_src_sys_n[DomainAonSel];
  assign unused_edn_sys_rst = rsts_ast.rst_ast_edn0_sys_n[DomainAonSel];


  ast #(
    .EntropyStreams(top_pkg::ENTROPY_STREAM),
    .AdcChannels(top_pkg::ADC_CHANNELS),
    .AdcDataWidth(top_pkg::ADC_DATAW),
    .UsbCalibWidth(ast_pkg::UsbCalibWidth),
    .Ast2PadOutWidth(ast_pkg::Ast2PadOutWidth),
    .Pad2AstInWidth(ast_pkg::Pad2AstInWidth)
  ) u_ast (
    // tlul
    .tl_i                  ( base_ast_bus ),
    .tl_o                  ( ast_base_bus ),
    // buffered clocks & resets
    // Reset domain connection is manual at the moment
    .clk_ast_adc_i         ( clks_ast.clk_ast_adc_ctrl_aon_io_div4_peri ),
    .rst_ast_adc_ni        ( rsts_ast.rst_ast_adc_ctrl_aon_sys_io_div4_n[DomainAonSel] ),
    .clk_ast_alert_i       ( clks_ast.clk_ast_sensor_ctrl_aon_io_div4_secure ),
    .rst_ast_alert_ni      ( rsts_ast.rst_ast_sensor_ctrl_aon_sys_io_div4_n[DomainAonSel] ),
    .clk_ast_es_i          ( clks_ast.clk_ast_edn0_main_secure ),
    .rst_ast_es_ni         ( rsts_ast.rst_ast_edn0_sys_n[Domain0Sel] ),
    .clk_ast_rng_i         ( clks_ast.clk_ast_entropy_src_main_secure ),
    .rst_ast_rng_ni        ( rsts_ast.rst_ast_entropy_src_sys_n[Domain0Sel] ),
    .clk_ast_tlul_i        ( clks_ast.clk_ast_ast_io_div4_secure ),
    .rst_ast_tlul_ni       ( rsts_ast.rst_ast_ast_sys_io_div4_n[DomainAonSel] ),
    .clk_ast_usb_i         ( clks_ast.clk_ast_usbdev_usb_peri ),
    .rst_ast_usb_ni        ( rsts_ast.rst_ast_usbdev_usb_n[Domain0Sel] ),
    .clk_ast_ext_i         ( ext_clk ),
    .por_ni                ( manual_in_por_n ),
    // pok test for FPGA
    .vcc_supp_i            ( 1'b1 ),
    .vcaon_supp_i          ( 1'b1 ),
    .vcmain_supp_i         ( 1'b1 ),
    .vioa_supp_i           ( 1'b1 ),
    .viob_supp_i           ( 1'b1 ),
    // pok
    .vcaon_pok_o           ( aon_pok ),
    .vcmain_pok_o          ( ast_base_pwr.main_pok ),
    .vioa_pok_o            ( ast_status.io_pok[0] ),
    .viob_pok_o            ( ast_status.io_pok[1] ),
    // main regulator
    .main_iso_en_i         ( base_ast_pwr.pwr_clamp ),
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
    .as_alert_trig_i       ( ast_alert_rsp.alerts_trig[AsSel]    ),
    .as_alert_ack_i        ( ast_alert_rsp.alerts_ack[AsSel]     ),
    .as_alert_o            ( ast_alert_req.alerts[AsSel]         ),
    .cg_alert_trig_i       ( ast_alert_rsp.alerts_trig[CgSel]    ),
    .cg_alert_ack_i        ( ast_alert_rsp.alerts_ack[CgSel]     ),
    .cg_alert_o            ( ast_alert_req.alerts[CgSel]         ),
    .gd_alert_trig_i       ( ast_alert_rsp.alerts_trig[GdSel]    ),
    .gd_alert_ack_i        ( ast_alert_rsp.alerts_ack[GdSel]     ),
    .gd_alert_o            ( ast_alert_req.alerts[GdSel]         ),
    .ts_alert_hi_trig_i    ( ast_alert_rsp.alerts_trig[TsHiSel]  ),
    .ts_alert_hi_ack_i     ( ast_alert_rsp.alerts_ack[TsHiSel]   ),
    .ts_alert_hi_o         ( ast_alert_req.alerts[TsHiSel]       ),
    .ts_alert_lo_trig_i    ( ast_alert_rsp.alerts_trig[TsLoSel]  ),
    .ts_alert_lo_ack_i     ( ast_alert_rsp.alerts_ack[TsLoSel]   ),
    .ts_alert_lo_o         ( ast_alert_req.alerts[TsLoSel]       ),
    .ls_alert_trig_i       ( ast_alert_rsp.alerts_trig[LsSel]    ),
    .ls_alert_ack_i        ( ast_alert_rsp.alerts_ack[LsSel]     ),
    .ls_alert_o            ( ast_alert_req.alerts[LsSel]         ),
    .ot_alert_trig_i       ( ast_alert_rsp.alerts_trig[OtSel]    ),
    .ot_alert_ack_i        ( ast_alert_rsp.alerts_ack[OtSel]     ),
    .ot_alert_o            ( ast_alert_req.alerts[OtSel]         ),
    // dft
    .dft_strap_test_i      ( dft_strap_test   ),
    .lc_dft_en_i           ( dft_en           ),
    // pinmux related
    .padmux2ast_i          ( pinmux2ast ),
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
    .AesMasking(1'b1),
    .AesSBoxImpl(aes_pkg::SBoxImplDom),
    .SecAesStartTriggerDelay(0),
    .SecAesAllowForcingMasks(1'b0),
    .KmacEnMasking(1),  // DOM AND + Masking scheme
    .KmacReuseShare(0),
    .SramCtrlRetAonInstrExec(0),
    .SramCtrlMainInstrExec(1),
    .PinmuxAonTargetCfg(PinmuxTargetCfg)
  ) top_earlgrey (
    .rst_ni                       ( aon_pok                    ),
    // ast connections
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
    .sensor_ctrl_ast_status_i     ( ast_status                 ),
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
    .flash_bist_enable_i          ( flash_bist_enable          ),
    .flash_power_down_h_i         ( flash_power_down_h         ),
    .flash_power_ready_h_i        ( flash_power_ready_h        ),
    .es_rng_req_o                 ( es_rng_req                 ),
    .es_rng_rsp_i                 ( es_rng_rsp                 ),
    .es_rng_fips_o                ( es_rng_fips                ),
    .ast_clk_byp_req_o            ( ast_clk_byp_req            ),
    .ast_clk_byp_ack_i            ( ast_clk_byp_ack            ),
    .pinmux2ast_o                 ( pinmux2ast                 ),
    .ast2pinmux_i                 ( ast2pinmux                 ),

    // Flash test mode voltages
    .flash_test_mode_a_io         ( {FLASH_TEST_MODE1,
                                     FLASH_TEST_MODE0}         ),
    .flash_test_voltage_h_io      ( FLASH_TEST_VOLT            ),

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
    .scan_rst_ni                  ( scan_rst_n                 ),
    .scan_en_i                    ( scan_en                    ),
    .scanmode_i                   ( scanmode                   )
  );




endmodule : chip_earlgrey_asic
