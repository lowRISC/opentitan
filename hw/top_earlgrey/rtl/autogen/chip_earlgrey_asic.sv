// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_earlgrey/data/top_earlgrey.hjson
//                -o hw/top_earlgrey/



module chip_earlgrey_asic #(
  parameter bit SecRomCtrlDisableScrambling = 1'b0
) (
  // Dedicated Pads
  inout POR_N, // Manual Pad
  inout USB_P, // Manual Pad
  inout USB_N, // Manual Pad
  `INOUT_AI CC1, // Manual Pad
  `INOUT_AI CC2, // Manual Pad
  inout RRAM_ANALOG, // Manual Pad
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
  logic                         [19:0] dio_in_raw;

  logic unused_mio_in_raw;
  logic unused_dio_in_raw;
  assign unused_mio_in_raw = ^mio_in_raw;
  assign unused_dio_in_raw = ^dio_in_raw;

  // Manual pads
  logic manual_in_por_n, manual_out_por_n, manual_oe_por_n;
  logic manual_in_usb_p, manual_out_usb_p, manual_oe_usb_p;
  logic manual_in_usb_n, manual_out_usb_n, manual_oe_usb_n;
  logic manual_in_cc1, manual_out_cc1, manual_oe_cc1;
  logic manual_in_cc2, manual_out_cc2, manual_oe_cc2;
  logic manual_in_rram_analog, manual_out_rram_analog, manual_oe_rram_analog;

  pad_attr_t manual_attr_por_n;
  pad_attr_t manual_attr_usb_p;
  pad_attr_t manual_attr_usb_n;
  pad_attr_t manual_attr_cc1;
  pad_attr_t manual_attr_cc2;
  pad_attr_t manual_attr_rram_analog;

  // Power state from AST to USB
  ast_pkg::ast_pwst_t ast_pwst_h;

  // AST ADC analog inputs and direct analog pad-short outputs.
  ast_pkg::awire_t ast_adc_a0_a, ast_adc_a1_a;
  ast_pkg::awire_t ast2pad_t0_a, ast2pad_t1_a;
  assign ast_adc_a0_a = CC1;
  assign ast_adc_a1_a = CC2;
  assign IOA2 = ast2pad_t0_a;
  assign IOA3 = ast2pad_t1_a;

  //////////////////////
  // Padring Instance //
  //////////////////////

  // AST signals needed in padring - must be decleared here
  logic padring_scan_clk;
  prim_mubi_pkg::mubi4_t scanmode;

  padring #(
    // Padring specific counts may differ from pinmux config due
    // to custom, stubbed or added pads.
    .NDioPads(20),
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
      scan_role_pkg::DioPadRramAnalogScanRole,
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
    .DioPadOrient ({
      pad_orient_pkg::DioPadIor9PadOrient,
      pad_orient_pkg::DioPadIor8PadOrient,
      pad_orient_pkg::DioPadSpiDevCsLPadOrient,
      pad_orient_pkg::DioPadSpiDevClkPadOrient,
      pad_orient_pkg::DioPadSpiDevD3PadOrient,
      pad_orient_pkg::DioPadSpiDevD2PadOrient,
      pad_orient_pkg::DioPadSpiDevD1PadOrient,
      pad_orient_pkg::DioPadSpiDevD0PadOrient,
      pad_orient_pkg::DioPadSpiHostCsLPadOrient,
      pad_orient_pkg::DioPadSpiHostClkPadOrient,
      pad_orient_pkg::DioPadSpiHostD3PadOrient,
      pad_orient_pkg::DioPadSpiHostD2PadOrient,
      pad_orient_pkg::DioPadSpiHostD1PadOrient,
      pad_orient_pkg::DioPadSpiHostD0PadOrient,
      pad_orient_pkg::DioPadRramAnalogPadOrient,
      pad_orient_pkg::DioPadCc2PadOrient,
      pad_orient_pkg::DioPadCc1PadOrient,
      pad_orient_pkg::DioPadUsbNPadOrient,
      pad_orient_pkg::DioPadUsbPPadOrient,
      pad_orient_pkg::DioPadPorNPadOrient
    }),
    .MioPadOrient ({
      pad_orient_pkg::MioPadIor13PadOrient,
      pad_orient_pkg::MioPadIor12PadOrient,
      pad_orient_pkg::MioPadIor11PadOrient,
      pad_orient_pkg::MioPadIor10PadOrient,
      pad_orient_pkg::MioPadIor7PadOrient,
      pad_orient_pkg::MioPadIor6PadOrient,
      pad_orient_pkg::MioPadIor5PadOrient,
      pad_orient_pkg::MioPadIor4PadOrient,
      pad_orient_pkg::MioPadIor3PadOrient,
      pad_orient_pkg::MioPadIor2PadOrient,
      pad_orient_pkg::MioPadIor1PadOrient,
      pad_orient_pkg::MioPadIor0PadOrient,
      pad_orient_pkg::MioPadIoc12PadOrient,
      pad_orient_pkg::MioPadIoc11PadOrient,
      pad_orient_pkg::MioPadIoc10PadOrient,
      pad_orient_pkg::MioPadIoc9PadOrient,
      pad_orient_pkg::MioPadIoc8PadOrient,
      pad_orient_pkg::MioPadIoc7PadOrient,
      pad_orient_pkg::MioPadIoc6PadOrient,
      pad_orient_pkg::MioPadIoc5PadOrient,
      pad_orient_pkg::MioPadIoc4PadOrient,
      pad_orient_pkg::MioPadIoc3PadOrient,
      pad_orient_pkg::MioPadIoc2PadOrient,
      pad_orient_pkg::MioPadIoc1PadOrient,
      pad_orient_pkg::MioPadIoc0PadOrient,
      pad_orient_pkg::MioPadIob12PadOrient,
      pad_orient_pkg::MioPadIob11PadOrient,
      pad_orient_pkg::MioPadIob10PadOrient,
      pad_orient_pkg::MioPadIob9PadOrient,
      pad_orient_pkg::MioPadIob8PadOrient,
      pad_orient_pkg::MioPadIob7PadOrient,
      pad_orient_pkg::MioPadIob6PadOrient,
      pad_orient_pkg::MioPadIob5PadOrient,
      pad_orient_pkg::MioPadIob4PadOrient,
      pad_orient_pkg::MioPadIob3PadOrient,
      pad_orient_pkg::MioPadIob2PadOrient,
      pad_orient_pkg::MioPadIob1PadOrient,
      pad_orient_pkg::MioPadIob0PadOrient,
      pad_orient_pkg::MioPadIoa8PadOrient,
      pad_orient_pkg::MioPadIoa7PadOrient,
      pad_orient_pkg::MioPadIoa6PadOrient,
      pad_orient_pkg::MioPadIoa5PadOrient,
      pad_orient_pkg::MioPadIoa4PadOrient,
      pad_orient_pkg::MioPadIoa3PadOrient,
      pad_orient_pkg::MioPadIoa2PadOrient,
      pad_orient_pkg::MioPadIoa1PadOrient,
      pad_orient_pkg::MioPadIoa0PadOrient
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
      IoBankVcc, // RRAM_ANALOG
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
      AnalogIn0, // RRAM_ANALOG
      BidirTol, // CC2
      BidirTol, // CC1
      DualBidirTol, // USB_N
      DualBidirTol, // USB_P
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
      RRAM_ANALOG,
`ifdef ANALOGSIM
      '0,
`else
      CC2,
`endif
`ifdef ANALOGSIM
      '0,
`else
      CC1,
`endif
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
        manual_in_rram_analog,
        manual_in_cc2,
        manual_in_cc1,
        manual_in_usb_n,
        manual_in_usb_p,
        manual_in_por_n
      }),
    .dio_out_i ({
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
        manual_out_rram_analog,
        manual_out_cc2,
        manual_out_cc1,
        manual_out_usb_n,
        manual_out_usb_p,
        manual_out_por_n
      }),
    .dio_oe_i ({
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
        manual_oe_rram_analog,
        manual_oe_cc2,
        manual_oe_cc1,
        manual_oe_usb_n,
        manual_oe_usb_p,
        manual_oe_por_n
      }),
    .dio_attr_i ({
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
        manual_attr_rram_analog,
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

  assign manual_out_rram_analog = 1'b0;
  assign manual_oe_rram_analog = 1'b0;

  // Enable schmitt trigger on POR for better signal integrity.
  assign manual_attr_por_n = '{schmitt_en: 1'b1, pull_en: 1'b1, pull_select: 1'b1, default: '0};

  // These pad attributes are controlled through sensor_ctrl.  Update the description of
  // `MANUAL_PAD_ATTR` in `sensor_ctrl.hjson` when you change or extend the mapping below.
  prim_pad_wrapper_pkg::pad_attr_t [3:0] sensor_ctrl_manual_pad_attr;
  assign manual_attr_cc1 = sensor_ctrl_manual_pad_attr[0];
  assign manual_attr_cc2 = sensor_ctrl_manual_pad_attr[1];

  // Indices 2 and 3 used to map to FLASH_TEST_MODE0/1, which no longer exist
  // now that flash_ctrl has been removed from this top.
  logic unused_sensor_ctrl_manual_pad_attr;
  assign unused_sensor_ctrl_manual_pad_attr = ^{
    sensor_ctrl_manual_pad_attr[2],
    sensor_ctrl_manual_pad_attr[3]
  };

  // These pad attributes are currently tied off permanently (these are supply pads).
  assign manual_attr_rram_analog = '0;

  logic unused_manual_sigs;
  assign unused_manual_sigs = ^{
    manual_in_cc2,
    manual_in_cc1,
    manual_in_rram_analog
  };

  ///////////////////////////////
  // Differential USB Receiver //
  ///////////////////////////////

  // TODO: generalize this USB mux code and align with other tops.

  // Connect the D+ pad
  // Note that we use two pads in parallel for the D+ channel to meet electrical specifications.
  assign dio_in[DioUsbdevUsbDp] = manual_in_usb_p;
  assign manual_out_usb_p = dio_out[DioUsbdevUsbDp];
  assign manual_oe_usb_p = dio_oe[DioUsbdevUsbDp];
  assign manual_attr_usb_p = dio_attr[DioUsbdevUsbDp];

  // Connect the D- pads
  // Note that we use two pads in parallel for the D- channel to meet electrical specifications.
  assign dio_in[DioUsbdevUsbDn] = manual_in_usb_n;
  assign manual_out_usb_n = dio_out[DioUsbdevUsbDn];
  assign manual_oe_usb_n = dio_oe[DioUsbdevUsbDn];
  assign manual_attr_usb_n = dio_attr[DioUsbdevUsbDn];

  logic usb_rx_d;

  // Pullups and differential receiver enable
  logic usb_dp_pullup_en, usb_dn_pullup_en;
  logic usb_rx_enable;

  logic usb_diff_rx_obs;
  logic [ast_pkg::UsbCalibWidth-1:0] usb_io_pu_cal;

  prim_usb_diff_rx #(
    .CalibW(ast_pkg::UsbCalibWidth)
  ) u_prim_usb_diff_rx (
    .input_pi         (USB_P             ),
    .input_ni         (USB_N             ),
    .input_en_i       (usb_rx_enable     ),
    .core_pok_h_i     (ast_pwst_h.aon_pok),
    .pullup_p_en_i    (usb_dp_pullup_en  ),
    .pullup_n_en_i    (usb_dn_pullup_en  ),
    .calibration_i    (usb_io_pu_cal     ),
    .usb_diff_rx_obs_o(usb_diff_rx_obs   ),
    .input_o          (usb_rx_d          )
  );


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

  // external clock comes in at a fixed position
  assign clk_ast_ext = mio_in_raw[MioPadIoc6];

  // Bypass clocks are irrelevant for asic
  assign clks_osc_byp = '0;

  // Raw pad signals required by the ast
  assign padmux2ast = `PAD2AST_WIRES ;


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
    usb_obs: usb_diff_rx_obs
  };

  // Feed the same bypass struct to both PDs. This is a limitation as topgen cannot distribute the
  // same external signal to multiple IP ports from the top. The 'top' signals are local to their
  // power domain. Note these are only relevant for FPGA and verilator. But we always connect them
  // as topgen does not support conditional port generation.
  ast_pkg::clks_osc_byp_t clk_osc_byp_pd_main;
  ast_pkg::clks_osc_byp_t clk_osc_byp_pd_aon;
  assign clk_osc_byp_pd_main = clks_osc_byp;
  assign clk_osc_byp_pd_aon  = clks_osc_byp;

  // Unused AST power states
  logic unused_ast_pwst_h;
  assign unused_ast_pwst_h = ^{ast_pwst_h.vcc_pok,
                               ast_pwst_h.main_pok,
                               ast_pwst_h.io_pok};
  ///////////////////////////////////////
  // top_earlgrey: power domains //
  ///////////////////////////////////////
  top_earlgrey #(
    .I2c0InputDelayCycles(1),
    .I2c1InputDelayCycles(1),
    .I2c2InputDelayCycles(1),
    .SecAesAllowForcingMasks(1'b1),
    .SecRomCtrlDisableScrambling(SecRomCtrlDisableScrambling),
    .PinmuxTargetCfg(PinmuxTargetCfg)
  ) top_earlgrey (
    // Unmanaged external clocks
    .clk_ast_ext_i  (clk_ast_ext),
    .cg_en_ast_ext_i(cg_en_ast_ext),

    // Manual DFT signals
    .padring_scan_clk_o(padring_scan_clk),

    // Multiplexed I/O
    .mio_in_i (mio_in ),
    .mio_out_o(mio_out),
    .mio_oe_o (mio_oe ),

    // Dedicated I/O
    .dio_in_i (dio_in ),
    .dio_out_o(dio_out),
    .dio_oe_o (dio_oe ),

    // Pad attributes
    .mio_attr_o(mio_attr),
    .dio_attr_o(dio_attr),

    // Regular ports (auto-generated)
    .manual_in_por_n_i            (manual_in_por_n    ),
    .scanmode_o                   (scanmode           ),
    .scan_en_o                    (                   ),
    .scan_rst_n_o                 (                   ),
    .usb_io_pu_cal_o              (usb_io_pu_cal      ),
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
    .usb_dn_pullup_en_o           (usb_dn_pullup_en   ),
    .rram_test_analog_io          (RRAM_ANALOG        ),
    .fpga_info_i                  ('0                 ),
    .sensor_ctrl_manual_pad_attr_o(sensor_ctrl_manual_pad_attr),
    .usbdev_usb_rx_d_i            (usb_rx_d           ),
    .usbdev_usb_tx_d_o            (                   ),
    .usbdev_usb_tx_se0_o          (                   ),
    .usbdev_usb_tx_use_d_se0_o    (                   ),
    .usbdev_usb_rx_enable_o       (usb_rx_enable      )
  );

endmodule
