// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_earlgrey/data/top_earlgrey.hjson \
//                -o hw/top_earlgrey/ \
//                --rnd_cnst_seed \
//                1017106219537032642877583828875051302543807092889754935647094601236425074047


module chip_earlgrey_cw340 #(
  // Path to a VMEM file containing the contents of the boot ROM, which will be
  // baked into the FPGA bitstream.
  parameter BootRomInitFile = "test_rom_fpga_cw340.32.vmem",
  // Path to a VMEM file containing the contents of the emulated OTP, which will be
  // baked into the FPGA bitstream.
  parameter OtpCtrlMemInitFile = "otp_img_fpga_cw340.vmem"
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
  inout IOR8, // Dedicated Pad for sysrst_ctrl_aon_ec_rst_l
  inout IOR9, // Dedicated Pad for sysrst_ctrl_aon_flash_wp_l
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
  localparam int Dft0PadIdx = 25;
  localparam int Dft1PadIdx = 26;
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
  logic [24-1:0]                       dio_in_raw;
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_out;
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_oe;
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_in;

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

  /////////////////////////
  // Stubbed pad tie-off //
  /////////////////////////

  // Only signals going to non-custom pads need to be tied off.
  logic [69:0] unused_sig;

  //////////////////////
  // Padring Instance //
  //////////////////////

  ast_pkg::ast_clks_t ast_base_clks;


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
    .clk_scan_i   ( 1'b0                  ),
    .scanmode_i   ( prim_mubi_pkg::MuBi4False ),
    .dio_in_raw_o ( dio_in_raw ),
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
  logic usb_dn_pullup_en;
  logic usb_rx_d;
  logic usb_tx_d;
  logic usb_tx_se0;
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
    usb_dn_pullup_en,
    usb_tx_d,
    usb_tx_se0,
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
  prim_ram_2p_pkg::ram_2p_cfg_t spi_ram_2p_cfg;
  prim_ram_2p_pkg::ram_2p_cfg_t usb_ram_2p_cfg;
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

  // this maps as follows:
  // assign usb_ram_2p_cfg = {10'h000, ram_2p_cfg_i.a_ram_fcfg, ram_2p_cfg_i.b_ram_fcfg};
  assign usb_ram_2p_cfg = '{
    a_ram_lcfg: '{
                   cfg_en: ast_ram_2p_fcfg.marg_en_a,
                   cfg:    ast_ram_2p_fcfg.marg_a
                 },
    b_ram_lcfg: '{
                   cfg_en: ast_ram_2p_fcfg.marg_en_b,
                   cfg:    ast_ram_2p_fcfg.marg_b
                 },
    default: '0
  };

  // this maps as follows:
  // assign spi_ram_2p_cfg = {10'h000, ram_2p_cfg_i.a_ram_lcfg, ram_2p_cfg_i.b_ram_lcfg};
  assign spi_ram_2p_cfg = '{
    a_ram_lcfg: '{
                   cfg_en: ast_ram_2p_lcfg.marg_en_a,
                   cfg:    ast_ram_2p_lcfg.marg_a
                 },
    b_ram_lcfg: '{
                   cfg_en: ast_ram_2p_lcfg.marg_en_b,
                   cfg:    ast_ram_2p_lcfg.marg_b
                 },
    default: '0
  };

  assign rom_cfg = '{
    cfg_en: ast_rom_cfg.marg_en,
    cfg: ast_rom_cfg.marg
  };


  //////////////////////////////////
  // AST - Custom for targets     //
  //////////////////////////////////


  assign ast_base_pwr.main_pok = ast_pwst.main_pok;

  logic [rstmgr_pkg::PowerDomains-1:0] por_n;
  assign por_n = {ast_pwst.main_pok, ast_pwst.aon_pok};

  // TODO: Hook this up when FPGA pads are updated
  assign ext_clk = '0;
  assign pad2ast = '0;

  logic clk_main, clk_io, clk_usb_48mhz, clk_aon, rst_n;
  clkgen_xil_ultrascale # (
    .AddClkBuf(0)
  ) clkgen (
    .clk_i(manual_in_io_clk),
    .rst_ni(manual_in_por_n),
    .clk_main_o(clk_main),
    .clk_io_o(clk_io),
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
    io:  clk_io,
    aon: clk_aon
  };


  prim_mubi_pkg::mubi4_t ast_init_done;

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
    .clk_ast_tlul_i (clkmgr_aon_clocks.clk_io_div4_infra),
    .clk_ast_adc_i (clkmgr_aon_clocks.clk_aon_peri),
    .clk_ast_alert_i (clkmgr_aon_clocks.clk_io_div4_secure),
    .clk_ast_es_i (clkmgr_aon_clocks.clk_main_secure),
    .clk_ast_rng_i (clkmgr_aon_clocks.clk_main_secure),
    .clk_ast_usb_i (clkmgr_aon_clocks.clk_usb_peri),
    .rst_ast_tlul_ni (rstmgr_aon_resets.rst_lc_io_div4_n[rstmgr_pkg::Domain0Sel]),
    .rst_ast_adc_ni (rstmgr_aon_resets.rst_lc_aon_n[rstmgr_pkg::DomainAonSel]),
    .rst_ast_alert_ni (rstmgr_aon_resets.rst_lc_io_div4_n[rstmgr_pkg::Domain0Sel]),
    .rst_ast_es_ni (rstmgr_aon_resets.rst_lc_n[rstmgr_pkg::Domain0Sel]),
    .rst_ast_rng_ni (rstmgr_aon_resets.rst_lc_n[rstmgr_pkg::Domain0Sel]),
    .rst_ast_usb_ni (rstmgr_aon_resets.rst_usb_n[rstmgr_pkg::Domain0Sel]),
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

  assign manual_attr_io_clk = '0;
  assign manual_out_io_clk = 1'b0;
  assign manual_oe_io_clk = 1'b0;
  assign manual_attr_por_n = '0;
  assign manual_out_por_n = 1'b0;
  assign manual_oe_por_n = 1'b0;


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
    .SecAesMasking(1'b1),
    .SecAesSBoxImpl(aes_pkg::SBoxImplDom),
    .SecAesStartTriggerDelay(320),
    .SecAesAllowForcingMasks(1'b1),
    .KmacEnMasking(0),
    .KmacSwKeyMasked(1),
    .SecKmacCmdDelay(320),
    .SecKmacIdleAcceptSwMsg(1'b1),
    .KeymgrKmacEnMasking(0),
    .CsrngSBoxImpl(aes_pkg::SBoxImplLut),
    .OtbnRegFile(otbn_pkg::RegFileFPGA),
    .SecOtbnMuteUrnd(1'b1),
    .SecOtbnSkipUrndReseedAtStart(1'b1),
    .OtpCtrlMemInitFile(OtpCtrlMemInitFile),
    .RvCoreIbexPipeLine(1),
    .SramCtrlRetAonInstrExec(0),
    .UsbdevRcvrWakeTimeUs(10000),
    .RomCtrlBootRomInitFile(BootRomInitFile),
    .RvCoreIbexRegFile(ibex_pkg::RegFileFPGA),
    .RvCoreIbexSecureIbex(0),
    .SramCtrlMainInstrExec(1),
    .PinmuxAonTargetCfg(PinmuxTargetCfg)
  ) top_earlgrey (
    .por_n_i                      ( por_n                 ),
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
    .otp_obs_o                    ( otp_obs                    ),
    .sensor_ctrl_ast_alert_req_i  ( ast_alert_req              ),
    .sensor_ctrl_ast_alert_rsp_o  ( ast_alert_rsp              ),
    .sensor_ctrl_ast_status_i     ( ast_pwst.io_pok            ),
    .es_rng_req_o                 ( es_rng_req                 ),
    .es_rng_rsp_i                 ( es_rng_rsp                 ),
    .es_rng_fips_o                ( es_rng_fips                ),
    .ast2pinmux_i                 ( ast2pinmux                 ),
    .calib_rdy_i                  ( ast_init_done              ),
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
    .spi_ram_2p_cfg_i( '0 ),
    .usb_ram_2p_cfg_i( '0 ),
    .rom_cfg_i       ( '0 ),

    // DFT signals
    .dft_hold_tap_sel_i ( '0               ),
    .scan_rst_ni        ( 1'b1             ),
    .scan_en_i          ( 1'b0             ),
    .scanmode_i         ( prim_mubi_pkg::MuBi4False )
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
  // We use the clkmgr_aon_idle signal of the IP of interest to form a precise capture trigger.
  // GPIO[11:10] is used for selecting the IP of interest. The encoding is as follows (see
  // hint_names_e enum in clkmgr_pkg.sv for details).
  //
  // IP              - GPIO[11:10] - Index for clkmgr_aon_idle
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
  assign clk_trans_idle = top_earlgrey.clkmgr_aon_idle[trigger_sel];

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

endmodule : chip_earlgrey_cw340
