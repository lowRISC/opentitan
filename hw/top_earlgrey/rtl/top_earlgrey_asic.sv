// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module top_earlgrey_asic (
  // Clock and Reset
  // TODO: remove the IO_CLK port once AST contains an oscillator model. a calibration clock
  // will then be muxed in via another port.
  inout               IO_CLK,
  inout               IO_RST_N,
  // Bank A
  inout               IOA0,  // SPI Host Data 0
  inout               IOA1,  // SPI Host Data 1
  inout               IOA2,  // SPI Host Data 2
  inout               IOA3,  // SPI Host Data 3
  inout               IOA4,  // SPI Host CS_L
  inout               IOA5,  // SPI Host CLK
  inout               IOA6,  // SPI Device HIDO
  inout               IOA7,  // SPI Device HODI
  inout               IOA8,  // SPI Device CS_L
  inout               IOA9,  // SPI Device CLK
  inout               IOA10, // MIO 0
  inout               IOA11, // MIO 1
  inout               IOA12, // MIO 2
  inout               IOA13, // MIO 3
  inout               IOA14, // MIO 4
  inout               IOA15, // MIO 5
  // Bank B
  inout               IOB0,  // MIO 6
  inout               IOB1,  // MIO 7
  inout               IOB2,  // MIO 8
  inout               IOB3,  // MIO 9
  inout               IOB4,  // MIO 10
  inout               IOB5,  // MIO 11
  inout               IOB6,  // MIO 12
  inout               IOB7,  // MIO 13
  inout               IOB8,  // MIO 14
  inout               IOB9,  // MIO 15
  inout               IOB10, // MIO 16
  inout               IOB11, // MIO 17
  // Bank C
  inout               IOC0,  // MIO 18
  inout               IOC1,  // MIO 19
  inout               IOC2,  // MIO 20
  inout               IOC3,  // MIO 21
  inout               IOC4,  // MIO 22
  inout               IOC5,  // MIO 23
  inout               IOC6,  // MIO 24
  inout               IOC7,  // MIO 25
  inout               IOC8,  // MIO 26
  inout               IOC9,  // MIO 27
  inout               IOC10, // MIO 28
  inout               IOC11, // MIO 29
  inout               IOC12, // MIO 30
  inout               IOC13, // MIO 31
  inout               IOC14, // MIO 32
  inout               IOC15, // CC1
  inout               IOC16, // CC2
  inout               IOC17, // USB_P
  inout               IOC18, // USB_N
  // Bank R
  inout               IOR0,  // EcRstL
  inout               IOR1,  // PwrBI
  inout               IOR2,  // EcEnteringRw
  inout               IOR3,  // AcPresent
  inout               IOR4,  // FlashWpL
  inout               IOR5,  // PwrBO
  inout               IOR6,  // EcInRw
  inout               IOR7,  // BatEn
  inout               IOR8,  // Key0I (volup, column out from EC in laptop)
  inout               IOR9,  // Key1I (voldown, row input from keyboard matrix in laptop)
  inout               IOR10, // Key2I (tbd, row input from keyboard matrix in laptop)
  inout               IOR11, // Key0O (passthrough from Key0I)
  inout               IOR12, // Key1O (passthrough from Key1I)
  inout               IOR13  // Key2O (passthrough from Key2I)
);

  import top_earlgrey_pkg::*;

  ////////////////////////
  // Signal definitions //
  ////////////////////////

  //////////////////////
  // Padring Instance //
  //////////////////////

  logic clk, rst_n;
  logic [padctrl_reg_pkg::NMioPads-1:0][padctrl_reg_pkg::AttrDw-1:0] mio_attr;
  logic [padctrl_reg_pkg::NDioPads-1:0][padctrl_reg_pkg::AttrDw-1:0] dio_attr;
  logic [padctrl_reg_pkg::NMioPads-1:0] mio_out_core, mio_out_padring;
  logic [padctrl_reg_pkg::NMioPads-1:0] mio_oe_core, mio_oe_padring;
  logic [padctrl_reg_pkg::NMioPads-1:0] mio_in_core, mio_in_padring;
  logic [padctrl_reg_pkg::NDioPads-1:0] dio_out_core, dio_out_padring;
  logic [padctrl_reg_pkg::NDioPads-1:0] dio_oe_core, dio_oe_padring;
  logic [padctrl_reg_pkg::NDioPads-1:0] dio_in_core, dio_in_padring;

  // unused pad signals. need to hook these wires up since lint does not like module ports that are
  // tied to 1'bz.
  wire unused_usbdev_se0, unused_usbdev_tx_mode, unused_usbdev_suspend;
  wire unused_usbdev_d, unused_usbdev_aon_sense;
  wire unused_usbdev_dp_pullup_en, unused_usbdev_dn_pullup_en;

  // TODO: hook these up once both the SPI host and device are present
  logic [3:0] unused_spi;
  assign unused_spi = {IOA9, IOA8, IOA7, IOA6};
  assign {IOA9, IOA8, IOA7, IOA6} = '0;

  padring #(
    // All MIOs are connected
    .ConnectMioIn  ( 47'h7FFF_FFFF_FFFF ),
    .ConnectMioOut ( 47'h7FFF_FFFF_FFFF ),
    // Tied off DIOs:
    // 2-8 (USB)
    .ConnectDioIn  ( 15'h7E03 ),
    .ConnectDioOut ( 15'h7E03 ),
    // MIO pad types
    .MioPadVariant ( { // RBox
                       2'd0, // IOR13   -- bidir
                       2'd0, // IOR12   -- bidir
                       2'd0, // IOR11   -- bidir
                       2'd0, // IOR10   -- bidir
                       2'd0, // IOR9    -- bidir
                       2'd0, // IOR8    -- bidir
                       2'd3, // IOR7    -- open drain
                       2'd3, // IOR6    -- open drain
                       2'd3, // IOR5    -- open drain
                       2'd3, // IOR4    -- open drain
                       2'd3, // IOR3    -- open drain
                       2'd0, // IOR2    -- bidir
                       2'd3, // IOR1    -- open drain
                       2'd3, // IOR0    -- open drain
                       // Bank C
                       2'd0, // IOC14   -- bidir
                       2'd0, // IOC13   -- bidir
                       2'd0, // IOC12   -- bidir
                       2'd0, // IOC11   -- bidir
                       2'd0, // IOC10   -- bidir
                       2'd3, // IOC9    -- open drain
                       2'd0, // IOC8    -- bidir
                       2'd3, // IOC7    -- open drain
                       2'd3, // IOC6    -- open drain
                       2'd3, // IOC5    -- open drain
                       2'd0, // IOC4    -- bidir
                       2'd0, // IOC3    -- bidir
                       2'd0, // IOC2    -- bidir
                       2'd0, // IOC1    -- bidir
                       2'd0, // IOC0    -- bidir
                       // Bank B
                       2'd0, // IOB11   -- bidir
                       2'd0, // IOB10   -- bidir
                       2'd0, // IOB9    -- bidir
                       2'd0, // IOB8    -- bidir
                       2'd3, // IOB7    -- open drain
                       2'd3, // IOB6    -- open drain
                       2'd3, // IOB5    -- open drain
                       2'd3, // IOB4    -- open drain
                       2'd0, // IOB3    -- bidir
                       2'd0, // IOB2    -- bidir
                       2'd0, // IOB1    -- bidir
                       2'd0, // IOB0    -- bidir
                       // Bank A
                       2'd0, // IOA15   -- bidir
                       2'd0, // IOA14   -- bidir
                       2'd0, // IOA13   -- bidir
                       2'd0, // IOA12   -- bidir
                       2'd3, // IOA11   -- open drain
                       2'd3  // IOA10   -- open drain
                      } ),
    // DIO pad types
    .DioPadVariant ( { 2'd0, // IOA4     -- bidir
                       2'd0, // IOA5     -- bidir
                       2'd0, // IOA3     -- bidir
                       2'd0, // IOA2     -- bidir
                       2'd0, // IOA1     -- bidir
                       2'd0, // IOA0     -- bidir
                       2'd0, // unused
                       2'd0, // unused
                       2'd0, // IOC15    -- bidir
                       2'd0, // IOC16    -- bidir
                       2'd0, // unused
                       2'd0, // unused
                       2'd0, // unused
                       2'd2, // USB_P   -- tolerant
                       2'd2  // USB_N   -- tolerant
                      } )
  ) padring (
    // Clk / Rst
    .clk_pad_i           ( IO_CLK           ),
    .rst_pad_ni          ( IO_RST_N         ),
    .clk_o               ( clk              ),
    .rst_no              ( rst_n            ),
    .cc1_i               ( IOC15            ),
    .cc2_i               ( IOC16            ),
    // "special"
    // MIO Pads
    .mio_pad_io          ( { // RBox
                             IOR13, // MIO 46
                             IOR12, // MIO 45
                             IOR11, // MIO 44
                             IOR10, // MIO 43
                             IOR9,  // MIO 42
                             IOR8,  // MIO 41
                             IOR7,  // MIO 40
                             IOR6,  // MIO 39
                             IOR5,  // MIO 38
                             IOR4,  // MIO 37
                             IOR3,  // MIO 36
                             IOR2,  // MIO 35
                             IOR1,  // MIO 34
                             IOR0,  // MIO 33
                             // Bank C
                             IOC14, // MIO 32
                             IOC13, // MIO 31
                             IOC12, // MIO 30
                             IOC11, // MIO 29
                             IOC10, // MIO 28
                             IOC9,  // MIO 27
                             IOC8,  // MIO 26
                             IOC7,  // MIO 25
                             IOC6,  // MIO 24
                             IOC5,  // MIO 23
                             IOC4,  // MIO 22
                             IOC3,  // MIO 21
                             IOC2,  // MIO 20
                             IOC1,  // MIO 19
                             IOC0,  // MIO 18
                             // Bank B
                             IOB11, // MIO 17
                             IOB10, // MIO 16
                             IOB9,  // MIO 15
                             IOB8,  // MIO 14
                             IOB7,  // MIO 13
                             IOB6,  // MIO 12
                             IOB5,  // MIO 11
                             IOB4,  // MIO 10
                             IOB3,  // MIO 9
                             IOB2,  // MIO 8
                             IOB1,  // MIO 7
                             IOB0,  // MIO 6
                             // Bank A
                             IOA15, // MIO 5
                             IOA14, // MIO 4
                             IOA13, // MIO 3
                             IOA12, // MIO 2
                             IOA11, // MIO 1
                             IOA10  // MIO 0
                            } ),
    // DIO Pads
    // TODO: the SPI mapping is not correct since the SPI host is missing, and we still need
    // to free up 2 pads to squeeze in a 4x SPI device.
    .dio_pad_io          ( { IOA5, // cio_spi_device_sck_p2d
                             IOA4, // cio_spi_device_csb_p2d
                             IOA3, // cio_spi_device_s_p2d[3]
                             IOA2, // cio_spi_device_s_p2d[2]
                             IOA1, // cio_spi_device_s_p2d[1]
                             IOA0, // cio_spi_device_s_p2d[0]
                             unused_usbdev_aon_sense, //usbdev_aon_sense
                             unused_usbdev_se0, // usbdev_se0
                             unused_usbdev_dp_pullup_en,  // USB dp pullup
                             unused_usbdev_dn_pullup_en,  // USB dn pullup
                             unused_usbdev_tx_mode, // usbdev_tx_mode
                             unused_usbdev_suspend, // usbdev_suspend
                             unused_usbdev_d,       // usbdev_d
                             IOC17,  // USB_P
                             IOC18   // USB_N
                           } ),
    // Muxed IOs
    .mio_in_o            ( mio_in_padring   ),
    .mio_out_i           ( mio_out_padring  ),
    .mio_oe_i            ( mio_oe_padring   ),
    // Dedicated IOs
    .dio_in_o            ( dio_in_padring   ),
    .dio_out_i           ( dio_out_padring  ),
    .dio_oe_i            ( dio_oe_padring   ),
    // Pad Attributes
    .mio_attr_i          ( mio_attr         ),
    .dio_attr_i          ( dio_attr         )
  );

  //////////////////////
  // JTAG Overlay Mux //
  //////////////////////

  logic jtag_trst_n, jtag_srst_n;
  logic jtag_tck, jtag_tms, jtag_tdi, jtag_tdo;

  localparam int NumIOs = padctrl_reg_pkg::NMioPads +
                          padctrl_reg_pkg::NDioPads;

  // This specifies the tie-off values of the muxed MIO/DIOs
  // when the JTAG is active. SPI CSB is active low.
  localparam logic [NumIOs-1:0] TieOffValues =NumIOs'(1'b1 << (
      padctrl_reg_pkg::NMioPads + top_earlgrey_pkg::TopEarlgreyDioPinSpiDeviceCsb));

  // TODO: this is a temporary solution. JTAG will eventually be selected and
  // qualified inside the pinmux, based on strap and lifecycle state.
  // Parameterizeable JTAG overlay mux.
  // Unaffected indices are just passed through.
  jtag_mux #(
    .NumIOs         (                   NumIOs       ),
    .TieOffValues   (                   TieOffValues ),
    .JtagEnIdx      (                             30 ), // MIO 30
    .JtagEnPolarity (                              1 ),
    .TckIdx         ( padctrl_reg_pkg::NMioPads +
                      top_earlgrey_pkg::TopEarlgreyDioPinSpiDeviceSck ),
    .TmsIdx         ( padctrl_reg_pkg::NMioPads +
                      top_earlgrey_pkg::TopEarlgreyDioPinSpiDeviceCsb ),
    .TrstIdx        (                             9  ), // MIO 9
    .SrstIdx        (                             10 ), // MIO 10
    .TdiIdx         ( padctrl_reg_pkg::NMioPads +
                      top_earlgrey_pkg::TopEarlgreyDioPinSpiDeviceS0 ),
    .TdoIdx         ( padctrl_reg_pkg::NMioPads +
                      top_earlgrey_pkg::TopEarlgreyDioPinSpiDeviceS1 )
  ) jtag_mux (
    // To JTAG inside core
    .jtag_tck_o   ( jtag_tck        ),
    .jtag_tms_o   ( jtag_tms        ),
    .jtag_trst_no ( jtag_trst_n     ),
    .jtag_srst_no ( jtag_srst_n     ),
    .jtag_tdi_o   ( jtag_tdi        ),
    .jtag_tdo_i   ( jtag_tdo        ),
    // To core side
    .out_core_i   ( {dio_out_core, mio_out_core} ),
    .oe_core_i    ( {dio_oe_core,  mio_oe_core}  ),
    .in_core_o    ( {dio_in_core,  mio_in_core}  ),
    // To padring side
    .out_padring_o ( {dio_out_padring, mio_out_padring} ),
    .oe_padring_o  ( {dio_oe_padring , mio_oe_padring } ),
    .in_padring_i  ( {dio_in_padring , mio_in_padring } )
  );

  //////////////////////
  // AST              //
  //////////////////////
  tlul_pkg::tl_h2d_t base_ast_bus;
  tlul_pkg::tl_d2h_t ast_base_bus;
  ast_wrapper_pkg::ast_status_t ast_base_status;
  ast_wrapper_pkg::ast_alert_req_t ast_base_alerts;
  ast_wrapper_pkg::ast_alert_rsp_t base_ast_alerts;
  ast_wrapper_pkg::ast_rst_t ast_base_rst;
  ast_wrapper_pkg::ast_clks_t ast_base_clks;
  pwrmgr_pkg::pwr_ast_req_t base_ast_pwr;
  pwrmgr_pkg::pwr_ast_rsp_t ast_base_pwr;
  sensor_ctrl_pkg::ast_aux_t base_ast_aux;
  entropy_src_pkg::entropy_src_rng_req_t base_ast_entropy_src;
  entropy_src_pkg::entropy_src_rng_rsp_t ast_base_entropy_src;
  logic usb_ref_pulse;
  logic usb_ref_val;

  ast_wrapper ast_wrapper (
    .clk_ext_i(clk),
    .por_ni(rst_n),
    .bus_i(base_ast_bus),
    .bus_o(ast_base_bus),
    .pwr_i(base_ast_pwr),
    .pwr_o(ast_base_pwr),
    .rst_o(ast_base_rst),
    .clks_o(ast_base_clks),
    .usb_ref_pulse_i(usb_ref_pulse),
    .usb_ref_val_i(usb_ref_val),
    .aux_i(base_ast_aux),
    .adc_i('0),
    .adc_o(),
    .es_i(base_ast_entropy_src),
    .es_o(ast_base_entropy_src),
    .alert_i(base_ast_alerts),
    .alert_o(ast_base_alerts),
    .status_o(ast_base_status)
  );


  //////////////////////
  // Top-level design //
  //////////////////////

  top_earlgrey top_earlgrey (
    .rst_ni              ( rst_n                 ),
    .clkmgr_aon_clk_main ( ast_base_clks.clk_sys ),
    .clkmgr_aon_clk_io   ( ast_base_clks.clk_io  ),
    .clkmgr_aon_clk_usb  ( ast_base_clks.clk_usb ),
    .clkmgr_aon_clk_aon  ( ast_base_clks.clk_aon ),

    // JTAG
    .jtag_tck_i      ( jtag_tck      ),
    .jtag_tms_i      ( jtag_tms      ),
    .jtag_trst_ni    ( jtag_trst_n   ),
    .jtag_tdi_i      ( jtag_tdi      ),
    .jtag_tdo_o      ( jtag_tdo      ),

    // Multiplexed I/O
    .mio_in_i        ( mio_in_core   ),
    .mio_out_o       ( mio_out_core  ),
    .mio_oe_o        ( mio_oe_core   ),

    // Dedicated I/O
    .dio_in_i        ( dio_in_core   ),
    .dio_out_o       ( dio_out_core  ),
    .dio_oe_o        ( dio_oe_core   ),

    // Pad attributes
    .mio_attr_o      ( mio_attr      ),
    .dio_attr_o      ( dio_attr      ),

    // AST connections
    .sensor_ctrl_ast_host            ( base_ast_bus         ),
    .sensor_ctrl_ast_dev             ( ast_base_bus         ),
    .sensor_ctrl_ast_status          ( ast_base_status      ),
    .sensor_ctrl_ast_alert_req       ( ast_base_alerts      ),
    .sensor_ctrl_ast_alert_rsp       ( base_ast_alerts      ),
    .pwrmgr_aon_pwr_ast_req          ( base_ast_pwr         ),
    .pwrmgr_aon_pwr_ast_rsp          ( ast_base_pwr         ),
    .rstmgr_aon_ast                  ( ast_base_rst         ),
    .usbdev_aon_usb_ref_pulse        ( usb_ref_pulse        ),
    .usbdev_aon_usb_ref_val          ( usb_ref_val          ),
    .sensor_ctrl_ast_aux             ( base_ast_aux         ),
    .entropy_src_entropy_src_rng_req ( base_ast_entropy_src ),
    .entropy_src_entropy_src_rng_rsp ( ast_base_entropy_src ),

    // DFT signals
    .scan_rst_ni     ( 1'b1          ),
    .scanmode_i      ( 1'b0          )
  );

endmodule : top_earlgrey_asic
