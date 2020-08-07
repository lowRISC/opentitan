// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module top_earlgrey_asic (
  // Clock and Reset
  // TODO: remove the IO_CLK port once AST contains an oscillator model. a calibration clock
  // will then be muxed in via another port.
  inout               IO_CLK,
  inout               IO_RST_N,
  // Bank A (VIOA domain)
  inout               SPI_HOST_D0,
  inout               SPI_HOST_D1,
  inout               SPI_HOST_D2,
  inout               SPI_HOST_D3,
  inout               SPI_HOST_CLK,
  inout               SPI_HOST_CS_L,
  inout               SPI_DEV_D0,
  inout               SPI_DEV_D1,
  inout               SPI_DEV_D2,
  inout               SPI_DEV_D3,
  inout               SPI_DEV_CLK,
  inout               SPI_DEV_CS_L,
  inout               IOA0,  // MIO 0
  inout               IOA1,  // MIO 1
  inout               IOA2,  // MIO 2
  inout               IOA3,  // MIO 3
  inout               IOA4,  // MIO 4
  inout               IOA5,  // MIO 5
  // Bank B (VIOB domain)
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
  // Bank C (VCC domain)
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
  // Bank R (VCC domain)
  inout               IOR0,  // MIO 30
  inout               IOR1,  // MIO 31
  inout               IOR2,  // MIO 32
  inout               IOR3,  // MIO 33
  inout               IOR4,  // MIO 34
  inout               IOR5,  // MIO 35
  inout               IOR6,  // MIO 36
  inout               IOR7,  // MIO 37
  inout               IOR8,  // MIO 38
  inout               IOR9,  // MIO 39
  inout               IOR10, // MIO 40
  inout               IOR11, // MIO 41
  inout               IOR12, // MIO 42
  inout               IOR13, // MIO 43
  // DCD (VCC domain)
  inout               CC1,
  inout               CC2,
  // USB (VCC domain)
  inout               USB_P,
  inout               USB_N,
  // FLASH
  inout [3:0]         FLASH_TEST_MODE,
  inout               FLASH_TEST_VOLT

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
  wire unused_spi_device_s2, unused_spi_device_s3;

  padring #(
    // All MIOs are connected
    .ConnectMioIn  ( 44'hFFF_FFFF_FFFF ),
    .ConnectMioOut ( 44'hFFF_FFFF_FFFF ),
    // Tied off DIOs:
    // 2-8 (USB)
    .ConnectDioIn  ( 21'h1FFE03 ),
    .ConnectDioOut ( 21'h1FFE03 ),
    // MIO pad types
    .MioPadVariant ( { // RBox
                       2'd3, // IOR13   -- open drain
                       2'd3, // IOR12   -- open drain
                       2'd3, // IOR11   -- open drain
                       2'd3, // IOR10   -- open drain
                       2'd3, // IOR9    -- open drain
                       2'd3, // IOR8    -- open drain
                       2'd0, // IOR7    -- bidir
                       2'd0, // IOR6    -- bidir
                       2'd0, // IOR5    -- bidir
                       2'd0, // IOR4    -- bidir
                       2'd0, // IOR3    -- bidir
                       2'd0, // IOR2    -- bidir
                       2'd0, // IOR1    -- bidir
                       2'd0, // IOR0    -- bidir
                       // Bank C
                       2'd3, // IOC11   -- open drain
                       2'd3, // IOC10   -- open drain
                       2'd3, // IOC9    -- open drain
                       2'd3, // IOC8    -- open drain
                       2'd0, // IOC7    -- bidir
                       2'd0, // IOC6    -- bidir
                       2'd0, // IOC5    -- bidir
                       2'd0, // IOC4    -- bidir
                       2'd0, // IOC3    -- bidir
                       2'd0, // IOC2    -- bidir
                       2'd0, // IOC1    -- bidir
                       2'd0, // IOC0    -- bidir
                       // Bank B
                       2'd3, // IOB11   -- open drain
                       2'd3, // IOB10   -- open drain
                       2'd3, // IOB9    -- open drain
                       2'd3, // IOB8    -- open drain
                       2'd0, // IOB7    -- birid
                       2'd0, // IOB6    -- birid
                       2'd0, // IOB5    -- birid
                       2'd0, // IOB4    -- birid
                       2'd0, // IOB3    -- bidir
                       2'd0, // IOB2    -- bidir
                       2'd0, // IOB1    -- bidir
                       2'd0, // IOB0    -- bidir
                       // Bank A
                       2'd3, // IOA5    -- open drain
                       2'd3, // IOA4    -- open drain
                       2'd0, // IOA3    -- bidir
                       2'd0, // IOA2    -- bidir
                       2'd0, // IOA1    -- bidir
                       2'd0  // IOA0    -- bidir
                      } ),
    // DIO pad types
    .DioPadVariant (  { 2'd1, // SPI_DEV_CLK    -- input only
                        2'd1, // SPI_DEV_CS_L   -- input only
                        2'd0, // SPI_DEV_D3     -- bidir
                        2'd0, // SPI_DEV_D2     -- bidir
                        2'd0, // SPI_DEV_D1     -- bidir
                        2'd0, // SPI_DEV_D0     -- bidir
                        2'd0, // SPI_HOST_CLK   -- bidir
                        2'd0, // SPI_HOST_CS_L  -- bidir
                        2'd0, // SPI_HOST_D3    -- bidir
                        2'd0, // SPI_HOST_D2    -- bidir
                        2'd0, // SPI_HOST_D1    -- bidir
                        2'd0, // SPI_HOST_D0    -- bidir
                        2'd0, // unused
                        2'd0, // unused
                        2'd0, // unused
                        2'd0, // unused
                        2'd0, // unused
                        2'd0, // unused
                        2'd0, // unused
                        2'd2, // USB_P          -- tolerant
                        2'd2  // USB_N          -- tolerant
                      } )
  ) u_padring (
    // Clk / Rst
    .clk_pad_i           ( IO_CLK           ),
    .rst_pad_ni          ( IO_RST_N         ),
    .clk_o               ( clk              ),
    .rst_no              ( rst_n            ),
    .cc1_i               ( CC1              ),
    .cc2_i               ( CC2              ),
    // "special"
    // MIO Pads
    .mio_pad_io          ( { // RBox
                             IOR13, // MIO 43
                             IOR12, // MIO 42
                             IOR11, // MIO 41
                             IOR10, // MIO 40
                             IOR9,  // MIO 39
                             IOR8,  // MIO 38
                             IOR7,  // MIO 37
                             IOR6,  // MIO 36
                             IOR5,  // MIO 35
                             IOR4,  // MIO 34
                             IOR3,  // MIO 33
                             IOR2,  // MIO 32
                             IOR1,  // MIO 31
                             IOR0,  // MIO 30
                             // Bank C
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
                             IOA5,  // MIO 5
                             IOA4,  // MIO 4
                             IOA3,  // MIO 3
                             IOA2,  // MIO 2
                             IOA1,  // MIO 1
                             IOA0   // MIO 0
                            } ),
    // DIO Pads
    .dio_pad_io          ( { SPI_DEV_CLK,                 // cio_spi_device_sck_p2d
                             SPI_DEV_CS_L,                // cio_spi_device_csb_p2d
                             SPI_DEV_D3,                  // cio_spi_device_s_p2d[3]
                             SPI_DEV_D2,                  // cio_spi_device_s_p2d[2]
                             SPI_DEV_D1,                  // cio_spi_device_s_p2d[1]
                             SPI_DEV_D0,                  // cio_spi_device_s_p2d[0]
                             SPI_HOST_CLK,                // cio_spi_host0_sck_p2d
                             SPI_HOST_CS_L,               // cio_spi_host0_csb_p2d
                             SPI_HOST_D3,                 // cio_spi_host0_s_p2d[3]
                             SPI_HOST_D2,                 // cio_spi_host0_s_p2d[2]
                             SPI_HOST_D1,                 // cio_spi_host0_s_p2d[1]
                             SPI_HOST_D0,                 // cio_spi_host0_s_p2d[0]
                             unused_usbdev_aon_sense,     // cio_usbdev_aon_sense_p2d
                             unused_usbdev_se0,           // cio_usbdev_aon_se0
                             unused_usbdev_dp_pullup_en,  // cio_usbdev_aon_dp_pullup
                             unused_usbdev_dn_pullup_en,  // cio_usbdev_aon_dn_pullup
                             unused_usbdev_tx_mode,       // cio_usbdev_aon_tx_mode_se
                             unused_usbdev_suspend,       // cio_usbdev_aon_suspend
                             unused_usbdev_d,             // cio_usbdev_aon_d_p2d
                             USB_P,                       // cio_usbdev_aon_dp_p2d
                             USB_N                        // cio_usbdev_aon_dn_p2d
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

  ///////////////////////////////
  // Differential USB Receiver //
  ///////////////////////////////

  logic usbdev_aon_usb_rx_enable;
  logic usb_pullup_p_en;
  logic usb_pullup_n_en;
  logic usb_diff_input;

  logic ast_usb_core_pok;
  logic [31:0] ast_usb_calibration;
  logic [ast_wrapper_pkg::UsbCalibWidth-1:0] usb_io_pu_cal;

  prim_usb_diff_rx #(
    .CalibW(ast_wrapper_pkg::UsbCalibWidth)
  ) i_prim_usb_diff_rx (
    .input_pi      ( USB_P                    ),
    .input_ni      ( USB_N                    ),
    .input_en_i    ( usbdev_aon_usb_rx_enable ),
    .core_pok_i    ( ast_usb_core_pok         ),
    .pullup_p_en_i ( usb_pullup_p_en          ),
    .pullup_n_en_i ( usb_pullup_n_en          ),
    .calibration_i ( usb_io_pu_cal            ),
    .input_o       ( usb_diff_input           )
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
    .NumIOs         ( NumIOs       ),
    .TieOffValues   ( TieOffValues ),
    .JtagEnIdx      (           25 ), // IOC7 -- MIO 25
    .JtagEnPolarity (            1 ),
    .TckIdx         (           33 ), // IOR3 -- MIO 33
    .TmsIdx         (           30 ), // IOR0 -- MIO 30
    .TrstIdx        (           34 ), // IOR4 -- MIO 34
    .SrstIdx        (           35 ), // IOR5 -- MIO 35
    .TdiIdx         (           32 ), // IOR2 -- MIO 32
    .TdoIdx         (           31 ), // IOR1 -- MIO 31
    .UsbDpPuIdx     ( padctrl_reg_pkg::NMioPads +
                      top_earlgrey_pkg::TopEarlgreyDioPinUsbdevAonDpPullup ),
    .UsbDnPuIdx     ( padctrl_reg_pkg::NMioPads +
                      top_earlgrey_pkg::TopEarlgreyDioPinUsbdevAonDnPullup ),
    .UsbDIdx        ( padctrl_reg_pkg::NMioPads +
                      top_earlgrey_pkg::TopEarlgreyDioPinUsbdevAonD )
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
    .in_padring_i  ( {dio_in_padring , mio_in_padring } ),
    // USB breakouts
    .usb_pullup_p_en_o ( usb_pullup_p_en ),
    .usb_pullup_n_en_o ( usb_pullup_n_en ),
    .usb_diff_input_i  ( usb_diff_input  )
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
  ast_wrapper_pkg::ast_eflash_t ast_base_eflash;
  pwrmgr_pkg::pwr_ast_req_t base_ast_pwr;
  pwrmgr_pkg::pwr_ast_rsp_t ast_base_pwr;
  ast_wrapper_pkg::ast_func_clks_rsts base_ast_aux;
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
    .status_o(ast_base_status),
    .usb_io_pu_cal_o(usb_io_pu_cal),
    .ast_eflash_o(ast_base_eflash),
    .scanmode_i(1'b0),
    .scan_reset_ni(1'b1)
  );

  assign ast_usb_core_pok = ast_base_rst.aon_pok;

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
    .aux_o                           ( base_ast_aux         ),
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
    .entropy_src_entropy_src_rng_req ( base_ast_entropy_src ),
    .entropy_src_entropy_src_rng_rsp ( ast_base_entropy_src ),
    .pinmux_aon_io_pok               ( ast_base_status      ),
    .ast_eflash_i                    ( ast_base_eflash      ),

    // USB signals
    .usbdev_aon_usb_rx_enable,

    // flash ports
    .flash_test_mode_ai              ( FLASH_TEST_MODE      ),
    .flash_test_voltage_hi           ( FLASH_TEST_VOLT      ),

    // DFT signals
    .scan_rst_ni     ( 1'b1          ),
    .scanmode_i      ( 1'b0          )
  );

endmodule : top_earlgrey_asic
