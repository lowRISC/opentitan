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
  logic [pinmux_reg_pkg::NMioPads-1:0][pinmux_reg_pkg::AttrDw-1:0] mio_attr;
  logic [pinmux_reg_pkg::NDioPads-1:0][pinmux_reg_pkg::AttrDw-1:0] dio_attr;
  logic [pinmux_reg_pkg::NMioPads-1:0] mio_out_core, mio_out_padring;
  logic [pinmux_reg_pkg::NMioPads-1:0] mio_oe_core, mio_oe_padring;
  logic [pinmux_reg_pkg::NMioPads-1:0] mio_in_core, mio_in_padring;
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_out_core, dio_out_padring;
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_oe_core, dio_oe_padring;
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_in_core, dio_in_padring;

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
  logic [ast_pkg::UsbCalibWidth-1:0] usb_io_pu_cal;

  // TODO: overhaul these USB connections
  assign usbdev_aon_usb_rx_enable = 1'b0;

  prim_usb_diff_rx #(
    .CalibW(ast_pkg::UsbCalibWidth)
  ) u_prim_usb_diff_rx (
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

  localparam int NumIOs = pinmux_reg_pkg::NMioPads +
                          pinmux_reg_pkg::NDioPads;

  // This specifies the tie-off values of the muxed MIO/DIOs
  // when the JTAG is active. SPI CSB is active low.
  localparam logic [NumIOs-1:0] TieOffValues =NumIOs'(1'b1 << (
      pinmux_reg_pkg::NMioPads + top_earlgrey_pkg::TopEarlgreyDioPinSpiDeviceCsb));

  // TODO: this is a temporary solution. JTAG will eventually be selected and
  // qualified inside the pinmux, based on strap and lifecycle state.
  // Parameterizeable JTAG overlay mux.
  // Unaffected indices are just passed through.
  jtag_mux #(
    .NumIOs         (                   NumIOs       ),
    .TieOffValues   (                   TieOffValues ),
    .JtagEnIdx      (                             16 ), // MIO 16
    .JtagEnPolarity (                              1 ),
    .TckIdx         ( pinmux_reg_pkg::NMioPads +
                      top_earlgrey_pkg::TopEarlgreyDioPinSpiDeviceSck ),
    .TmsIdx         ( pinmux_reg_pkg::NMioPads +
                      top_earlgrey_pkg::TopEarlgreyDioPinSpiDeviceCsb ),
    .TrstIdx        (                             18 ), // MIO 18
    .SrstIdx        (                             19 ), // MIO 19
    .TdiIdx         ( pinmux_reg_pkg::NMioPads +
                      top_earlgrey_pkg::TopEarlgreyDioPinSpiDeviceSd0 ),
    .TdoIdx         ( pinmux_reg_pkg::NMioPads +
                      top_earlgrey_pkg::TopEarlgreyDioPinSpiDeviceSd1 ),
    .UsbDpPuIdx     ( pinmux_reg_pkg::NMioPads +
                      top_earlgrey_pkg::TopEarlgreyDioPinUsbdevDpPullup ),
    .UsbDnPuIdx     ( pinmux_reg_pkg::NMioPads +
                      top_earlgrey_pkg::TopEarlgreyDioPinUsbdevDnPullup ),
    .UsbDIdx        ( pinmux_reg_pkg::NMioPads +
                      top_earlgrey_pkg::TopEarlgreyDioPinUsbdevD ),
    .ConnectUSB     (1)
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
  // TLUL interface
  tlul_pkg::tl_h2d_t base_ast_bus;
  tlul_pkg::tl_d2h_t ast_base_bus;

  // assorted ast status
  ast_pkg::ast_status_t ast_status;

  // ast clocks and resets
  ast_pkg::ast_rst_t ast_base_rst;
  ast_pkg::ast_clks_t ast_base_clks;

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
  lc_ctrl_pkg::lc_tx_t lc_ast_clk_byp_req;
  lc_ctrl_pkg::lc_tx_t lc_ast_clk_byp_ack;

  // DFT connections
  logic scan_rst_n;
  logic scan_en;
  lc_ctrl_pkg::lc_tx_t scanmode;

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
  import rstmgr_pkg::DomainAonSel;
  import rstmgr_pkg::Domain0Sel;

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
    .clk_ast_adc_i         ( 1'b0 ),
    .rst_ast_adc_ni        ( 1'b0 ),
    .clk_ast_alert_i       ( clks_ast.clk_ast_sensor_ctrl_aon_io_div4_secure ),
    .rst_ast_alert_ni      ( rsts_ast.rst_ast_sensor_ctrl_aon_sys_io_div4_n[DomainAonSel] ),
    .clk_ast_es_i          ( clks_ast.clk_ast_edn0_main_secure ),
    .rst_ast_es_ni         ( rsts_ast.rst_ast_edn0_sys_n[Domain0Sel] ),
    .clk_ast_rng_i         ( clks_ast.clk_ast_entropy_src_main_secure ),
    .rst_ast_rng_ni        ( rsts_ast.rst_ast_entropy_src_sys_n[Domain0Sel] ),
    .clk_ast_tlul_i        ( clks_ast.clk_ast_sensor_ctrl_aon_io_div4_secure ),
    .rst_ast_tlul_ni       ( rsts_ast.rst_ast_sensor_ctrl_aon_sys_io_div4_n[DomainAonSel] ),
    .clk_ast_usb_i         ( clks_ast.clk_ast_usbdev_usb_peri ),
    .rst_ast_usb_ni        ( rsts_ast.rst_ast_usbdev_usb_n[Domain0Sel] ),
    .clk_ast_ext_i         ( clk ),
    .por_ni                ( rst_n ),
    // pok test for FPGA
    .vcc_supp_i            ( 1'b1 ),
    .vcaon_supp_i          ( 1'b1 ),
    .vcmain_supp_i         ( 1'b1 ),
    .vioa_supp_i           ( 1'b1 ),
    .viob_supp_i           ( 1'b1 ),
    // pok
    .vcaon_pok_o           ( ast_base_rst.aon_pok ),
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
    // TODO: Connect to do adc_ctrl when instantiated
    .adc_pd_i              ( '0 ),
    .adc_a0_ai             ( '0 ),
    .adc_a1_ai             ( '0 ),
    .adc_chnsel_i          ( '0 ),
    .adc_d_o               (  ),
    .adc_d_val_o           (  ),
    // rng
    .rng_en_i              ( es_rng_req.rng_enable ),
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
    .dft_strap_test_i      ( '0               ),
    .lc_dft_en_i           ( lc_ctrl_pkg::Off ),
    // pad mux related
    //TODO: Connect to pinmux
    .padmux2ast_i          ( '0 ),
    .ast2padmux_o          ( ),
    //TODO: Connect to PAD
    .pad2ast_t0_ai         ( '0 ),
    .pad2ast_t1_ai         ( '0 ),
    .ast2pad_t0_ao         ( ),
    .ast2pad_t1_ao         ( ),
    .lc_clk_byp_req_i      ( lc_ast_clk_byp_req ),
    .lc_clk_byp_ack_o      ( lc_ast_clk_byp_ack ),
    .flash_bist_en_o       ( flash_bist_enable  ),
    //TODO: Connect to memories
    .dpram_rmf_o           ( ),
    .dpram_rml_o           ( ),
    .spram_rm_o            ( ),
    .sprgf_rm_o            ( ),
    .sprom_rm_o            ( ),
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
    .KmacReuseShare(0)
  ) top_earlgrey (
    .rst_ni                       ( rst_n                      ),
    // ast connections
    .clk_main_i                   ( ast_base_clks.clk_sys      ),
    .clk_io_i                     ( ast_base_clks.clk_io       ),
    .clk_usb_i                    ( ast_base_clks.clk_usb      ),
    .clk_aon_i                    ( ast_base_clks.clk_aon      ),
    .clks_ast_o                   ( clks_ast                   ),
    .clk_main_jitter_en_o         ( jen                        ),
    .rstmgr_ast_i                 ( ast_base_rst               ),
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
    .ast_edn_edn_req_i            ( ast_edn_edn_req            ),
    .ast_edn_edn_rsp_o            ( ast_edn_edn_rsp            ),
    .otp_ctrl_otp_ast_pwr_seq_o   ( otp_ctrl_otp_ast_pwr_seq   ),
    .otp_ctrl_otp_ast_pwr_seq_h_i ( otp_ctrl_otp_ast_pwr_seq_h ),
    .flash_bist_enable_i          ( flash_bist_enable          ),
    .flash_power_down_h_i         ( flash_power_down_h         ),
    .flash_power_ready_h_i        ( flash_power_ready_h        ),
    .es_rng_req_o                 ( es_rng_req                 ),
    .es_rng_rsp_i                 ( es_rng_rsp                 ),
    .lc_clk_byp_req_o             ( lc_ast_clk_byp_req         ),
    .lc_clk_byp_ack_i             ( lc_ast_clk_byp_ack         ),
    // TODO: connect these
    .flash_test_mode_a_i          ('0                          ),
    .flash_test_voltage_h_i       ('0                          ),
    // JTAG
    .jtag_tck_i                   ( jtag_tck                   ),
    .jtag_tms_i                   ( jtag_tms                   ),
    .jtag_trst_ni                 ( jtag_trst_n                ),
    .jtag_tdi_i                   ( jtag_tdi                   ),
    .jtag_tdo_o                   ( jtag_tdo                   ),

    // Multiplexed I/O
    .mio_in_i                     ( mio_in_core                ),
    .mio_out_o                    ( mio_out_core               ),
    .mio_oe_o                     ( mio_oe_core                ),

    // Dedicated I/O
    .dio_in_i                     ( dio_in_core                ),
    .dio_out_o                    ( dio_out_core               ),
    .dio_oe_o                     ( dio_oe_core                ),

    // Pad attributes
    .mio_attr_o                   ( mio_attr                   ),
    .dio_attr_o                   ( dio_attr                   ),

    // DFT signals
    .scan_rst_ni                  ( scan_rst_n                 ),
    .scan_en_i                    ( scan_en                    ),
    .scanmode_i                   ( scanmode                   )
  );

endmodule : top_earlgrey_asic
