// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module top_earlgrey_asic (
  // Clock and Reset
  inout               IO_CLK,
  inout               IO_RST_N,
  inout               IO_CLK_USB_48MHZ,
  // JTAG interface
  inout               IO_DPS0, // IO_JTCK,    IO_SDCK
  inout               IO_DPS3, // IO_JTMS,    IO_SDCSB
  inout               IO_DPS1, // IO_JTDI,    IO_SDSDI
  inout               IO_DPS4, // IO_JTRST_N,
  inout               IO_DPS5, // IO_JSRST_N,
  inout               IO_DPS2, // IO_JTDO,    IO_SDO
  inout               IO_DPS6, // JTAG=1,     SPI=0
  inout               IO_DPS7, // BOOTSTRAP=1
  // UART interface
  inout               IO_URX,
  inout               IO_UTX,
  // USB interface
  inout               IO_USB_DP0,
  inout               IO_USB_DN0,
  inout               IO_USB_SENSE0,
  inout               IO_USB_DNPULLUP0,
  inout               IO_USB_DPPULLUP0,
  // GPIO x 16 interface
  inout               IO_GP0,
  inout               IO_GP1,
  inout               IO_GP2,
  inout               IO_GP3,
  inout               IO_GP4,
  inout               IO_GP5,
  inout               IO_GP6,
  inout               IO_GP7,
  inout               IO_GP8,
  inout               IO_GP9,
  inout               IO_GP10,
  inout               IO_GP11,
  inout               IO_GP12,
  inout               IO_GP13,
  inout               IO_GP14,
  inout               IO_GP15
);

  import top_earlgrey_pkg::*;

  //////////////////////
  // Padring Instance //
  //////////////////////

  logic clk, clk_usb_48mhz, rst_n;
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
  wire unused_usbdev_se0, unused_usbdev_tx_mode, unused_usbdev_suspend, unused_usbdev_d;
  wire [11:0] unused_mio;

  padring #(
    // MIOs 31:20 are currently not
    // connected to pads and hence tied off
    .ConnectMioIn  ( 32'h000FFFFF ),
    .ConnectMioOut ( 32'h000FFFFF ),
    // Tied off DIOs:
    // 2: usbdev_d
    // 3: usbdev_suspend
    // 4: usbdev_tx_mode
    // 7: usbdev_se
    .ConnectDioIn  ( 15'h7F63 ),
    .ConnectDioOut ( 15'h7F63 ),
    // Pad types
    .MioPadVariant ( '0 ),
    .DioPadVariant ( '0 )
  ) padring (
    // Clk / Rst
    .clk_pad_i           ( IO_CLK           ),
    .clk_usb_48mhz_pad_i ( IO_CLK_USB_48MHZ ),
    .rst_pad_ni          ( IO_RST_N         ),
    .clk_o               ( clk              ),
    .clk_usb_48mhz_o     ( clk_usb_48mhz    ),
    .rst_no              ( rst_n            ),
    // MIO Pads
    .mio_pad_io          ( { unused_mio, // Note that 31:20 are currently not mapped
                             IO_DPS5,    // Use GPIO19 to pass JTAG_SRST
                             IO_DPS4,    // Use GPIO18 to pass JTAG_TRST
                             IO_DPS7,    // Use GPIO17 to pass rom boot_strap indication
                             IO_DPS6,    // Use GPIO16 to pass SPI/JTAG control flag
                             IO_GP15,
                             IO_GP14,
                             IO_GP13,
                             IO_GP12,
                             IO_GP11,
                             IO_GP10,
                             IO_GP9,
                             IO_GP8,
                             IO_GP7,
                             IO_GP6,
                             IO_GP5,
                             IO_GP4,
                             IO_GP3,
                             IO_GP2,
                             IO_GP1,
                             IO_GP0 } ),
    // DIO Pads
    .dio_pad_io          ( { IO_DPS0, // SCK, JTAG_TCK
                             IO_DPS3, // CSB, JTAG_TMS
                             IO_DPS1, // SDI, JTAG_TDI
                             IO_DPS2, // SDO, JTAG_TDO
                             IO_URX,
                             IO_UTX,
                             IO_USB_SENSE0,
                             unused_usbdev_se0, // usbdev_se0
                             IO_USB_DPPULLUP0,
                             IO_USB_DNPULLUP0,
                             unused_usbdev_tx_mode, // usbdev_tx_mode
                             unused_usbdev_suspend, // usbdev_suspend
                             unused_usbdev_d,       // usbdev_d
                             IO_USB_DP0,
                             IO_USB_DN0 } ),
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
                      top_earlgrey_pkg::TopEarlgreyDioPinSpiDeviceSdi ),
    .TdoIdx         ( pinmux_reg_pkg::NMioPads +
                      top_earlgrey_pkg::TopEarlgreyDioPinSpiDeviceSdo )
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
    .usb_io_pu_cal_o       ( ),
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
    .dft_strap_test_i      ( '{valid: 1'b0, straps: 2'b00} ),
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
