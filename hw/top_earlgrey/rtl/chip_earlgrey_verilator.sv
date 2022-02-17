// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module chip_earlgrey_verilator (
  // Clock and Reset
  input clk_i,
  input rst_ni,

  // communication with GPIO
  input [31:0] cio_gpio_p2d_i,
  output logic [31:0] cio_gpio_d2p_o,
  output logic [31:0] cio_gpio_en_d2p_o,

  // communication with UART
  input cio_uart_rx_p2d_i,
  output logic cio_uart_tx_d2p_o,
  output logic cio_uart_tx_en_d2p_o,

  // communication with SPI
  input cio_spi_device_sck_p2d_i,
  input cio_spi_device_csb_p2d_i,
  input cio_spi_device_sdi_p2d_i,
  output logic cio_spi_device_sdo_d2p_o,
  output logic cio_spi_device_sdo_en_d2p_o,

  // communication with USB
  input cio_usbdev_sense_p2d_i,
  output logic cio_usbdev_dp_pullup_d2p_o,
  output logic cio_usbdev_dp_pullup_en_d2p_o,
  output logic cio_usbdev_dn_pullup_d2p_o,
  output logic cio_usbdev_dn_pullup_en_d2p_o,
  input cio_usbdev_dp_p2d_i,
  output logic cio_usbdev_dp_d2p_o,
  output logic cio_usbdev_dp_en_d2p_o,
  input cio_usbdev_dn_p2d_i,
  output logic cio_usbdev_dn_d2p_o,
  output logic cio_usbdev_dn_en_d2p_o,
  input cio_usbdev_d_p2d_i,
  output logic cio_usbdev_d_d2p_o,
  output logic cio_usbdev_d_en_d2p_o,
  output logic cio_usbdev_se0_d2p_o,
  output logic cio_usbdev_se0_en_d2p_o,
  output logic cio_usbdev_tx_mode_se_d2p_o,
  output logic cio_usbdev_tx_mode_se_en_d2p_o
);

  import top_earlgrey_pkg::*;


  logic IO_JTCK, IO_JTMS, IO_JTRST_N, IO_JTDI, IO_JTDO;

  // TODO: instantiate padring and route these signals through that module
  logic [pinmux_pkg::NDioPads-1:0] dio_in;
  logic [pinmux_pkg::NDioPads-1:0] dio_out;
  logic [pinmux_pkg::NDioPads-1:0] dio_oe;

  always_comb begin : assign_dio_in
    dio_in = '0;
    dio_in[DioSpiDeviceSck] = cio_spi_device_sck_p2d_i;
    dio_in[DioSpiDeviceCsb] = cio_spi_device_csb_p2d_i;
    dio_in[DioSpiDeviceSd0] = cio_spi_device_sdi_p2d_i;
    dio_in[DioUsbdevD] = cio_usbdev_d_p2d_i;
    dio_in[DioUsbdevDp] = cio_usbdev_dp_p2d_i;
    dio_in[DioUsbdevDn] = cio_usbdev_dn_p2d_i;
  end

  assign cio_usbdev_dn_d2p_o = dio_out[DioUsbdevDn];
  assign cio_usbdev_dp_d2p_o = dio_out[DioUsbdevDp];
  assign cio_usbdev_d_d2p_o  = dio_out[DioUsbdevD];
  assign cio_usbdev_suspend_d2p_o = dio_out[DioUsbdevSuspend];
  assign cio_usbdev_tx_mode_se_d2p_o = dio_out[DioUsbdevTxModeSe];
  assign cio_usbdev_dn_pullup_d2p_o = dio_out[DioUsbdevDnPullup];
  assign cio_usbdev_dp_pullup_d2p_o = dio_out[DioUsbdevDpPullup];
  assign cio_usbdev_se0_d2p_o = dio_out[DioUsbdevSe0];
  assign cio_spi_device_sdo_d2p_o = dio_out[DioSpiDeviceSd1];

  assign cio_usbdev_dn_en_d2p_o = dio_oe[DioUsbdevDn];
  assign cio_usbdev_dp_en_d2p_o = dio_oe[DioUsbdevDp];
  assign cio_usbdev_d_en_d2p_o  = dio_oe[DioUsbdevD];
  assign cio_usbdev_suspend_en_d2p_o = dio_oe[DioUsbdevSuspend];
  assign cio_usbdev_tx_mode_se_en_d2p_o = dio_oe[DioUsbdevTxModeSe];
  assign cio_usbdev_dn_pullup_en_d2p_o = dio_oe[DioUsbdevDnPullup];
  assign cio_usbdev_dp_pullup_en_d2p_o = dio_oe[DioUsbdevDpPullup];
  assign cio_usbdev_se0_en_d2p_o = dio_oe[DioUsbdevSe0];
  assign cio_spi_device_sdo_en_d2p_o = dio_oe[DioSpiDeviceSd1];

  logic [pinmux_pkg::NMioPads-1:0] mio_in;
  logic [pinmux_pkg::NMioPads-1:0] mio_out;
  logic [pinmux_pkg::NMioPads-1:0] mio_oe;

  always_comb begin : assign_mio_in
    mio_in = '0;
    mio_in[31:0] = cio_gpio_p2d_i;
    mio_in[25] = cio_uart_rx_p2d_i;
    mio_in[35] = cio_usbdev_sense_p2d_i;
    mio_in[36] = cio_usbdev_sense_p2d_i;
  end

  assign cio_gpio_d2p_o[25:0]       = mio_out[25:0];
  assign cio_gpio_en_d2p_o[25:0]    = mio_oe[25:0];
  assign cio_gpio_d2p_o[31:27]      = mio_out[31:27];
  assign cio_gpio_en_d2p_o[31:27]   = mio_oe[31:27];
  assign cio_uart_tx_d2p_o    = mio_out[26];
  assign cio_uart_tx_en_d2p_o = mio_oe[26];

  ////////////////////////////////
  // AST - Custom for Verilator //
  ////////////////////////////////
  ast_pkg::ast_pwst_t ast_pwst;
  ast_pkg::ast_pwst_t ast_pwst_h;

  // pwrmgr interface
  pwrmgr_pkg::pwr_ast_req_t base_ast_pwr;
  pwrmgr_pkg::pwr_ast_rsp_t ast_base_pwr;

  ast_pkg::ast_clks_t ast_base_clks;

  // external clock comes in at a fixed position
  logic ext_clk;
  assign ext_clk = '0;

  logic [ast_pkg::Pad2AstInWidth-1:0] pad2ast;
  assign pad2ast = '0;

  logic clk_aon;
  // reset is not used below becuase verilator uses only sync resets
  // and also does not under 'x'.
  // if we allow the divider below to reset, clk_aon will be silenced,
  // and as a result all the clk_aon logic inside top_earlgrey does not
  // get reset
  prim_clock_div #(
    .Divisor(4)
  ) u_aon_div (
    .clk_i,
    .rst_ni(1'b1),
    .step_down_req_i('0),
    .step_down_ack_o(),
    .test_en_i('0),
    .clk_o(clk_aon)
  );

  ast_pkg::clks_osc_byp_t clks_osc_byp;
  assign clks_osc_byp = '{
    usb: clk_i,
    sys: clk_i,
    io:  clk_i,
    aon: clk_aon
  };

  ///////////////////////////////////////
  // AST - Common with other platforms //
  ///////////////////////////////////////

  // platform specific supply manipulation to create POR
  logic [3:0] cnt;
  logic vcc_supp;

  // keep incrementing until saturation
  always_ff @(posedge clk_aon) begin
    if (cnt < 4'hf) begin
      cnt <= cnt + 1'b1;
    end
  end

  // create fake por condition
  assign vcc_supp = cnt < 4'h4 ? 1'b0 :
                    cnt < 4'h8 ? 1'b1 :
                    cnt < 4'hc ? 1'b0 : 1'b1;

  // TLUL interface
  tlul_pkg::tl_h2d_t base_ast_bus;
  tlul_pkg::tl_d2h_t ast_base_bus;

  assign ast_base_pwr.main_pok = ast_pwst.main_pok;

  // synchronization clocks / rests
  clkmgr_pkg::clkmgr_out_t clkmgr_aon_clocks;
  rstmgr_pkg::rstmgr_out_t rstmgr_aon_resets;

  // monitored clock
  logic sck_monitor;

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

  // Life cycle clock bypass req/ack
  prim_mubi_pkg::mubi4_t all_clk_byp_req;
  prim_mubi_pkg::mubi4_t all_clk_byp_ack;
  prim_mubi_pkg::mubi4_t io_clk_byp_req;
  prim_mubi_pkg::mubi4_t io_clk_byp_ack;
  logic hi_speed_sel;


  // DFT connections
  logic scan_en;
  lc_ctrl_pkg::lc_tx_t dft_en;
  pinmux_pkg::dft_strap_test_req_t dft_strap_test;

  // Debug connections
  logic [ast_pkg::Ast2PadOutWidth-1:0] ast2pinmux;

  // Jitter enable
  logic jen;

  // reset domain connections
  import rstmgr_pkg::PowerDomains;
  import rstmgr_pkg::DomainAonSel;
  import rstmgr_pkg::Domain0Sel;

  // AST does not use all clocks / resets forwarded to it
  logic unused_slow_clk_en;
  assign unused_slow_clk_en = base_ast_pwr.slow_clk_en;

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
    // different between verilator and other platforms
    .clk_ast_ext_i         ( clk_i ),
    .por_ni                ( rst_ni ),
    // USB IO Pull-up Calibration Setting
    .usb_io_pu_cal_o       (  ),
    // adc
    .adc_a0_ai             ( '0 ),
    .adc_a1_ai             ( '0 ),
    // Direct short to PAD
    .ast2pad_t0_ao         (  ),
    .ast2pad_t1_ao         (  ),
    // Memory configuration connections
    .dpram_rmf_o           (  ),
    .dpram_rml_o           (  ),
    .spram_rm_o            (  ),
    .sprgf_rm_o            (  ),
    .sprom_rm_o            (  ),
    // clocks' oschillator bypass for FPGA
    .clk_osc_byp_i         ( clks_osc_byp ),


    // clocks and resets supplied for detection
    .sns_clks_i      ( clkmgr_aon_clocks    ),
    .sns_rsts_i      ( rstmgr_aon_resets    ),
    .sns_spi_ext_clk_i ( sck_monitor          ),
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
    .rst_ast_adc_ni (rstmgr_aon_resets.rst_sys_aon_n[rstmgr_pkg::Domain0Sel]),
    .rst_ast_alert_ni (rstmgr_aon_resets.rst_lc_io_div4_n[rstmgr_pkg::Domain0Sel]),
    .rst_ast_es_ni (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel]),
    .rst_ast_rng_ni (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel]),
    .rst_ast_usb_ni (rstmgr_aon_resets.rst_usbif_n[rstmgr_pkg::Domain0Sel]),

    // pok test for FPGA
    .vcc_supp_i            ( vcc_supp ),
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
    .clk_src_io_48m_o      (  ),
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
    .fla_obs_i             ( '0 ),
    .otp_obs_i             ( '0 ),
    .otm_obs_i             ( '0 ),
    .usb_obs_i             ( '0 ),
    .obs_ctrl_o            (  ),
    // pinmux related
    .padmux2ast_i          ( pad2ast    ),
    .ast2padmux_o          ( ast2pinmux ),
    .ext_freq_is_96m_i     ( hi_speed_sel ),
    .all_clk_byp_req_i     ( ast_clk_byp_req ),
    .all_clk_byp_ack_o     ( ast_clk_byp_ack ),
    .io_clk_byp_req_i      ( io_clk_byp_req   ),
    .io_clk_byp_ack_o      ( io_clk_byp_ack   ),
    .flash_bist_en_o       ( flash_bist_enable ),
    // scan
    .dft_scan_md_o         ( scanmode ),
    .scan_shift_en_o       ( scan_en ),
    .scan_reset_no         ( scan_rst_n )
  );


  // TODO: generate these indices from the target-specific
  // pinout configuration. But first, this verilator top needs
  // to be split into a Verilator TB and a Verilator chiplevel.
  // DFT and Debug signal positions in the pinout.
  localparam pinmux_pkg::target_cfg_t PinmuxTargetCfg = '{
    tck_idx:        pinmux_reg_pkg::NMioPads +
                    top_earlgrey_pkg::DioSpiDeviceSck,
    tms_idx:        pinmux_reg_pkg::NMioPads +
                    top_earlgrey_pkg::DioSpiDeviceCsb,
    trst_idx:       18, // MIO 18
    tdi_idx:        pinmux_reg_pkg::NMioPads +
                    top_earlgrey_pkg::DioSpiDeviceSd0,
    tdo_idx:        pinmux_reg_pkg::NMioPads +
                    top_earlgrey_pkg::DioSpiDeviceSd1,
    tap_strap0_idx: 26, // MIO 26
    tap_strap1_idx: 16, // MIO 16 (this is different in the ASIC top)
    dft_strap0_idx: 21, // MIO 21
    dft_strap1_idx: 22, // MIO 22
    // TODO: check whether there is a better way to pass these USB-specific params
    usb_dp_idx:        DioUsbdevDp,
    usb_dn_idx:        DioUsbdevDn,
    usb_dp_pullup_idx: DioUsbdevDpPullup,
    usb_dn_pullup_idx: DioUsbdevDnPullup,
    usb_sense_idx:     MioInUsbdevSense,
    // TODO: connect these once the verilator chip-level has been merged with the chiplevel.sv.tpl
    dio_pad_type: {pinmux_reg_pkg::NDioPads{prim_pad_wrapper_pkg::BidirStd}},
    mio_pad_type: {pinmux_reg_pkg::NMioPads{prim_pad_wrapper_pkg::BidirStd}}
  };

  prim_mubi_pkg::mubi4_t lc_clk_bypass;


  // Top-level design

  logic [rstmgr_pkg::PowerDomains-1:0] por_n;
  assign por_n = {ast_pwst.main_pok, ast_pwst.aon_pok};

  top_earlgrey #(
    .SramCtrlRetAonInstrExec(0),
    .SramCtrlMainInstrExec(1),
    .PinmuxAonTargetCfg(PinmuxTargetCfg)
  ) top_earlgrey (
    // update por / reset connections, this is not quite right here
    .por_n_i                      (por_n             ),
    .clk_main_i                   (clk_i             ),
    .clk_io_i                     (clk_i             ),
    .clk_usb_i                    (clk_i             ),
    .clk_aon_i                    (clk_aon           ),
    // change the above
    .clks_ast_o                   (clkmgr_aon_clocks ),
    .clk_main_jitter_en_o         ( jen              ),
    .rsts_ast_o                   ( rstmgr_aon_resets),
    .sck_monitor_o                ( sck_monitor      ),
    .pwrmgr_ast_req_o             ( base_ast_pwr     ),
    .pwrmgr_ast_rsp_i             ( ast_base_pwr     ),
    .sensor_ctrl_ast_alert_req_i  ( ast_alert_req    ),
    .sensor_ctrl_ast_alert_rsp_o  ( ast_alert_rsp    ),
    .sensor_ctrl_ast_status_i     ( ast_pwst.io_pok  ),
    .usbdev_usb_ref_val_o         ( usb_ref_val      ),
    .usbdev_usb_ref_pulse_o       ( usb_ref_pulse    ),
    .ast_tl_req_o                 ( base_ast_bus     ),
    .ast_tl_rsp_i                 ( ast_base_bus     ),
    .adc_req_o                    ( adc_req          ),
    .adc_rsp_i                    ( adc_rsp          ),
    .ast_edn_req_i                ( ast_edn_edn_req  ),
    .ast_edn_rsp_o                ( ast_edn_edn_rsp  ),
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
    .all_clk_byp_req_o            ( all_clk_byp_req            ),
    .all_clk_byp_ack_i            ( all_clk_byp_ack            ),
    .io_clk_byp_req_o             ( io_clk_byp_req             ),
    .io_clk_byp_ack_i             ( io_clk_byp_ack             ),
    .hi_speed_sel_o               ( hi_speed_sel               ),
    .ast2pinmux_i                 ( ast2pinmux                 ),
    .ast_init_done_i              ( ast_init_done              ),

    // Flash test mode voltages
    .flash_test_mode_a_io         ( ),
    .flash_test_voltage_h_io      ( ),

    // OTP external voltage
    .otp_ext_voltage_h_io         ( ),

    // Multiplexed I/O
    .mio_in_i                     (mio_in),
    .mio_out_o                    (mio_out),
    .mio_oe_o                     (mio_oe),

    // Dedicated I/O
    .dio_in_i                     (dio_in),
    .dio_out_o                    (dio_out),
    .dio_oe_o                     (dio_oe),

    // Pad attributes
    .mio_attr_o                   ( ),
    .dio_attr_o                   ( ),

    // Memory attributes
    // This is different between verilator and the rest of the platforms right now
    .ram_1p_cfg_i                 ('0),
    .ram_2p_cfg_i                 ('0),
    .rom_cfg_i                    ('0),

    // DFT signals
    .ast_lc_dft_en_o              ( dft_en                     ),
    .dft_strap_test_o             ( dft_strap_test             ),
    .dft_hold_tap_sel_i           ( '0                         ),
    .scan_rst_ni                  ( scan_rst_n                 ),
    .scan_en_i                    ( scan_en                    ),
    .scanmode_i                   ( scanmode                   )
  );

endmodule : chip_earlgrey_verilator
