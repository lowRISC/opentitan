// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module chip_darjeeling_verilator (
  // Clock and Reset
  input clk_i,
  input rst_ni,

  // communication with GPIO
  input [31:0] cio_gpio_p2d_i,
  output logic [31:0] cio_gpio_d2p_o,
  output logic [31:0] cio_gpio_en_d2p_o,
  output logic [31:0] cio_gpio_pull_en_o,
  output logic [31:0] cio_gpio_pull_select_o,

  // communication with UART
  input cio_uart_rx_p2d_i,
  output logic cio_uart_tx_d2p_o,
  output logic cio_uart_tx_en_d2p_o,

  // communication with SPI
  input cio_spi_device_sck_p2d_i,
  input cio_spi_device_csb_p2d_i,
  input cio_spi_device_sdi_p2d_i,
  output logic cio_spi_device_sdo_d2p_o,
  output logic cio_spi_device_sdo_en_d2p_o

  // TODO: MIO pins?
);

  import top_darjeeling_pkg::*;


  logic IO_JTCK, IO_JTMS, IO_JTRST_N, IO_JTDI, IO_JTDO;

  // TODO: instantiate padring and route these signals through that module
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_in;
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_out;
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_oe;
  prim_pad_wrapper_pkg::pad_attr_t [pinmux_reg_pkg::NDioPads-1:0] dio_attr;

  always_comb begin : assign_dio_in
    dio_in = '0;
    dio_in[DioUart0Rx]      = cio_uart_rx_p2d_i;
    dio_in[DioSpiDeviceSck] = cio_spi_device_sck_p2d_i;
    dio_in[DioSpiDeviceCsb] = cio_spi_device_csb_p2d_i;
    dio_in[DioSpiDeviceSd0] = cio_spi_device_sdi_p2d_i;
    dio_in[DioGpioGpio31:DioGpioGpio0] = cio_gpio_p2d_i;
  end

  assign cio_spi_device_sdo_d2p_o = dio_out[DioSpiDeviceSd1];
  assign cio_spi_device_sdo_en_d2p_o = dio_oe[DioSpiDeviceSd1];

  logic [pinmux_reg_pkg::NMioPads-1:0] mio_in;
  logic [pinmux_reg_pkg::NMioPads-1:0] mio_out;
  logic [pinmux_reg_pkg::NMioPads-1:0] mio_oe;
  prim_pad_wrapper_pkg::pad_attr_t [pinmux_reg_pkg::NMioPads-1:0] mio_attr;

  always_comb begin : assign_mio_in
    mio_in = '0;
/*
    // 14 generic GPIOs
    mio_in[MioPadIob12:MioPadIob6] = cio_gpio_p2d_i[6:0];
    mio_in[MioPadIor13:MioPadIor5] = cio_gpio_p2d_i[13:7];
    // SW straps
    mio_in[MioPadIoc2:MioPadIoc0] = cio_gpio_p2d_i[24:22];
    // TAP straps
    mio_in[MioPadIoc5] = cio_gpio_p2d_i[27];
    mio_in[MioPadIoc8] = cio_gpio_p2d_i[30];
    // UART RX
    mio_in[MioPadIoc3] = cio_uart_rx_p2d_i;
*/
  end

  // 32 generic GPIOs
  assign cio_gpio_d2p_o    = dio_out[DioGpioGpio31:DioGpioGpio0];
  assign cio_gpio_en_d2p_o = dio_oe[DioGpioGpio31:DioGpioGpio0];
/*
  // SW straps
  assign cio_gpio_d2p_o[24:22]      = mio_out[MioPadIoc2:MioPadIoc0];
  assign cio_gpio_en_d2p_o[24:22]   = mio_oe[MioPadIoc2:MioPadIoc0];
  assign cio_gpio_d2p_o[26:25]      = '0;
  assign cio_gpio_en_d2p_o[26:25]   = '0;
  // TAP straps
  assign cio_gpio_d2p_o[27]         = mio_out[MioPadIoc5];
  assign cio_gpio_en_d2p_o[27]      = mio_oe[MioPadIoc5];
  assign cio_gpio_d2p_o[29:28]      = '0;
  assign cio_gpio_en_d2p_o[29:28]   = '0;
  assign cio_gpio_d2p_o[30]         = mio_out[MioPadIoc8];
  assign cio_gpio_en_d2p_o[30]      = mio_oe[MioPadIoc8];
  assign cio_gpio_d2p_o[31]         = '0;
  assign cio_gpio_en_d2p_o[31]      = '0;
*/

  assign cio_uart_tx_d2p_o    = dio_out[DioUart0Tx];
  assign cio_uart_tx_en_d2p_o = dio_oe[DioUart0Tx];

/*
  // Note: we're collecting the `pull_en` and `pull_select` signals together
  // so that the GPIO DPI functions can simulate weak and strong GPIO
  // inputs.  The `cio_gpio_pull_en_o` and `cio_gpio_pull_select_o` bit
  // vectors should have the same ordering as the `cio_gpio_d2p_o` vector.
  // See gpiodpi.c to see how weak/strong inputs work.
  //
  // Pull enable for 14 generic GPIOs
  assign cio_gpio_pull_en_o[0] = mio_attr[MioPadIob6].pull_en;
  assign cio_gpio_pull_en_o[1] = mio_attr[MioPadIob7].pull_en;
  assign cio_gpio_pull_en_o[2] = mio_attr[MioPadIob8].pull_en;
  assign cio_gpio_pull_en_o[3] = mio_attr[MioPadIob9].pull_en;
  assign cio_gpio_pull_en_o[4] = mio_attr[MioPadIob10].pull_en;
  assign cio_gpio_pull_en_o[5] = mio_attr[MioPadIob11].pull_en;
  assign cio_gpio_pull_en_o[6] = mio_attr[MioPadIob12].pull_en;
  assign cio_gpio_pull_en_o[7] = mio_attr[MioPadIor5].pull_en;
  assign cio_gpio_pull_en_o[8] = mio_attr[MioPadIor6].pull_en;
  assign cio_gpio_pull_en_o[9] = mio_attr[MioPadIor7].pull_en;
  assign cio_gpio_pull_en_o[10] = mio_attr[MioPadIor10].pull_en;
  assign cio_gpio_pull_en_o[11] = mio_attr[MioPadIor11].pull_en;
  assign cio_gpio_pull_en_o[12] = mio_attr[MioPadIor12].pull_en;
  assign cio_gpio_pull_en_o[13] = mio_attr[MioPadIor13].pull_en;
  assign cio_gpio_pull_en_o[21:14] = '0;

  // Pull enable for SW STRAPs
  assign cio_gpio_pull_en_o[22] = mio_attr[MioPadIoc0].pull_en;
  assign cio_gpio_pull_en_o[23] = mio_attr[MioPadIoc1].pull_en;
  assign cio_gpio_pull_en_o[24] = mio_attr[MioPadIoc2].pull_en;

  // Pull enable for TAP STRAPs
  assign cio_gpio_pull_en_o[26:25] = '0;
  assign cio_gpio_pull_en_o[27] = mio_attr[MioPadIoc5].pull_en;
  assign cio_gpio_pull_en_o[29:28] = '0;
  assign cio_gpio_pull_en_o[30] = mio_attr[MioPadIoc8].pull_en;
  assign cio_gpio_pull_en_o[31] = '0;

  // Pull select for 14 generic GPIOs
  assign cio_gpio_pull_select_o[0] = mio_attr[MioPadIob6].pull_select;
  assign cio_gpio_pull_select_o[1] = mio_attr[MioPadIob7].pull_select;
  assign cio_gpio_pull_select_o[2] = mio_attr[MioPadIob8].pull_select;
  assign cio_gpio_pull_select_o[3] = mio_attr[MioPadIob9].pull_select;
  assign cio_gpio_pull_select_o[4] = mio_attr[MioPadIob10].pull_select;
  assign cio_gpio_pull_select_o[5] = mio_attr[MioPadIob11].pull_select;
  assign cio_gpio_pull_select_o[6] = mio_attr[MioPadIob12].pull_select;
  assign cio_gpio_pull_select_o[7] = mio_attr[MioPadIor5].pull_select;
  assign cio_gpio_pull_select_o[8] = mio_attr[MioPadIor6].pull_select;
  assign cio_gpio_pull_select_o[9] = mio_attr[MioPadIor7].pull_select;
  assign cio_gpio_pull_select_o[10] = mio_attr[MioPadIor10].pull_select;
  assign cio_gpio_pull_select_o[11] = mio_attr[MioPadIor11].pull_select;
  assign cio_gpio_pull_select_o[12] = mio_attr[MioPadIor12].pull_select;
  assign cio_gpio_pull_select_o[13] = mio_attr[MioPadIor13].pull_select;
  assign cio_gpio_pull_select_o[21:14] = '0;

  // Pull select for SW STRAPs
  assign cio_gpio_pull_select_o[22] = mio_attr[MioPadIoc0].pull_select;
  assign cio_gpio_pull_select_o[23] = mio_attr[MioPadIoc1].pull_select;
  assign cio_gpio_pull_select_o[24] = mio_attr[MioPadIoc2].pull_select;

  // Pull select for TAP STRAPs
  assign cio_gpio_pull_select_o[26:25] = '0;
  assign cio_gpio_pull_select_o[27] = mio_attr[MioPadIoc5].pull_select;
  assign cio_gpio_pull_select_o[29:28] = '0;
  assign cio_gpio_pull_select_o[30] = mio_attr[MioPadIoc8].pull_select;
  assign cio_gpio_pull_select_o[31] = '0;
*/
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
  // and as a result all the clk_aon logic inside top_darjeeling does not
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
    sys: clk_i,
    io:  clk_i,
    aon: clk_aon,
    usb: clk_i
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

  // debug policy bus
  soc_dbg_ctrl_pkg::soc_dbg_policy_t soc_dbg_policy_bus;

  // observe interface
  logic [7:0] otp_obs;
  ast_pkg::ast_obs_ctrl_t obs_ctrl;

  // otp power sequence
  otp_macro_pkg::otp_ast_req_t otp_macro_pwr_seq;
  otp_macro_pkg::otp_ast_rsp_t otp_macro_pwr_seq_h;

  // OTP DFT configuration
  otp_macro_pkg::otp_cfg_t otp_cfg;
  assign otp_cfg = otp_macro_pkg::OTP_CFG_DEFAULT;

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

  // Life cycle clock bypass req/ack
  prim_mubi_pkg::mubi4_t all_clk_byp_req;
  prim_mubi_pkg::mubi4_t all_clk_byp_ack;
  prim_mubi_pkg::mubi4_t io_clk_byp_req;
  prim_mubi_pkg::mubi4_t io_clk_byp_ack;
  prim_mubi_pkg::mubi4_t div_step_down_req;
  logic hi_speed_sel;

  // DFT connections
  lc_ctrl_pkg::lc_tx_t dft_en;

  // Debug connections
  logic [ast_pkg::Ast2PadOutWidth-1:0] ast2pinmux;

  logic debug_halt_cpu_boot;
  assign debug_halt_cpu_boot = 1'b0;

  prim_mubi_pkg::mubi8_t ac_range_check_override;
  assign ac_range_check_override = prim_mubi_pkg::MuBi8True;

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

  // alerts
  soc_proxy_pkg::soc_alert_req_t [23:0] soc_fatal_alert_req;
  soc_proxy_pkg::soc_alert_req_t [3:0] soc_recov_alert_req;
  assign soc_fatal_alert_req = {24{soc_proxy_pkg::SOC_ALERT_REQ_DEFAULT}};
  assign soc_recov_alert_req = { 4{soc_proxy_pkg::SOC_ALERT_REQ_DEFAULT}};

  // SoC control
  logic soc_wkup_async;
  assign soc_wkup_async = 1'b0;
  logic soc_rst_req_async;
  assign soc_rst_req_async = 1'b0;
  logic soc_intr_async;
  assign soc_intr_async = 1'b0;
  logic [7:0] soc_lsio_trigger;
  assign soc_lsio_trigger = '0;
  logic [15:0] soc_gpo_async;
  assign soc_gpo_async = '0;
  logic [3:0] integrator_id;
  assign integrator_id = '0;

  // Boot status from power manager
  pwrmgr_pkg::pwr_boot_status_t pwrmgr_boot_status;

  // TL-UL network connections
  tlul_pkg::tl_h2d_t mbx_tl_req;
  assign mbx_tl_req = tlul_pkg::TL_H2D_DEFAULT;

  // TODO: Connect the JTAG TAP above?
  tlul_pkg::tl_h2d_t dbg_tl_req;
  assign dbg_tl_req = tlul_pkg::TL_H2D_DEFAULT;

  tlul_pkg::tl_h2d_t ctn_misc_tl_h2d;
  assign ctn_misc_tl_h2d = tlul_pkg::TL_H2D_DEFAULT;

  // scan
  logic scan_rst_n;
  logic scan_en;
  prim_mubi_pkg::mubi4_t scanmode;
  assign scan_rst_n = 1'b1;
  assign scan_en = 1'b0;
  assign scanmode = prim_mubi_pkg::MuBi4False;

  prim_mubi_pkg::mubi4_t ast_init_done;
  ast u_ast (
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
    // clocks' oscillator bypass for FPGA
    .clk_osc_byp_i         ( clks_osc_byp ),

    // clocks and resets supplied for detection
    .sns_clks_i      ( clkmgr_aon_clocks    ),
    .sns_rsts_i      ( rstmgr_aon_resets    ),
    .sns_spi_ext_clk_i ( sck_monitor          ),
    // tlul
    .tl_i                  ( base_ast_bus ),
    .tl_o                  ( ast_base_bus ),
    // init done indication
    .ast_init_done_o       ( ast_init_done),
    // buffered clocks & resets
    .clk_ast_tlul_i (clkmgr_aon_clocks.clk_io_div4_secure),
//  .clk_ast_adc_i (clkmgr_aon_clocks.clk_aon_secure),
    .clk_ast_adc_i (clkmgr_aon_clocks.clk_aon_infra),
    .clk_ast_alert_i (clkmgr_aon_clocks.clk_io_div4_secure),
    .clk_ast_es_i (clkmgr_aon_clocks.clk_main_secure),
    .clk_ast_rng_i (clkmgr_aon_clocks.clk_main_secure),
    .clk_ast_usb_i (clkmgr_aon_clocks.clk_main_secure),
    .rst_ast_tlul_ni (rstmgr_aon_resets.rst_lc_io_div4_n[rstmgr_pkg::Domain0Sel]),
    .rst_ast_adc_ni (rstmgr_aon_resets.rst_lc_aon_n[rstmgr_pkg::Domain0Sel]),
    .rst_ast_alert_ni (rstmgr_aon_resets.rst_lc_io_div4_n[rstmgr_pkg::Domain0Sel]),
    .rst_ast_es_ni (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel]),
    .rst_ast_rng_ni (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel]),
    .rst_ast_usb_ni (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel]),

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
    .flash_power_down_h_o  (  ),
    .flash_power_ready_h_o (  ),
    .otp_power_seq_i       ( otp_macro_pwr_seq ),
    .otp_power_seq_h_o     ( otp_macro_pwr_seq_h ),
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
    // TODO: Darjeeling does not include a USB device but the AST
    // has not yet been updated to reflect that.
    .usb_ref_pulse_i       ( 1'b0 ),
    .usb_ref_val_i         ( 1'b0 ),
    .clk_src_usb_en_i      ( 1'b0 ),
    .clk_src_usb_o         (  ),
    .clk_src_usb_val_o     (  ),
    // adc
    .adc_pd_i              ( adc_req.pd ),
    .adc_chnsel_i          ( adc_req.channel_sel ),
    .adc_d_o               ( adc_rsp.data ),
    .adc_d_val_o           ( adc_rsp.data_valid ),
    // entropy source interface
    .es_req_i              ( '0 ),
    .es_rsp_o              (  ),
    // entropy
    .entropy_rsp_i         ( ast_edn_edn_rsp ),
    .entropy_req_o         ( ast_edn_edn_req ),
    // alerts
    .alert_rsp_i           ( ast_alert_rsp  ),
    .alert_req_o           ( ast_alert_req  ),
    // dft
    .lc_dft_en_i           ( dft_en           ),
    .fla_obs_i             ( '0 ),
    .otp_obs_i             ( otp_obs  ),
    .otm_obs_i             ( '0 ),
    .usb_obs_i             ( '0 ),
    .obs_ctrl_o            ( obs_ctrl ),
    // pinmux related
    .padmux2ast_i          ( pad2ast    ),
    .ast2padmux_o          ( ast2pinmux ),
    .ext_freq_is_96m_i     ( hi_speed_sel ),
    .all_clk_byp_req_i     ( all_clk_byp_req ),
    .all_clk_byp_ack_o     ( all_clk_byp_ack ),
    .io_clk_byp_req_i      ( io_clk_byp_req   ),
    .io_clk_byp_ack_o      ( io_clk_byp_ack   ),
    .flash_bist_en_o       (  ),
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
    tck_idx: MioPadMio0,
    tms_idx: MioPadMio0,
    trst_idx: MioPadMio0,
    tdi_idx: MioPadMio0,
    tdo_idx: MioPadMio0,
    tap_strap0_idx: MioPadMio0,
    tap_strap1_idx: MioPadMio0,
    dft_strap0_idx: MioPadMio0,
    dft_strap1_idx: MioPadMio0,
    // TODO: Darjeeling has no USB but the pin definitions are still present.
    usb_dp_idx: MioPadMio0,
    usb_dn_idx: MioPadMio0,
    usb_sense_idx: MioPadMio0,
/*
    tck_idx:        MioPadIor3,
    tms_idx:        MioPadIor0,
    trst_idx:       MioPadIor4,
    tdi_idx:        MioPadIor2,
    tdo_idx:        MioPadIor1,
    tap_strap0_idx: MioPadIoc8,
    tap_strap1_idx: MioPadIoc5,
    dft_strap0_idx: MioPadIor5,
    dft_strap1_idx: MioPadIor7,
*/
    // TODO: connect these once the verilator chip-level has been merged with the chiplevel.sv.tpl
    dio_pad_type: {pinmux_reg_pkg::NDioPads{prim_pad_wrapper_pkg::BidirStd}},
    mio_pad_type: {pinmux_reg_pkg::NMioPads{prim_pad_wrapper_pkg::BidirStd}},
    dio_scan_role: {pinmux_reg_pkg::NDioPads{prim_pad_wrapper_pkg::NoScan}},
    mio_scan_role: {pinmux_reg_pkg::NMioPads{prim_pad_wrapper_pkg::NoScan}}
  };

  prim_mubi_pkg::mubi4_t lc_clk_bypass;

  //////////////////
  // TAP Instance //
  //////////////////

/*
  tlul_pkg::tl_h2d_t dmi_h2d;
  tlul_pkg::tl_d2h_t dmi_d2h;
  jtag_pkg::jtag_req_t jtag_req;
  jtag_pkg::jtag_rsp_t jtag_rsp;

  assign jtag_req.tck    = manual_in_jtag_tck;
  assign jtag_req.tms    = manual_in_jtag_tms;
  assign jtag_req.trst_n = manual_in_jtag_trst_n;
  assign jtag_req.tdi    = manual_in_jtag_tdi;

  assign manual_out_jtag_tck     = '0;
  assign manual_out_jtag_tms     = '0;
  assign manual_out_jtag_trst_n  = '0;
  assign manual_out_jtag_tdi     = '0;
  assign manual_oe_jtag_tck      = '0;
  assign manual_oe_jtag_tms      = '0;
  assign manual_oe_jtag_trst_n   = '0;
  assign manual_oe_jtag_tdi      = '0;
  assign manual_attr_jtag_tck    = '0;
  assign manual_attr_jtag_tms    = '0;
  assign manual_attr_jtag_trst_n = '0;
  assign manual_attr_jtag_tdi    = '0;

  assign manual_out_jtag_tdo     = jtag_rsp.tdo;
  assign manual_oe_jtag_tdo      = jtag_rsp.tdo_oe;
  assign manual_attr_jtag_tdo    = '0;

  logic unused_manual_jtag_sigs;
  assign unused_manual_jtag_sigs = ^{
    manual_in_jtag_tdo
  };

  tlul_jtag_dtm #(
    .IdcodeValue(jtag_id_pkg::LC_DM_COMBINED_JTAG_IDCODE),
    // Notes:
    // - one RV_DM instance uses 9bits
    // - our crossbar tooling expects individual IPs to be spaced apart by 12bits at the moment
    // - the DMI address shifted through jtag is a word address and hence 2bits smaller than this
    // - setting this to 18bits effectively gives us 2^6 = 64 addressable 12bit ranges
    .NumDmiByteAbits(18)
  ) u_tlul_jtag_dtm (
    .clk_i      (clkmgr_aon_clocks.clk_main_infra),
    .rst_ni     (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel]),
    .jtag_i     (jtag_req),
    .jtag_o     (jtag_rsp),
    .scan_rst_ni(scan_rst_n),
    .scanmode_i (scanmode),
    .tl_h2d_o   (dmi_h2d),
    .tl_d2h_i   (dmi_d2h)
  );
*/

  ////////////////
  // CTN M-to-1 //
  ////////////////

  tlul_pkg::tl_h2d_t ctn_tl_h2d[2];
  tlul_pkg::tl_d2h_t ctn_tl_d2h[2];
  //TODO: Resolve this and wire it up.
  assign ctn_tl_h2d[1] = tlul_pkg::TL_H2D_DEFAULT;

  tlul_pkg::tl_h2d_t ctn_sm1_to_s1n_tl_h2d;
  tlul_pkg::tl_d2h_t ctn_sm1_to_s1n_tl_d2h;

  tlul_socket_m1 #(
    .M         (2),
    .HReqPass  ({2{1'b1}}),
    .HRspPass  ({2{1'b1}}),
    .HReqDepth ({2{4'd0}}),
    .HRspDepth ({2{4'd0}}),
    .DReqPass  (1'b1),
    .DRspPass  (1'b1),
    .DReqDepth (4'd0),
    .DRspDepth (4'd0)
  ) u_ctn_sm1 (
    .clk_i  (clkmgr_aon_clocks.clk_main_infra),
    .rst_ni (rstmgr_aon_resets.rst_lc_n[rstmgr_pkg::Domain0Sel]),
    .tl_h_i (ctn_tl_h2d),
    .tl_h_o (ctn_tl_d2h),
    .tl_d_o (ctn_sm1_to_s1n_tl_h2d),
    .tl_d_i (ctn_sm1_to_s1n_tl_d2h)
  );

  ////////////////////////////////////////////
  // CTN Address decoding and SRAM Instance //
  ////////////////////////////////////////////

  localparam int CtnSramDw = top_pkg::TL_DW;

  tlul_pkg::tl_h2d_t ctn_s1n_tl_h2d[1];
  tlul_pkg::tl_d2h_t ctn_s1n_tl_d2h[1];

  // Steering signal for address decoding.
  logic [0:0] ctn_dev_sel_s1n;

  logic sram_req, sram_we, sram_rvalid;
  logic [top_pkg::CtnSramAw-1:0] sram_addr;
  logic [CtnSramDw-1:0] sram_wdata, sram_wmask, sram_rdata;

  // Steering of requests.
  // Addresses leaving the RoT through the CTN port are mapped to an internal 1G address space of
  // 0x4000_0000 - 0x8000_0000. However, the CTN RAM only covers a 1MB region inside that space,
  // and hence additional decoding and steering logic is needed here.
  // TODO: this should in the future be replaced by an automatically generated crossbar.
  always_comb begin
    // Default steering to generate error response if address is not within the range
    ctn_dev_sel_s1n = 1'b1;
    // Steering to CTN SRAM.
    if ((ctn_sm1_to_s1n_tl_h2d.a_address & ~(TOP_DARJEELING_RAM_CTN_SIZE_BYTES-1)) ==
        (TOP_DARJEELING_RAM_CTN_BASE_ADDR - TOP_DARJEELING_CTN_BASE_ADDR)) begin
      ctn_dev_sel_s1n = 1'd0;
    end
  end

  tlul_socket_1n #(
    .HReqDepth (4'h0),
    .HRspDepth (4'h0),
    .DReqDepth (8'h0),
    .DRspDepth (8'h0),
    .N         (1)
  ) u_ctn_s1n (
    .clk_i        (clkmgr_aon_clocks.clk_main_infra),
    .rst_ni       (rstmgr_aon_resets.rst_lc_n[rstmgr_pkg::Domain0Sel]),
    .tl_h_i       (ctn_sm1_to_s1n_tl_h2d),
    .tl_h_o       (ctn_sm1_to_s1n_tl_d2h),
    .tl_d_o       (ctn_s1n_tl_h2d),
    .tl_d_i       (ctn_s1n_tl_d2h),
    .dev_select_i (ctn_dev_sel_s1n)
  );

  // TODO: Presently we ask the tlul_adapter_sram module to generate the integrity signals
  // on both the response and data channels because the CTN SRAM here does not have ECC data.
  // In other simulation environments the ECC data is fixed-up at the point of loading
  // code into the CTN SRAM but that requires UVM support.
  tlul_adapter_sram #(
    .SramAw(top_pkg::CtnSramAw),
    .SramDw(CtnSramDw),
    .Outstanding(2),
    .ByteAccess(1),
    .CmdIntgCheck(1),
    .EnableRspIntgGen(1),
    .EnableDataIntgGen(1),
    .EnableDataIntgPt(0),
    .SecFifoPtr      (0)
  ) u_tlul_adapter_sram_ctn (
    .clk_i       (clkmgr_aon_clocks.clk_main_infra),
    .rst_ni      (rstmgr_aon_resets.rst_lc_n[rstmgr_pkg::Domain0Sel]),
    .tl_i        (ctn_s1n_tl_h2d[0]),
    .tl_o        (ctn_s1n_tl_d2h[0]),
    // Ifetch is explicitly allowed
    .en_ifetch_i (prim_mubi_pkg::MuBi4True),
    .req_o       (sram_req),
    .req_type_o  (),
    // SRAM can always accept a request.
    .gnt_i       (1'b1),
    .we_o        (sram_we),
    .addr_o      (sram_addr),
    .wdata_o     (sram_wdata),
    .wmask_o     (sram_wmask),
    .intg_error_o(),
    .user_rsvd_o (),
    .rdata_i     (sram_rdata),
    .rvalid_i    (sram_rvalid),
    .rerror_i    ('0),
    .compound_txn_in_progress_o(),
    .readback_en_i(prim_mubi_pkg::MuBi4False),
    .readback_error_o(),
    .wr_collision_i(1'b0),
    .write_pending_i(1'b0)
  );

  prim_ram_1p_adv #(
    .Depth(top_pkg::CtnSramDepth),
    .Width(CtnSramDw),
    .DataBitsPerMask(CtnSramDw),
    .EnableECC(0),
    .EnableParity(0),
    .EnableInputPipeline(1),
    .EnableOutputPipeline(1)
  ) u_prim_ram_1p_adv_ctn (
    .clk_i    (clkmgr_aon_clocks.clk_main_infra),
    .rst_ni   (rstmgr_aon_resets.rst_lc_n[rstmgr_pkg::Domain0Sel]),
    .req_i    (sram_req),
    .write_i  (sram_we),
    .addr_i   (sram_addr),
    .wdata_i  (sram_wdata),
    .wmask_i  (sram_wmask),
    .rdata_o  (sram_rdata),
    .rvalid_o (sram_rvalid),
    // No error detection is enabled inside SRAM.
    // Bus ECC is checked at the consumer side.
    .rerror_o (),
    .cfg_i    (ram_1p_cfg),
    .cfg_rsp_o(),
    .alert_o()
  );

  // Top-level design

  logic [rstmgr_pkg::PowerDomains-1:0] por_n;
  assign por_n = {ast_pwst.main_pok, ast_pwst.aon_pok};

  top_darjeeling #(
    .PinmuxAonTargetCfg(PinmuxTargetCfg),
    .SecAesAllowForcingMasks(1'b1),
    .SramCtrlMainInstrExec(1),
    .SramCtrlRetAonInstrExec(0)
  ) top_darjeeling (
    // Multiplexed I/O
    .mio_in_i                     (mio_in),
    .mio_out_o                    (mio_out),
    .mio_oe_o                     (mio_oe),

    // Dedicated I/O
    .dio_in_i                     (dio_in),
    .dio_out_o                    (dio_out),
    .dio_oe_o                     (dio_oe),

    // Pad attributes
    .mio_attr_o                   (mio_attr),
    .dio_attr_o                   (dio_attr),

    .ast_edn_req_i                ( ast_edn_edn_req  ),
    .ast_edn_rsp_o                ( ast_edn_edn_rsp  ),
    .ast_lc_dft_en_o              ( dft_en           ),
    .ast_lc_hw_debug_en_o         ( ),
    .obs_ctrl_i                   ( obs_ctrl ),
    .rom_ctrl0_cfg_i              ('0),
    .rom_ctrl1_cfg_i              ('0),
    .i2c_ram_1p_cfg_i             ('0),
    .i2c_ram_1p_cfg_rsp_o         ( ),
    .sram_ctrl_ret_aon_ram_1p_cfg_i     ('0),
    .sram_ctrl_ret_aon_ram_1p_cfg_rsp_o ( ),
    .sram_ctrl_main_ram_1p_cfg_i        ('0),
    .sram_ctrl_main_ram_1p_cfg_rsp_o    ( ),
    .sram_ctrl_mbox_ram_1p_cfg_i        ('0),
    .sram_ctrl_mbox_ram_1p_cfg_rsp_o    ( ),
    .otbn_imem_ram_1p_cfg_i             ('0),
    .otbn_imem_ram_1p_cfg_rsp_o         ( ),
    .otbn_dmem_ram_1p_cfg_i             ('0),
    .otbn_dmem_ram_1p_cfg_rsp_o         ( ),
    .rv_core_ibex_icache_tag_ram_1p_cfg_i       ('0),
    .rv_core_ibex_icache_tag_ram_1p_cfg_rsp_o   ( ),
    .rv_core_ibex_icache_data_ram_1p_cfg_i      ('0),
    .rv_core_ibex_icache_data_ram_1p_cfg_rsp_o  ( ),
    .spi_device_ram_2p_cfg_sys2spi_i            ('0),
    .spi_device_ram_2p_cfg_rsp_sys2spi_o        ( ),
    .spi_device_ram_2p_cfg_rsp_spi2sys_o        ( ),
    .spi_device_ram_2p_cfg_spi2sys_i            ('0),

    .pwrmgr_boot_status_o         ( pwrmgr_boot_status ),
    .clk_main_jitter_en_o         ( jen                ),
    .io_clk_byp_req_o             ( io_clk_byp_req     ),
    .io_clk_byp_ack_i             ( io_clk_byp_ack     ),
    .all_clk_byp_req_o            ( all_clk_byp_req    ),
    .all_clk_byp_ack_i            ( all_clk_byp_ack    ),
    .hi_speed_sel_o               ( hi_speed_sel       ),
    .div_step_down_req_i          ( div_step_down_req  ),
    .calib_rdy_i                  ( ast_init_done      ),
    .entropy_src_hw_if_req_o      ( ),
    .entropy_src_hw_if_rsp_i      ( ),
    .dma_sys_req_o                ( ),
    .dma_sys_rsp_i                ( '0 ),
    .mbx_tl_req_i                 ( mbx_tl_req ),
    .mbx_tl_rsp_o                 ( ),

    .mbx0_doe_intr_o                            ( ),
    .mbx0_doe_intr_en_o                         ( ),
    .mbx0_doe_intr_support_o                    ( ),
    .mbx0_doe_async_msg_support_o               ( ),
    .mbx1_doe_intr_o                            ( ),
    .mbx1_doe_intr_en_o                         ( ),
    .mbx1_doe_intr_support_o                    ( ),
    .mbx1_doe_async_msg_support_o               ( ),
    .mbx2_doe_intr_o                            ( ),
    .mbx2_doe_intr_en_o                         ( ),
    .mbx2_doe_intr_support_o                    ( ),
    .mbx2_doe_async_msg_support_o               ( ),
    .mbx3_doe_intr_o                            ( ),
    .mbx3_doe_intr_en_o                         ( ),
    .mbx3_doe_intr_support_o                    ( ),
    .mbx3_doe_async_msg_support_o               ( ),
    .mbx4_doe_intr_o                            ( ),
    .mbx4_doe_intr_en_o                         ( ),
    .mbx4_doe_intr_support_o                    ( ),
    .mbx4_doe_async_msg_support_o               ( ),
    .mbx5_doe_intr_o                            ( ),
    .mbx5_doe_intr_en_o                         ( ),
    .mbx5_doe_intr_support_o                    ( ),
    .mbx5_doe_async_msg_support_o               ( ),
    .mbx6_doe_intr_o                            ( ),
    .mbx6_doe_intr_en_o                         ( ),
    .mbx6_doe_intr_support_o                    ( ),
    .mbx6_doe_async_msg_support_o               ( ),
    .mbx_jtag_doe_intr_o                        ( ),
    .mbx_jtag_doe_intr_en_o                     ( ),
    .mbx_jtag_doe_intr_support_o                ( ),
    .mbx_jtag_doe_async_msg_support_o           ( ),
    .mbx_pcie0_doe_intr_o                       ( ),
    .mbx_pcie0_doe_intr_en_o                    ( ),
    .mbx_pcie0_doe_intr_support_o               ( ),
    .mbx_pcie0_doe_async_msg_support_o          ( ),
    .mbx_pcie1_doe_intr_o                       ( ),
    .mbx_pcie1_doe_intr_en_o                    ( ),
    .mbx_pcie1_doe_intr_support_o               ( ),
    .mbx_pcie1_doe_async_msg_support_o          ( ),
    .dbg_tl_req_i                               ( dbg_tl_req ),
    .dbg_tl_rsp_o                               ( ),
    .rv_dm_next_dm_addr_i                       ( ),
    .ast_tl_req_o                 ( base_ast_bus     ),
    .ast_tl_rsp_i                 ( ast_base_bus     ),
    .pwrmgr_ast_req_o             ( base_ast_pwr     ),
    .pwrmgr_ast_rsp_i             ( ast_base_pwr     ),
    .otp_macro_pwr_seq_o          ( otp_macro_pwr_seq   ),
    .otp_macro_pwr_seq_h_i        ( otp_macro_pwr_seq_h ),

    // OTP external voltage
    .otp_ext_voltage_h_io         ( ),

    .otp_obs_o                    ( otp_obs                 ),
    .otp_cfg_i                    ( otp_cfg                 ),
    .otp_cfg_rsp_o                ( ),
    .por_n_i                      ( por_n                   ),
    .fpga_info_i                  ( '0 ),
    .ctn_misc_tl_h2d_i            ( ctn_misc_tl_h2d         ),
    .ctn_misc_tl_d2h_o            ( ),
    .soc_fatal_alert_req_i        ( soc_fatal_alert_req     ),
    .soc_fatal_alert_rsp_o        ( ),
    .soc_recov_alert_req_i        ( soc_recov_alert_req     ),
    .soc_recov_alert_rsp_o        ( ),
    .soc_wkup_async_i             ( soc_wkup_async          ),
    .soc_rst_req_async_i          ( soc_rst_req_async       ),
    .soc_intr_async_i             ( soc_intr_async          ),
    .soc_lsio_trigger_i           ( soc_lsio_trigger        ),
    .soc_gpi_async_o              ( ),
    .soc_gpo_async_i              ( soc_gpo_async           ),
    .integrator_id_i              ( integrator_id           ),
    .sck_monitor_o                ( sck_monitor             ),
    .soc_dbg_policy_bus_o         ( soc_dbg_policy_bus      ),
    .debug_halt_cpu_boot_i        ( debug_halt_cpu_boot     ),
    .racl_policies_o              ( ),
    .racl_error_i                 ( '0 ),
    .ac_range_check_overwrite_i   ( ac_range_check_override ),
    .ctn_tl_h2d_o                 ( ctn_tl_h2d[0]           ),
    .ctn_tl_d2h_i                 ( ctn_tl_d2h[0]           ),

    // All externally supplied clocks
    .clk_main_i                   ( clk_i                      ),
    .clk_io_i                     ( clk_i                      ),
    .clk_aon_i                    ( clk_aon                    ),

    // All clocks forwarded to ast
    .clks_ast_o                   ( clkmgr_aon_clocks          ),
    .rsts_ast_o                   ( rstmgr_aon_resets          ),

    .scan_rst_ni                  ( scan_rst_n                 ),
    .scan_en_i                    ( scan_en                    ),
    .scanmode_i                   ( scanmode                   )
  );

endmodule : chip_darjeeling_verilator
