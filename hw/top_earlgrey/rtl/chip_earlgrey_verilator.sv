// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module chip_earlgrey_verilator (
  // Clock and Reset
  input clk_i,
  input rst_ni
);

  import top_earlgrey_pkg::*;


  logic IO_JTCK, IO_JTMS, IO_JTRST_N, IO_JTDI, IO_JTDO;

  logic [pinmux_reg_pkg::NDioPads-1:0] dio_in;
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_out;
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_oe;

  logic [pinmux_reg_pkg::NMioPads-1:0] mio_in;
  logic [pinmux_reg_pkg::NMioPads-1:0] mio_out;
  logic [pinmux_reg_pkg::NMioPads-1:0] mio_oe;
  prim_pad_wrapper_pkg::pad_attr_t[pinmux_reg_pkg::NMioPads-1:0] mio_attr;

  // USB related signals
  logic usb_dp_pullup_en;
  logic usb_dn_pullup_en;
  logic usb_rx_d;
  logic usb_tx_d;
  logic usb_tx_se0;
  logic usb_tx_use_d_se0;
  logic usb_rx_enable;

  // Padring substitute that maps the mio/dio interface from pinmux to flat
  // cio_* signals that the testbench DPI models connect to.
  padring_verilator u_padring (
    .mio_in_o  (mio_in ),
    .mio_out_i (mio_out),
    .mio_oe_i  (mio_oe ),
    .mio_attr_i(mio_attr),

    .dio_in_o (dio_in ),
    .dio_out_i(dio_out),
    .dio_oe_i (dio_oe ),

    .usb_rx_d_o        (usb_rx_d        ),
    .usb_tx_d_i        (usb_tx_d        ),
    .usb_tx_se0_i      (usb_tx_se0      ),
    .usb_tx_use_d_se0_i(usb_tx_use_d_se0),
    .usb_rx_enable_i   (usb_rx_enable   ),
    .usb_dp_pullup_en_i(usb_dp_pullup_en),
    .usb_dn_pullup_en_i(usb_dn_pullup_en)
  );

  ////////////////////////////////
  // AST - Custom for Verilator //
  ////////////////////////////////
  ast_pkg::ast_pwst_t ast_pwst;
  ast_pkg::ast_pwst_t ast_pwst_h;

  // pwrmgr interface
  pwrmgr_pkg::pwr_ast_req_t pwrmgr_ast_req;
  pwrmgr_pkg::pwr_ast_rsp_t pwrmgr_ast_rsp;

  ast_pkg::ast_clks_t ast_base_clks;

  // external clock comes in at a fixed position
  logic ext_clk;
  assign ext_clk = '0;

  logic [ast_pkg::Pad2AstInWidth-1:0] pad2ast;
  assign pad2ast = '0;

  logic clk_aon;
  // reset is not used below because verilator uses only sync resets
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
  tlul_pkg::tl_h2d_t ast_tl_req;
  tlul_pkg::tl_d2h_t ast_tl_rsp;

  assign pwrmgr_ast_rsp.main_pok = ast_pwst.main_pok;

  // Generated clocks, resets, and enable signals
  clkmgr_pkg::clkmgr_out_t    clkmgr_aon_clocks;
  clkmgr_pkg::clkmgr_cg_en_t  clkmgr_aon_cg_en;
  rstmgr_pkg::rstmgr_out_t    rstmgr_aon_resets;
  rstmgr_pkg::rstmgr_rst_en_t rstmgr_aon_rst_en;

  // monitored clock
  logic sck_monitor;

  // otp power sequence
  otp_macro_pkg::otp_ast_req_t otp_macro_pwr_seq;
  otp_macro_pkg::otp_ast_rsp_t otp_macro_pwr_seq_h;

  logic usb_ref_pulse;
  logic usb_ref_val;

  // adc
  ast_pkg::adc_ast_req_t adc_req;
  ast_pkg::adc_ast_rsp_t adc_rsp;

  // entropy source interface
  logic es_rng_enable, es_rng_valid;
  logic [ast_pkg::EntropyStreams-1:0] es_rng_bit;
  logic es_rng_fips;

  // entropy distribution network
  edn_pkg::edn_req_t ast_edn_req;
  edn_pkg::edn_rsp_t ast_edn_rsp;

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
  prim_mubi_pkg::mubi4_t div_step_down_req;
  logic hi_speed_sel;

  // DFT connections
  logic scan_en;
  lc_ctrl_pkg::lc_tx_t lc_dft_en;
  pinmux_pkg::dft_strap_test_req_t dft_strap_test;

  // Debug connections
  logic [ast_pkg::Ast2PadOutWidth-1:0] ast2pinmux;

  // Jitter enable
  logic clk_main_jitter_en;

  // AST does not use all clocks / resets forwarded to it
  logic unused_slow_clk_en;
  assign unused_slow_clk_en = pwrmgr_ast_req.slow_clk_en;

  logic unused_pwr_clamp;
  assign unused_pwr_clamp = pwrmgr_ast_req.pwr_clamp;

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
    // clocks' oschillator bypass for FPGA
    .clk_osc_byp_i         ( clks_osc_byp ),


    // clocks and resets supplied for detection
    .sns_clks_i            ( clkmgr_aon_clocks ),
    .sns_rsts_i            ( rstmgr_aon_resets ),
    .sns_spi_ext_clk_i     ( sck_monitor       ),
    // tlul
    .tl_i                  ( ast_tl_req ),
    .tl_o                  ( ast_tl_rsp ),
    // init done indication
    .ast_init_done_o       ( ast_init_done),
    // buffered clocks & resets
    .clk_ast_tlul_i (clkmgr_aon_clocks.clk_io_div4_infra),
    .clk_ast_adc_i (clkmgr_aon_clocks.clk_aon_peri),
    .clk_ast_alert_i (clkmgr_aon_clocks.clk_io_div4_secure),
    .clk_ast_es_i (clkmgr_aon_clocks.clk_main_secure),
    .clk_ast_rng_i (clkmgr_aon_clocks.clk_main_secure),
    .clk_ast_usb_i (clkmgr_aon_clocks.clk_usb_peri),
    .rst_ast_tlul_ni (rstmgr_aon_resets.rst_lc_io_div4_n[rstmgr_pkg::DomainMainSel]),
    .rst_ast_adc_ni (rstmgr_aon_resets.rst_lc_aon_n[rstmgr_pkg::DomainMainSel]),
    .rst_ast_alert_ni (rstmgr_aon_resets.rst_lc_io_div4_n[rstmgr_pkg::DomainMainSel]),
    .rst_ast_es_ni (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::DomainMainSel]),
    .rst_ast_rng_ni (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::DomainMainSel]),
    .rst_ast_usb_ni (rstmgr_aon_resets.rst_usb_n[rstmgr_pkg::DomainMainSel]),

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
    .main_env_iso_en_i     ( pwrmgr_ast_req.pwr_clamp_env ),
    .main_pd_ni            ( pwrmgr_ast_req.main_pd_n ),
    // pdm control (flash)/otp
    .flash_power_down_h_o  ( flash_power_down_h ),
    .flash_power_ready_h_o ( flash_power_ready_h ),
    .otp_power_seq_i       ( otp_macro_pwr_seq ),
    .otp_power_seq_h_o     ( otp_macro_pwr_seq_h ),
    // system source clock
    .clk_src_sys_en_i      ( pwrmgr_ast_req.core_clk_en ),
    // need to add function in clkmgr
    .clk_src_sys_jen_i     ( clk_main_jitter_en ),
    .clk_src_sys_o         ( ast_base_clks.clk_sys  ),
    .clk_src_sys_val_o     ( pwrmgr_ast_rsp.core_clk_val ),
    // aon source clock
    .clk_src_aon_o         ( ast_base_clks.clk_aon ),
    .clk_src_aon_val_o     ( pwrmgr_ast_rsp.slow_clk_val ),
    // io source clock
    .clk_src_io_en_i       ( pwrmgr_ast_req.io_clk_en ),
    .clk_src_io_o          ( ast_base_clks.clk_io ),
    .clk_src_io_val_o      ( pwrmgr_ast_rsp.io_clk_val ),
    .clk_src_io_48m_o      ( div_step_down_req ),
    // usb source clock
    .usb_ref_pulse_i       ( usb_ref_pulse ),
    .usb_ref_val_i         ( usb_ref_val ),
    .clk_src_usb_en_i      ( pwrmgr_ast_req.usb_clk_en ),
    .clk_src_usb_o         ( ast_base_clks.clk_usb ),
    .clk_src_usb_val_o     ( pwrmgr_ast_rsp.usb_clk_val ),
    // adc
    .adc_pd_i              ( adc_req.pd ),
    .adc_chnsel_i          ( adc_req.channel_sel ),
    .adc_d_o               ( adc_rsp.data ),
    .adc_d_val_o           ( adc_rsp.data_valid ),
    // rng
    .rng_en_i              ( es_rng_enable ),
    .rng_fips_i            ( es_rng_fips ),
    .rng_val_o             ( es_rng_valid ),
    .rng_b_o               ( es_rng_bit ),
    // entropy
    .entropy_rsp_i         ( ast_edn_rsp ),
    .entropy_req_o         ( ast_edn_req ),
    // alerts
    .alert_rsp_i           ( ast_alert_rsp  ),
    .alert_req_o           ( ast_alert_req  ),
    // dft
    .dft_strap_test_i      ( dft_strap_test   ),
    .lc_dft_en_i           ( lc_dft_en           ),
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
    tck_idx:        MioPadIor3,
    tms_idx:        MioPadIor0,
    trst_idx:       MioPadIor4,
    tdi_idx:        MioPadIor2,
    tdo_idx:        MioPadIor1,
    tap_strap0_idx: MioPadIoc8,
    tap_strap1_idx: MioPadIoc5,
    dft_strap0_idx: MioPadIor5,
    dft_strap1_idx: MioPadIor7,
    // TODO: check whether there is a better way to pass these USB-specific params
    usb_dp_idx:        DioUsbdevUsbDp,
    usb_dn_idx:        DioUsbdevUsbDn,
    usb_sense_idx:     MioInUsbdevSense,
    // TODO: connect these once the verilator chip-level has been merged with the chiplevel.sv.tpl
    dio_pad_type: {pinmux_reg_pkg::NDioPads{prim_pad_wrapper_pkg::BidirStd}},
    mio_pad_type: {pinmux_reg_pkg::NMioPads{prim_pad_wrapper_pkg::BidirStd}},
    dio_scan_role: {pinmux_reg_pkg::NDioPads{prim_pad_wrapper_pkg::NoScan}},
    mio_scan_role: {pinmux_reg_pkg::NMioPads{prim_pad_wrapper_pkg::NoScan}}
  };

  prim_mubi_pkg::mubi4_t lc_clk_bypass;


  // Top-level design

  logic [rstmgr_pkg::PowerDomains-1:0] por_n;
  // TODO update por / reset connections, this is not quite right here
  assign por_n = {ast_pwst.main_pok, ast_pwst.aon_pok};

  // Inter-Power Domain signals
  logic [6:0] intr_vector_pd_aon;
  prim_alert_pkg::alert_tx_t [11:0] alert_tx_pd_aon;
  prim_alert_pkg::alert_rx_t [11:0] alert_rx_pd_aon;
  alert_handler_pkg::alert_crashdump_t       alert_handler_crashdump;
  prim_esc_pkg::esc_rx_t       alert_handler_esc_rx;
  prim_esc_pkg::esc_tx_t       alert_handler_esc_tx;
  logic       aon_timer_aon_nmi_wdog_timer_bark;
  otp_ctrl_pkg::sram_otp_key_req_t       otp_ctrl_sram_otp_key_req;
  otp_ctrl_pkg::sram_otp_key_rsp_t       otp_ctrl_sram_otp_key_rsp;
  pwrmgr_pkg::pwr_nvm_t       pwrmgr_aon_pwr_nvm;
  pwrmgr_pkg::pwr_otp_req_t       pwrmgr_aon_pwr_otp_req;
  pwrmgr_pkg::pwr_otp_rsp_t       pwrmgr_aon_pwr_otp_rsp;
  lc_ctrl_pkg::pwr_lc_req_t       pwrmgr_aon_pwr_lc_req;
  lc_ctrl_pkg::pwr_lc_rsp_t       pwrmgr_aon_pwr_lc_rsp;
  logic       pwrmgr_aon_strap;
  logic       pwrmgr_aon_low_power;
  lc_ctrl_pkg::lc_tx_t       pwrmgr_aon_fetch_en;
  rom_ctrl_pkg::pwrmgr_data_t       rom_ctrl_pwrmgr_data;
  prim_mubi_pkg::mubi4_t [3:0] clkmgr_aon_idle;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_dft_en;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_hw_debug_en;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_escalate_en;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_clk_byp_req;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_clk_byp_ack;
  rv_core_ibex_pkg::cpu_crash_dump_t       rv_core_ibex_crash_dump;
  rv_core_ibex_pkg::cpu_pwrmgr_t       rv_core_ibex_pwrmgr;
  logic       rv_dm_ndmreset_req;
  logic [1:0] pwrmgr_aon_wakeups;
  tlul_pkg::tl_h2d_t       pwrmgr_aon_tl_req;
  tlul_pkg::tl_d2h_t       pwrmgr_aon_tl_rsp;
  tlul_pkg::tl_h2d_t       rstmgr_aon_tl_req;
  tlul_pkg::tl_d2h_t       rstmgr_aon_tl_rsp;
  tlul_pkg::tl_h2d_t       clkmgr_aon_tl_req;
  tlul_pkg::tl_d2h_t       clkmgr_aon_tl_rsp;
  tlul_pkg::tl_h2d_t       sensor_ctrl_aon_tl_req;
  tlul_pkg::tl_d2h_t       sensor_ctrl_aon_tl_rsp;
  tlul_pkg::tl_h2d_t       sram_ctrl_ret_aon_regs_tl_req;
  tlul_pkg::tl_d2h_t       sram_ctrl_ret_aon_regs_tl_rsp;
  tlul_pkg::tl_h2d_t       sram_ctrl_ret_aon_ram_tl_req;
  tlul_pkg::tl_d2h_t       sram_ctrl_ret_aon_ram_tl_rsp;
  tlul_pkg::tl_h2d_t       aon_timer_aon_tl_req;
  tlul_pkg::tl_d2h_t       aon_timer_aon_tl_rsp;
  tlul_pkg::tl_h2d_t       sysrst_ctrl_aon_tl_req;
  tlul_pkg::tl_d2h_t       sysrst_ctrl_aon_tl_rsp;
  tlul_pkg::tl_h2d_t       adc_ctrl_aon_tl_req;
  tlul_pkg::tl_d2h_t       adc_ctrl_aon_tl_rsp;
  logic       cio_sysrst_ctrl_aon_ec_rst_l_d2p;
  logic       cio_sysrst_ctrl_aon_ec_rst_l_en_d2p;
  logic       cio_sysrst_ctrl_aon_ec_rst_l_p2d;
  logic       cio_sysrst_ctrl_aon_flash_wp_l_d2p;
  logic       cio_sysrst_ctrl_aon_flash_wp_l_en_d2p;
  logic       cio_sysrst_ctrl_aon_flash_wp_l_p2d;
  logic       cio_sysrst_ctrl_aon_ac_present_p2d;
  logic       cio_sysrst_ctrl_aon_key0_in_p2d;
  logic       cio_sysrst_ctrl_aon_key1_in_p2d;
  logic       cio_sysrst_ctrl_aon_key2_in_p2d;
  logic       cio_sysrst_ctrl_aon_pwrb_in_p2d;
  logic       cio_sysrst_ctrl_aon_lid_open_p2d;
  logic       cio_sysrst_ctrl_aon_bat_disable_d2p;
  logic       cio_sysrst_ctrl_aon_bat_disable_en_d2p;
  logic       cio_sysrst_ctrl_aon_key0_out_d2p;
  logic       cio_sysrst_ctrl_aon_key0_out_en_d2p;
  logic       cio_sysrst_ctrl_aon_key1_out_d2p;
  logic       cio_sysrst_ctrl_aon_key1_out_en_d2p;
  logic       cio_sysrst_ctrl_aon_key2_out_d2p;
  logic       cio_sysrst_ctrl_aon_key2_out_en_d2p;
  logic       cio_sysrst_ctrl_aon_pwrb_out_d2p;
  logic       cio_sysrst_ctrl_aon_pwrb_out_en_d2p;
  logic       cio_sysrst_ctrl_aon_z3_wakeup_d2p;
  logic       cio_sysrst_ctrl_aon_z3_wakeup_en_d2p;
  logic [8:0] cio_sensor_ctrl_aon_ast_debug_out_d2p;
  logic [8:0] cio_sensor_ctrl_aon_ast_debug_out_en_d2p;

  //////////////////////
  // Top-level design //
  //////////////////////
  top_earlgrey #(
    .PinmuxAonTargetCfg(PinmuxTargetCfg),
    .SecAesAllowForcingMasks(1'b1),
    .SramCtrlMainInstrExec(1)
  ) top_earlgrey (
    // Clocks and clock gating control from clkmgr_aon
    .clkmgr_aon_clocks_i(clkmgr_aon_clocks),
    .clkmgr_aon_cg_en_i (clkmgr_aon_cg_en),

    // Resets and reset assert info from rstmgr_aon
    .rstmgr_aon_resets_i(rstmgr_aon_resets),
    .rstmgr_aon_rst_en_i(rstmgr_aon_rst_en),

    // Manual DFT signals
    .scan_rst_ni(scan_rst_n),
    .scan_en_i  (scan_en   ),
    .scanmode_i (scanmode  ),

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
    .dio_attr_o(),

    // Special inter-power domain signals (interrupts, alerts)
    .intr_vector_pd_aon_i(intr_vector_pd_aon),

    .alert_tx_pd_aon_i(alert_tx_pd_aon),
    .alert_rx_pd_aon_o(alert_rx_pd_aon),

    // Ports to and from other power domains (auto-generated)
    .alert_handler_crashdump_o                 (alert_handler_crashdump  ),
    .alert_handler_esc_rx_i                    (alert_handler_esc_rx     ),
    .alert_handler_esc_tx_o                    (alert_handler_esc_tx     ),
    .aon_timer_aon_nmi_wdog_timer_bark_i       (aon_timer_aon_nmi_wdog_timer_bark),
    .otp_ctrl_sram_otp_key_req_i               (otp_ctrl_sram_otp_key_req),
    .otp_ctrl_sram_otp_key_rsp_o               (otp_ctrl_sram_otp_key_rsp),
    .pwrmgr_aon_pwr_nvm_o                      (pwrmgr_aon_pwr_nvm       ),
    .pwrmgr_aon_pwr_otp_req_i                  (pwrmgr_aon_pwr_otp_req   ),
    .pwrmgr_aon_pwr_otp_rsp_o                  (pwrmgr_aon_pwr_otp_rsp   ),
    .pwrmgr_aon_pwr_lc_req_i                   (pwrmgr_aon_pwr_lc_req    ),
    .pwrmgr_aon_pwr_lc_rsp_o                   (pwrmgr_aon_pwr_lc_rsp    ),
    .pwrmgr_aon_strap_i                        (pwrmgr_aon_strap         ),
    .pwrmgr_aon_low_power_i                    (pwrmgr_aon_low_power     ),
    .pwrmgr_aon_fetch_en_i                     (pwrmgr_aon_fetch_en      ),
    .rom_ctrl_pwrmgr_data_o                    (rom_ctrl_pwrmgr_data     ),
    .clkmgr_aon_idle_o                         (clkmgr_aon_idle          ),
    .lc_ctrl_lc_dft_en_o                       (lc_ctrl_lc_dft_en        ),
    .lc_ctrl_lc_hw_debug_en_o                  (lc_ctrl_lc_hw_debug_en   ),
    .lc_ctrl_lc_escalate_en_o                  (lc_ctrl_lc_escalate_en   ),
    .lc_ctrl_lc_clk_byp_req_o                  (lc_ctrl_lc_clk_byp_req   ),
    .lc_ctrl_lc_clk_byp_ack_i                  (lc_ctrl_lc_clk_byp_ack   ),
    .rv_core_ibex_crash_dump_o                 (rv_core_ibex_crash_dump  ),
    .rv_core_ibex_pwrmgr_o                     (rv_core_ibex_pwrmgr      ),
    .rv_dm_ndmreset_req_o                      (rv_dm_ndmreset_req       ),
    .pwrmgr_aon_wakeups_o                      (pwrmgr_aon_wakeups       ),
    .pwrmgr_aon_tl_req_o                       (pwrmgr_aon_tl_req        ),
    .pwrmgr_aon_tl_rsp_i                       (pwrmgr_aon_tl_rsp        ),
    .rstmgr_aon_tl_req_o                       (rstmgr_aon_tl_req        ),
    .rstmgr_aon_tl_rsp_i                       (rstmgr_aon_tl_rsp        ),
    .clkmgr_aon_tl_req_o                       (clkmgr_aon_tl_req        ),
    .clkmgr_aon_tl_rsp_i                       (clkmgr_aon_tl_rsp        ),
    .sensor_ctrl_aon_tl_req_o                  (sensor_ctrl_aon_tl_req   ),
    .sensor_ctrl_aon_tl_rsp_i                  (sensor_ctrl_aon_tl_rsp   ),
    .sram_ctrl_ret_aon_regs_tl_req_o           (sram_ctrl_ret_aon_regs_tl_req),
    .sram_ctrl_ret_aon_regs_tl_rsp_i           (sram_ctrl_ret_aon_regs_tl_rsp),
    .sram_ctrl_ret_aon_ram_tl_req_o            (sram_ctrl_ret_aon_ram_tl_req),
    .sram_ctrl_ret_aon_ram_tl_rsp_i            (sram_ctrl_ret_aon_ram_tl_rsp),
    .aon_timer_aon_tl_req_o                    (aon_timer_aon_tl_req     ),
    .aon_timer_aon_tl_rsp_i                    (aon_timer_aon_tl_rsp     ),
    .sysrst_ctrl_aon_tl_req_o                  (sysrst_ctrl_aon_tl_req   ),
    .sysrst_ctrl_aon_tl_rsp_i                  (sysrst_ctrl_aon_tl_rsp   ),
    .adc_ctrl_aon_tl_req_o                     (adc_ctrl_aon_tl_req      ),
    .adc_ctrl_aon_tl_rsp_i                     (adc_ctrl_aon_tl_rsp      ),
    .cio_sysrst_ctrl_aon_ec_rst_l_d2p_i        (cio_sysrst_ctrl_aon_ec_rst_l_d2p),
    .cio_sysrst_ctrl_aon_ec_rst_l_en_d2p_i     (cio_sysrst_ctrl_aon_ec_rst_l_en_d2p),
    .cio_sysrst_ctrl_aon_ec_rst_l_p2d_o        (cio_sysrst_ctrl_aon_ec_rst_l_p2d),
    .cio_sysrst_ctrl_aon_flash_wp_l_d2p_i      (cio_sysrst_ctrl_aon_flash_wp_l_d2p),
    .cio_sysrst_ctrl_aon_flash_wp_l_en_d2p_i   (cio_sysrst_ctrl_aon_flash_wp_l_en_d2p),
    .cio_sysrst_ctrl_aon_flash_wp_l_p2d_o      (cio_sysrst_ctrl_aon_flash_wp_l_p2d),
    .cio_sysrst_ctrl_aon_ac_present_p2d_o      (cio_sysrst_ctrl_aon_ac_present_p2d),
    .cio_sysrst_ctrl_aon_key0_in_p2d_o         (cio_sysrst_ctrl_aon_key0_in_p2d),
    .cio_sysrst_ctrl_aon_key1_in_p2d_o         (cio_sysrst_ctrl_aon_key1_in_p2d),
    .cio_sysrst_ctrl_aon_key2_in_p2d_o         (cio_sysrst_ctrl_aon_key2_in_p2d),
    .cio_sysrst_ctrl_aon_pwrb_in_p2d_o         (cio_sysrst_ctrl_aon_pwrb_in_p2d),
    .cio_sysrst_ctrl_aon_lid_open_p2d_o        (cio_sysrst_ctrl_aon_lid_open_p2d),
    .cio_sysrst_ctrl_aon_bat_disable_d2p_i     (cio_sysrst_ctrl_aon_bat_disable_d2p),
    .cio_sysrst_ctrl_aon_bat_disable_en_d2p_i  (cio_sysrst_ctrl_aon_bat_disable_en_d2p),
    .cio_sysrst_ctrl_aon_key0_out_d2p_i        (cio_sysrst_ctrl_aon_key0_out_d2p),
    .cio_sysrst_ctrl_aon_key0_out_en_d2p_i     (cio_sysrst_ctrl_aon_key0_out_en_d2p),
    .cio_sysrst_ctrl_aon_key1_out_d2p_i        (cio_sysrst_ctrl_aon_key1_out_d2p),
    .cio_sysrst_ctrl_aon_key1_out_en_d2p_i     (cio_sysrst_ctrl_aon_key1_out_en_d2p),
    .cio_sysrst_ctrl_aon_key2_out_d2p_i        (cio_sysrst_ctrl_aon_key2_out_d2p),
    .cio_sysrst_ctrl_aon_key2_out_en_d2p_i     (cio_sysrst_ctrl_aon_key2_out_en_d2p),
    .cio_sysrst_ctrl_aon_pwrb_out_d2p_i        (cio_sysrst_ctrl_aon_pwrb_out_d2p),
    .cio_sysrst_ctrl_aon_pwrb_out_en_d2p_i     (cio_sysrst_ctrl_aon_pwrb_out_en_d2p),
    .cio_sysrst_ctrl_aon_z3_wakeup_d2p_i       (cio_sysrst_ctrl_aon_z3_wakeup_d2p),
    .cio_sysrst_ctrl_aon_z3_wakeup_en_d2p_i    (cio_sysrst_ctrl_aon_z3_wakeup_en_d2p),
    .cio_sensor_ctrl_aon_ast_debug_out_d2p_i   (cio_sensor_ctrl_aon_ast_debug_out_d2p),
    .cio_sensor_ctrl_aon_ast_debug_out_en_d2p_i(cio_sensor_ctrl_aon_ast_debug_out_en_d2p),

    // Regular ports
    .ast_edn_req_i            (ast_edn_req        ),
    .ast_edn_rsp_o            (ast_edn_rsp        ),
    .ast_lc_dft_en_o          (lc_dft_en          ),
    .obs_ctrl_i               ('0                 ),
    .ram_1p_cfg_i             ('0                 ),
    .sram_ctrl_main_cfg_i     ('0                 ),
    .spi_ram_2p_cfg_i         ('0                 ),
    .usb_ram_1p_cfg_i         ('0                 ),
    .rom_cfg_i                ('0                 ),
    .flash_bist_enable_i      (flash_bist_enable  ),
    .flash_power_down_h_i     (flash_power_down_h ),
    .flash_power_ready_h_i    (flash_power_ready_h),
    .flash_test_mode_a_io     (                   ),
    .flash_test_voltage_h_io  (                   ),
    .flash_obs_o              (                   ),
    .es_rng_enable_o          (es_rng_enable      ),
    .es_rng_valid_i           (es_rng_valid       ),
    .es_rng_bit_i             (es_rng_bit         ),
    .es_rng_fips_o            (                   ),
    .ast_tl_req_o             (ast_tl_req         ),
    .ast_tl_rsp_i             (ast_tl_rsp         ),
    .dft_strap_test_o         (dft_strap_test     ),
    .dft_hold_tap_sel_i       ('0                 ),
    .usb_dp_pullup_en_o       (usb_dp_pullup_en   ),
    .usb_dn_pullup_en_o       (usb_dn_pullup_en   ),
    .otp_macro_pwr_seq_o      (otp_macro_pwr_seq  ),
    .otp_macro_pwr_seq_h_i    (otp_macro_pwr_seq_h),
    .otp_ext_voltage_h_io     (                   ),
    .otp_obs_o                (                   ),
    .fpga_info_i              ('0                 ),
    .sck_monitor_o            (sck_monitor        ),
    .usbdev_usb_rx_d_i        (usb_rx_d           ),
    .usbdev_usb_tx_d_o        (usb_tx_d           ),
    .usbdev_usb_tx_se0_o      (usb_tx_se0         ),
    .usbdev_usb_tx_use_d_se0_o(usb_tx_use_d_se0   ),
    .usbdev_usb_rx_enable_o   (usb_rx_enable      ),
    .usbdev_usb_ref_val_o     (usb_ref_val        ),
    .usbdev_usb_ref_pulse_o   (usb_ref_pulse      )
  );


  //////////////////////
  // Always-on Domain //
  //////////////////////
  top_earlgrey_pd_aon #(
    .SramCtrlRetAonInstrExec(0)
  ) top_earlgrey_pd_aon (
    // All externally supplied clocks
    // TODO check if these assignments make sense
    .clk_main_i(clk_i  ),
    .clk_io_i  (clk_i  ),
    .clk_usb_i (clk_i  ),
    .clk_aon_i (clk_aon),

    // Manual DFT signals
    .scan_rst_ni(scan_rst_n),
    .scanmode_i (scanmode  ),

    // Special inter-power domain signals (interrupts, alerts)
    .intr_vector_o(intr_vector_pd_aon),

    .alert_tx_o(alert_tx_pd_aon),
    .alert_rx_i(alert_rx_pd_aon),

    // Ports to and from other power domains
    .alert_handler_crashdump_i                 (alert_handler_crashdump  ),
    .alert_handler_esc_rx_o                    (alert_handler_esc_rx     ),
    .alert_handler_esc_tx_i                    (alert_handler_esc_tx     ),
    .aon_timer_aon_nmi_wdog_timer_bark_o       (aon_timer_aon_nmi_wdog_timer_bark),
    .otp_ctrl_sram_otp_key_req_o               (otp_ctrl_sram_otp_key_req),
    .otp_ctrl_sram_otp_key_rsp_i               (otp_ctrl_sram_otp_key_rsp),
    .pwrmgr_aon_pwr_nvm_i                      (pwrmgr_aon_pwr_nvm       ),
    .pwrmgr_aon_pwr_otp_req_o                  (pwrmgr_aon_pwr_otp_req   ),
    .pwrmgr_aon_pwr_otp_rsp_i                  (pwrmgr_aon_pwr_otp_rsp   ),
    .pwrmgr_aon_pwr_lc_req_o                   (pwrmgr_aon_pwr_lc_req    ),
    .pwrmgr_aon_pwr_lc_rsp_i                   (pwrmgr_aon_pwr_lc_rsp    ),
    .pwrmgr_aon_strap_o                        (pwrmgr_aon_strap         ),
    .pwrmgr_aon_low_power_o                    (pwrmgr_aon_low_power     ),
    .pwrmgr_aon_fetch_en_o                     (pwrmgr_aon_fetch_en      ),
    .rom_ctrl_pwrmgr_data_i                    (rom_ctrl_pwrmgr_data     ),
    .clkmgr_aon_idle_i                         (clkmgr_aon_idle          ),
    .lc_ctrl_lc_dft_en_i                       (lc_ctrl_lc_dft_en        ),
    .lc_ctrl_lc_hw_debug_en_i                  (lc_ctrl_lc_hw_debug_en   ),
    .lc_ctrl_lc_escalate_en_i                  (lc_ctrl_lc_escalate_en   ),
    .lc_ctrl_lc_clk_byp_req_i                  (lc_ctrl_lc_clk_byp_req   ),
    .lc_ctrl_lc_clk_byp_ack_o                  (lc_ctrl_lc_clk_byp_ack   ),
    .rv_core_ibex_crash_dump_i                 (rv_core_ibex_crash_dump  ),
    .rv_core_ibex_pwrmgr_i                     (rv_core_ibex_pwrmgr      ),
    .rv_dm_ndmreset_req_i                      (rv_dm_ndmreset_req       ),
    .pwrmgr_aon_wakeups_i                      (pwrmgr_aon_wakeups       ),
    .pwrmgr_aon_tl_req_i                       (pwrmgr_aon_tl_req        ),
    .pwrmgr_aon_tl_rsp_o                       (pwrmgr_aon_tl_rsp        ),
    .rstmgr_aon_tl_req_i                       (rstmgr_aon_tl_req        ),
    .rstmgr_aon_tl_rsp_o                       (rstmgr_aon_tl_rsp        ),
    .clkmgr_aon_tl_req_i                       (clkmgr_aon_tl_req        ),
    .clkmgr_aon_tl_rsp_o                       (clkmgr_aon_tl_rsp        ),
    .sensor_ctrl_aon_tl_req_i                  (sensor_ctrl_aon_tl_req   ),
    .sensor_ctrl_aon_tl_rsp_o                  (sensor_ctrl_aon_tl_rsp   ),
    .sram_ctrl_ret_aon_regs_tl_req_i           (sram_ctrl_ret_aon_regs_tl_req),
    .sram_ctrl_ret_aon_regs_tl_rsp_o           (sram_ctrl_ret_aon_regs_tl_rsp),
    .sram_ctrl_ret_aon_ram_tl_req_i            (sram_ctrl_ret_aon_ram_tl_req),
    .sram_ctrl_ret_aon_ram_tl_rsp_o            (sram_ctrl_ret_aon_ram_tl_rsp),
    .aon_timer_aon_tl_req_i                    (aon_timer_aon_tl_req     ),
    .aon_timer_aon_tl_rsp_o                    (aon_timer_aon_tl_rsp     ),
    .sysrst_ctrl_aon_tl_req_i                  (sysrst_ctrl_aon_tl_req   ),
    .sysrst_ctrl_aon_tl_rsp_o                  (sysrst_ctrl_aon_tl_rsp   ),
    .adc_ctrl_aon_tl_req_i                     (adc_ctrl_aon_tl_req      ),
    .adc_ctrl_aon_tl_rsp_o                     (adc_ctrl_aon_tl_rsp      ),
    .cio_sysrst_ctrl_aon_ec_rst_l_d2p_o        (cio_sysrst_ctrl_aon_ec_rst_l_d2p),
    .cio_sysrst_ctrl_aon_ec_rst_l_en_d2p_o     (cio_sysrst_ctrl_aon_ec_rst_l_en_d2p),
    .cio_sysrst_ctrl_aon_ec_rst_l_p2d_i        (cio_sysrst_ctrl_aon_ec_rst_l_p2d),
    .cio_sysrst_ctrl_aon_flash_wp_l_d2p_o      (cio_sysrst_ctrl_aon_flash_wp_l_d2p),
    .cio_sysrst_ctrl_aon_flash_wp_l_en_d2p_o   (cio_sysrst_ctrl_aon_flash_wp_l_en_d2p),
    .cio_sysrst_ctrl_aon_flash_wp_l_p2d_i      (cio_sysrst_ctrl_aon_flash_wp_l_p2d),
    .cio_sysrst_ctrl_aon_ac_present_p2d_i      (cio_sysrst_ctrl_aon_ac_present_p2d),
    .cio_sysrst_ctrl_aon_key0_in_p2d_i         (cio_sysrst_ctrl_aon_key0_in_p2d),
    .cio_sysrst_ctrl_aon_key1_in_p2d_i         (cio_sysrst_ctrl_aon_key1_in_p2d),
    .cio_sysrst_ctrl_aon_key2_in_p2d_i         (cio_sysrst_ctrl_aon_key2_in_p2d),
    .cio_sysrst_ctrl_aon_pwrb_in_p2d_i         (cio_sysrst_ctrl_aon_pwrb_in_p2d),
    .cio_sysrst_ctrl_aon_lid_open_p2d_i        (cio_sysrst_ctrl_aon_lid_open_p2d),
    .cio_sysrst_ctrl_aon_bat_disable_d2p_o     (cio_sysrst_ctrl_aon_bat_disable_d2p),
    .cio_sysrst_ctrl_aon_bat_disable_en_d2p_o  (cio_sysrst_ctrl_aon_bat_disable_en_d2p),
    .cio_sysrst_ctrl_aon_key0_out_d2p_o        (cio_sysrst_ctrl_aon_key0_out_d2p),
    .cio_sysrst_ctrl_aon_key0_out_en_d2p_o     (cio_sysrst_ctrl_aon_key0_out_en_d2p),
    .cio_sysrst_ctrl_aon_key1_out_d2p_o        (cio_sysrst_ctrl_aon_key1_out_d2p),
    .cio_sysrst_ctrl_aon_key1_out_en_d2p_o     (cio_sysrst_ctrl_aon_key1_out_en_d2p),
    .cio_sysrst_ctrl_aon_key2_out_d2p_o        (cio_sysrst_ctrl_aon_key2_out_d2p),
    .cio_sysrst_ctrl_aon_key2_out_en_d2p_o     (cio_sysrst_ctrl_aon_key2_out_en_d2p),
    .cio_sysrst_ctrl_aon_pwrb_out_d2p_o        (cio_sysrst_ctrl_aon_pwrb_out_d2p),
    .cio_sysrst_ctrl_aon_pwrb_out_en_d2p_o     (cio_sysrst_ctrl_aon_pwrb_out_en_d2p),
    .cio_sysrst_ctrl_aon_z3_wakeup_d2p_o       (cio_sysrst_ctrl_aon_z3_wakeup_d2p),
    .cio_sysrst_ctrl_aon_z3_wakeup_en_d2p_o    (cio_sysrst_ctrl_aon_z3_wakeup_en_d2p),
    .cio_sensor_ctrl_aon_ast_debug_out_d2p_o   (cio_sensor_ctrl_aon_ast_debug_out_d2p),
    .cio_sensor_ctrl_aon_ast_debug_out_en_d2p_o(cio_sensor_ctrl_aon_ast_debug_out_en_d2p),

    // Regular ports
    .adc_req_o                    (adc_req           ),
    .adc_rsp_i                    (adc_rsp           ),
    .sram_ctrl_ret_aon_cfg_i      ('0                ),
    .clkmgr_aon_clocks_o          (clkmgr_aon_clocks ),
    .clkmgr_aon_cg_en_o           (clkmgr_aon_cg_en  ),
    .clk_main_jitter_en_o         (clk_main_jitter_en),
    .io_clk_byp_req_o             (io_clk_byp_req    ),
    .io_clk_byp_ack_i             (io_clk_byp_ack    ),
    .all_clk_byp_req_o            (all_clk_byp_req   ),
    .all_clk_byp_ack_i            (all_clk_byp_ack   ),
    .hi_speed_sel_o               (hi_speed_sel      ),
    .div_step_down_req_i          (div_step_down_req ),
    .calib_rdy_i                  (ast_init_done     ),
    .pwrmgr_ast_req_o             (pwrmgr_ast_req    ),
    .pwrmgr_ast_rsp_i             (pwrmgr_ast_rsp    ),
    .por_n_i                      (por_n             ),
    .rstmgr_aon_resets_o          (rstmgr_aon_resets ),
    .rstmgr_aon_rst_en_o          (rstmgr_aon_rst_en ),
    .sensor_ctrl_ast_alert_req_i  (ast_alert_req     ),
    .sensor_ctrl_ast_alert_rsp_o  (ast_alert_rsp     ),
    .sensor_ctrl_ast_status_i     (ast_pwst.io_pok   ),
    .ast2pinmux_i                 (ast2pinmux        ),
    .ast_init_done_i              (ast_init_done     ),
    .sensor_ctrl_manual_pad_attr_o(                  )
  );

endmodule : chip_earlgrey_verilator
