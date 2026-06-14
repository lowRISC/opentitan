// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_earlgrey/data/top_earlgrey.hjson
//                -o hw/top_earlgrey/



module chip_earlgrey_verilator (
  // Clock and Reset
  input clk_i,
  input rst_ni
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
    },
    // Pad scan roles
    dio_scan_role: {
      scan_role_pkg::DioPadSpiHostCsLScanRole, // DIO spi_host0_csb
      scan_role_pkg::DioPadSpiHostClkScanRole, // DIO spi_host0_sck
      scan_role_pkg::DioPadSpiDevCsLScanRole, // DIO spi_device_csb
      scan_role_pkg::DioPadSpiDevClkScanRole, // DIO spi_device_sck
      scan_role_pkg::DioPadIor9ScanRole, // DIO sysrst_ctrl_aon_flash_wp_l
      scan_role_pkg::DioPadIor8ScanRole, // DIO sysrst_ctrl_aon_ec_rst_l
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


  //////////////////////
  // Padring Instance //
  //////////////////////

  // AST signals needed in padring - must be decleared here
  ast_pkg::ast_clks_t    ast_base_clks;
  prim_mubi_pkg::mubi4_t scanmode;

  // Padring substitute for the Verilator simulation top. The flat
  // per-peripheral cio_* signals live inside padring_verilator and
  // are driven and observed by the testbench DPI models through
  // hierarchical references (XMR).

  // USB signals routed directly to/from top_earlgrey (not via mio/dio)
  logic usb_dp_pullup_en;
  logic usb_dn_pullup_en;
  logic usb_rx_d;
  logic usb_tx_d;
  logic usb_tx_se0;
  logic usb_tx_use_d_se0;
  logic usb_rx_enable;

  padring_verilator u_padring (
    .mio_in_o  (mio_in ),
    .mio_out_i (mio_out),
    .mio_oe_i  (mio_oe ),
    .mio_attr_i(mio_attr),
    .dio_attr_i(dio_attr),

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

  //////////////////////////////////
  // AST - Common for all targets //
  //////////////////////////////////

  // pwrmgr interface
  pwrmgr_pkg::pwr_ast_req_t pwrmgr_ast_req;
  pwrmgr_pkg::pwr_ast_rsp_t pwrmgr_ast_rsp;

  // assorted ast status
  ast_pkg::ast_pwst_t    ast_pwst;
  prim_mubi_pkg::mubi4_t ast_init_done;

  // TLUL interface
  tlul_pkg::tl_h2d_t ast_tl_req;
  tlul_pkg::tl_d2h_t ast_tl_rsp;

  // Generated clocks and resets
  clkmgr_pkg::clkmgr_out_t clkmgr_aon_clocks;
  rstmgr_pkg::rstmgr_out_t rstmgr_aon_resets;

  // external clock
  logic ext_clk;

  // monitored clock
  logic sck_monitor;

  // POR signal for top
  logic [rstmgr_pkg::PowerDomains-1:0] por_n;

  // observe interface
  logic [7:0] flash_obs;
  logic [7:0] otp_obs;
  ast_pkg::ast_obs_ctrl_t obs_ctrl;

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

  // clock bypass req/ack
  prim_mubi_pkg::mubi4_t io_clk_byp_req;
  prim_mubi_pkg::mubi4_t io_clk_byp_ack;
  prim_mubi_pkg::mubi4_t all_clk_byp_req;
  prim_mubi_pkg::mubi4_t all_clk_byp_ack;
  prim_mubi_pkg::mubi4_t hi_speed_sel;
  prim_mubi_pkg::mubi4_t div_step_down_req;

  // DFT connections
  logic scan_en;
  logic scan_rst_n;
  lc_ctrl_pkg::lc_tx_t lc_dft_en;
  pinmux_pkg::dft_strap_test_req_t dft_strap_test;

  // Debug connections
  logic [ast_pkg::Ast2PadOutWidth-1:0] ast2pinmux;
  logic [ast_pkg::Pad2AstInWidth-1:0] pad2ast;

  // Jitter enable for main clock
  prim_mubi_pkg::mubi4_t clk_main_jitter_en;

  // Memory configuration connections
  prim_ram_1p_pkg::ram_1p_cfg_req_t otbn_imem_ram_cfg_req;
  prim_ram_1p_pkg::ram_1p_cfg_rsp_t otbn_imem_ram_cfg_rsp;
  prim_ram_1p_pkg::ram_1p_cfg_req_t otbn_dmem_ram_cfg_req;
  prim_ram_1p_pkg::ram_1p_cfg_rsp_t otbn_dmem_ram_cfg_rsp;
  prim_ram_1p_pkg::ram_1p_cfg_req_t i2c0_ram_cfg_req;
  prim_ram_1p_pkg::ram_1p_cfg_rsp_t i2c0_ram_cfg_rsp;
  prim_ram_1p_pkg::ram_1p_cfg_req_t i2c1_ram_cfg_req;
  prim_ram_1p_pkg::ram_1p_cfg_rsp_t i2c1_ram_cfg_rsp;
  prim_ram_1p_pkg::ram_1p_cfg_req_t i2c2_ram_cfg_req;
  prim_ram_1p_pkg::ram_1p_cfg_rsp_t i2c2_ram_cfg_rsp;
  prim_ram_1p_pkg::ram_1p_cfg_req_t usbdev_ram_cfg_req;
  prim_ram_1p_pkg::ram_1p_cfg_rsp_t usbdev_ram_cfg_rsp;
  prim_ram_1p_pkg::ram_1p_cfg_req_t [ibex_pkg::IC_NUM_WAYS-1:0]
      rv_core_ibex_icache_tag_ram_cfg_req;
  prim_ram_1p_pkg::ram_1p_cfg_rsp_t [ibex_pkg::IC_NUM_WAYS-1:0]
      rv_core_ibex_icache_tag_ram_cfg_rsp;
  prim_ram_1p_pkg::ram_1p_cfg_req_t [ibex_pkg::IC_NUM_WAYS-1:0]
      rv_core_ibex_icache_data_ram_cfg_req;
  prim_ram_1p_pkg::ram_1p_cfg_rsp_t [ibex_pkg::IC_NUM_WAYS-1:0]
      rv_core_ibex_icache_data_ram_cfg_rsp;
  prim_ram_1p_pkg::ram_1p_cfg_req_t [ast_pkg::SramCtrlMainNumRamInst-1:0]
      sram_ctrl_main_ram_cfg_req;
  prim_ram_1p_pkg::ram_1p_cfg_rsp_t [ast_pkg::SramCtrlMainNumRamInst-1:0]
      sram_ctrl_main_ram_cfg_rsp;
  prim_ram_1p_pkg::ram_1p_cfg_req_t [ast_pkg::SramCtrlRetAonNumRamInst-1:0]
      sram_ctrl_ret_aon_ram_cfg_req;
  prim_ram_1p_pkg::ram_1p_cfg_rsp_t [ast_pkg::SramCtrlRetAonNumRamInst-1:0]
      sram_ctrl_ret_aon_ram_cfg_rsp;
  prim_ram_1r1w_pkg::ram_1r1w_cfg_req_t spi_device_sys2spi_ram_cfg_req;
  prim_ram_1r1w_pkg::ram_1r1w_cfg_rsp_t spi_device_sys2spi_ram_cfg_rsp;
  prim_ram_1r1w_pkg::ram_1r1w_cfg_req_t spi_device_spi2sys_ram_cfg_req;
  prim_ram_1r1w_pkg::ram_1r1w_cfg_rsp_t spi_device_spi2sys_ram_cfg_rsp;
  prim_rom_pkg::rom_cfg_req_t rom_ctrl_rom_cfg_req;
  prim_rom_pkg::rom_cfg_rsp_t rom_ctrl_rom_cfg_rsp;

  ast_pkg::ast_mem_cfg_req_t chip_mem_cfg_req;
  ast_pkg::ast_mem_cfg_rsp_t chip_mem_cfg_rsp;
  assign otbn_imem_ram_cfg_req                     = chip_mem_cfg_req.otbn_imem;
  assign chip_mem_cfg_rsp.otbn_imem                = otbn_imem_ram_cfg_rsp;
  assign otbn_dmem_ram_cfg_req                     = chip_mem_cfg_req.otbn_dmem;
  assign chip_mem_cfg_rsp.otbn_dmem                = otbn_dmem_ram_cfg_rsp;
  assign i2c0_ram_cfg_req                          = chip_mem_cfg_req.i2c0;
  assign chip_mem_cfg_rsp.i2c0                     = i2c0_ram_cfg_rsp;
  assign i2c1_ram_cfg_req                          = chip_mem_cfg_req.i2c1;
  assign chip_mem_cfg_rsp.i2c1                     = i2c1_ram_cfg_rsp;
  assign i2c2_ram_cfg_req                          = chip_mem_cfg_req.i2c2;
  assign chip_mem_cfg_rsp.i2c2                     = i2c2_ram_cfg_rsp;
  assign usbdev_ram_cfg_req                        = chip_mem_cfg_req.usbdev_ram;
  assign chip_mem_cfg_rsp.usbdev_ram               = usbdev_ram_cfg_rsp;
  assign rv_core_ibex_icache_tag_ram_cfg_req       = chip_mem_cfg_req.rv_core_ibex_icache_tag;
  assign chip_mem_cfg_rsp.rv_core_ibex_icache_tag  = rv_core_ibex_icache_tag_ram_cfg_rsp;
  assign rv_core_ibex_icache_data_ram_cfg_req      = chip_mem_cfg_req.rv_core_ibex_icache_data;
  assign chip_mem_cfg_rsp.rv_core_ibex_icache_data = rv_core_ibex_icache_data_ram_cfg_rsp;
  assign sram_ctrl_main_ram_cfg_req                = chip_mem_cfg_req.sram_ctrl_main;
  assign chip_mem_cfg_rsp.sram_ctrl_main           = sram_ctrl_main_ram_cfg_rsp;
  assign sram_ctrl_ret_aon_ram_cfg_req             = chip_mem_cfg_req.sram_ctrl_ret_aon;
  assign chip_mem_cfg_rsp.sram_ctrl_ret_aon        = sram_ctrl_ret_aon_ram_cfg_rsp;
  assign spi_device_sys2spi_ram_cfg_req            = chip_mem_cfg_req.spi_device_sys2spi;
  assign chip_mem_cfg_rsp.spi_device_sys2spi       = spi_device_sys2spi_ram_cfg_rsp;
  assign spi_device_spi2sys_ram_cfg_req            = chip_mem_cfg_req.spi_device_spi2sys;
  assign chip_mem_cfg_rsp.spi_device_spi2sys       = spi_device_spi2sys_ram_cfg_rsp;
  assign rom_ctrl_rom_cfg_req                      = chip_mem_cfg_req.rom_ctrl_rom;
  assign chip_mem_cfg_rsp.rom_ctrl_rom             = rom_ctrl_rom_cfg_rsp;

  assign pwrmgr_ast_rsp.main_pok = ast_pwst.main_pok;
  assign por_n = {ast_pwst.main_pok, ast_pwst.aon_pok};

  //////////////////////////////////
  // AST - Custom for targets     //
  //////////////////////////////////

  assign ext_clk = '0;
  assign pad2ast = '0;

  // AON clock divider. Reset is not used because verilator uses only sync
  // resets (and does not model 'x'); if the divider below were reset, clk_aon
  // would be silenced and the clk_aon logic inside top_earlgrey would not
  // get reset.

  logic clk_aon;
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

  // POR for the AST comes directly from the reset input.
  logic rst_n;
  assign rst_n = rst_ni;

  ast_pkg::clks_osc_byp_t clks_osc_byp;
  assign clks_osc_byp = '{
    usb: clk_i,
    sys: clk_i,
    io:  clk_i,
    aon: clk_aon
  };

  // Target (Verilator) specific supply manipulation to create a synthetic POR condition.
  logic [3:0] cnt;
  logic vcc_supp;
  // keep incrementing until saturation
  always_ff @(posedge clk_aon) begin
    if (cnt < 4'hf) begin
      cnt <= cnt + 1'b1;
    end
  end
  assign vcc_supp = cnt < 4'h4 ? 1'b0 :
                    cnt < 4'h8 ? 1'b1 :
                    cnt < 4'hc ? 1'b0 : 1'b1;

  // AST does not use all clocks / resets forwarded to it
  logic unused_slow_clk_en;
  assign unused_slow_clk_en = pwrmgr_ast_req.slow_clk_en;

  logic unused_pwr_clamp;
  assign unused_pwr_clamp = pwrmgr_ast_req.pwr_clamp;


  ast u_ast (
    // external POR
    .por_ni                ( rst_n ),

    // USB IO Pull-up Calibration Setting
    .usb_io_pu_cal_o       ( ),

    // clocks' oscillator bypass for FPGA
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
    .tl_i                  ( ast_tl_req ),
    .tl_o                  ( ast_tl_rsp ),
    // init done indication
    .ast_init_done_o       ( ast_init_done ),
    // buffered clocks & resets
    .clk_ast_tlul_i (clkmgr_aon_clocks.clk_io_div4_infra),
    .clk_ast_adc_i (clkmgr_aon_clocks.clk_aon_peri),
    .clk_ast_alert_i (clkmgr_aon_clocks.clk_io_div4_secure),
    .clk_ast_es_i (clkmgr_aon_clocks.clk_main_secure),
    .clk_ast_rng_i (clkmgr_aon_clocks.clk_main_secure),
    .clk_ast_usb_i (clkmgr_aon_clocks.clk_usb_peri),
    .rst_ast_tlul_ni (rstmgr_aon_resets.rst_lc_io_div4_n[rstmgr_pkg::DomainMainSel]),
    .rst_ast_adc_ni (rstmgr_aon_resets.rst_lc_aon_n[rstmgr_pkg::DomainAonSel]),
    .rst_ast_alert_ni (rstmgr_aon_resets.rst_lc_io_div4_n[rstmgr_pkg::DomainMainSel]),
    .rst_ast_es_ni (rstmgr_aon_resets.rst_lc_n[rstmgr_pkg::DomainMainSel]),
    .rst_ast_rng_ni (rstmgr_aon_resets.rst_lc_n[rstmgr_pkg::DomainMainSel]),
    .rst_ast_usb_ni (rstmgr_aon_resets.rst_usb_n[rstmgr_pkg::DomainMainSel]),
    .clk_ast_ext_i         ( ext_clk ),

    // pok test for FPGA
    .vcc_supp_i            ( vcc_supp ),
    .vcaon_supp_i          ( 1'b1 ),
    .vcmain_supp_i         ( 1'b1 ),
    .vioa_supp_i           ( 1'b1 ),
    .viob_supp_i           ( 1'b1 ),
    // pok
    .ast_pwst_o            ( ast_pwst ),
    .ast_pwst_h_o          (  ),
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
    .lc_dft_en_i           ( lc_dft_en        ),
    .fla_obs_i             ( flash_obs ),
    .otp_obs_i             ( otp_obs ),
    .otm_obs_i             ( '0 ),
    .usb_obs_i             ( '0 ),
    .obs_ctrl_o            ( obs_ctrl ),
    // pinmux related
    .padmux2ast_i          ( pad2ast    ),
    .ast2padmux_o          ( ast2pinmux ),
    .mux_iob_sel_o         (  ),
    .ext_freq_is_96m_i     ( hi_speed_sel ),
    .all_clk_byp_req_i     ( all_clk_byp_req  ),
    .all_clk_byp_ack_o     ( all_clk_byp_ack  ),
    .io_clk_byp_req_i      ( io_clk_byp_req   ),
    .io_clk_byp_ack_o      ( io_clk_byp_ack   ),
    .flash_bist_en_o       ( flash_bist_enable ),
    // Memory configuration connections
    // Single aggregated request/response struct, driven from the AST's internal
    // SRAM configuration and fanned out to the individual cut signals above.
    .mem_cfg_req_o         ( chip_mem_cfg_req ),
    .mem_cfg_rsp_i         ( chip_mem_cfg_rsp ),
    // scan
    .dft_scan_md_o         ( scanmode   ),
    .scan_shift_en_o       ( scan_en    ),
    .scan_reset_no         ( scan_rst_n )
  );



  /////////////////////////////////////////////
  // top_earlgrey: power domains + AST //
  /////////////////////////////////////////////
  top_earlgrey #(
    .SramCtrlRetAonInstrExec(0),
    .SecAesAllowForcingMasks(1'b1),
    .SramCtrlMainInstrExec(1),
    .PinmuxAonTargetCfg(PinmuxTargetCfg)
  ) top_earlgrey (
    // Base clocks from AST
    .ast_base_clks_i(ast_base_clks),

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
    .dio_attr_o(dio_attr),

    // Regular ports (auto-generated)
    .adc_req_o                             (adc_req              ),
    .adc_rsp_i                             (adc_rsp              ),
    .ast_edn_req_i                         (ast_edn_req          ),
    .ast_edn_rsp_o                         (ast_edn_rsp          ),
    .ast_lc_dft_en_o                       (lc_dft_en            ),
    .obs_ctrl_i                            (obs_ctrl             ),
    .otbn_imem_ram_cfg_req_i               (otbn_imem_ram_cfg_req),
    .otbn_imem_ram_cfg_rsp_o               (otbn_imem_ram_cfg_rsp),
    .otbn_dmem_ram_cfg_req_i               (otbn_dmem_ram_cfg_req),
    .otbn_dmem_ram_cfg_rsp_o               (otbn_dmem_ram_cfg_rsp),
    .i2c0_ram_cfg_req_i                    (i2c0_ram_cfg_req     ),
    .i2c0_ram_cfg_rsp_o                    (i2c0_ram_cfg_rsp     ),
    .i2c1_ram_cfg_req_i                    (i2c1_ram_cfg_req     ),
    .i2c1_ram_cfg_rsp_o                    (i2c1_ram_cfg_rsp     ),
    .i2c2_ram_cfg_req_i                    (i2c2_ram_cfg_req     ),
    .i2c2_ram_cfg_rsp_o                    (i2c2_ram_cfg_rsp     ),
    .usbdev_ram_cfg_req_i                  (usbdev_ram_cfg_req   ),
    .usbdev_ram_cfg_rsp_o                  (usbdev_ram_cfg_rsp   ),
    .rv_core_ibex_icache_tag_ram_cfg_req_i (rv_core_ibex_icache_tag_ram_cfg_req),
    .rv_core_ibex_icache_tag_ram_cfg_rsp_o (rv_core_ibex_icache_tag_ram_cfg_rsp),
    .rv_core_ibex_icache_data_ram_cfg_req_i(rv_core_ibex_icache_data_ram_cfg_req),
    .rv_core_ibex_icache_data_ram_cfg_rsp_o(rv_core_ibex_icache_data_ram_cfg_rsp),
    .spi_device_sys2spi_ram_cfg_req_i      (spi_device_sys2spi_ram_cfg_req),
    .spi_device_sys2spi_ram_cfg_rsp_o      (spi_device_sys2spi_ram_cfg_rsp),
    .spi_device_spi2sys_ram_cfg_req_i      (spi_device_spi2sys_ram_cfg_req),
    .spi_device_spi2sys_ram_cfg_rsp_o      (spi_device_spi2sys_ram_cfg_rsp),
    .rom_ctrl_rom_cfg_req_i                (rom_ctrl_rom_cfg_req ),
    .rom_ctrl_rom_cfg_rsp_o                (rom_ctrl_rom_cfg_rsp ),
    .sram_ctrl_main_ram_cfg_req_i          (sram_ctrl_main_ram_cfg_req),
    .sram_ctrl_main_ram_cfg_rsp_o          (sram_ctrl_main_ram_cfg_rsp),
    .sram_ctrl_ret_aon_ram_cfg_req_i       (sram_ctrl_ret_aon_ram_cfg_req),
    .sram_ctrl_ret_aon_ram_cfg_rsp_o       (sram_ctrl_ret_aon_ram_cfg_rsp),
    .clkmgr_aon_clocks_o                   (clkmgr_aon_clocks    ),
    .clkmgr_aon_cg_en_o                    (                     ),
    .clk_main_jitter_en_o                  (clk_main_jitter_en   ),
    .io_clk_byp_req_o                      (io_clk_byp_req       ),
    .io_clk_byp_ack_i                      (io_clk_byp_ack       ),
    .all_clk_byp_req_o                     (all_clk_byp_req      ),
    .all_clk_byp_ack_i                     (all_clk_byp_ack      ),
    .hi_speed_sel_o                        (hi_speed_sel         ),
    .div_step_down_req_i                   (div_step_down_req    ),
    .calib_rdy_i                           (ast_init_done        ),
    .flash_bist_enable_i                   (flash_bist_enable    ),
    .flash_power_down_h_i                  (flash_power_down_h   ),
    .flash_power_ready_h_i                 (flash_power_ready_h  ),
    .flash_test_mode_a_io                  (                     ),
    .flash_test_voltage_h_io               (                     ),
    .flash_obs_o                           (flash_obs            ),
    .es_rng_enable_o                       (es_rng_enable        ),
    .es_rng_valid_i                        (es_rng_valid         ),
    .es_rng_bit_i                          (es_rng_bit           ),
    .es_rng_fips_o                         (es_rng_fips          ),
    .ast_tl_req_o                          (ast_tl_req           ),
    .ast_tl_rsp_i                          (ast_tl_rsp           ),
    .dft_strap_test_o                      (dft_strap_test       ),
    .dft_hold_tap_sel_i                    ('0                   ),
    .usb_dp_pullup_en_o                    (usb_dp_pullup_en     ),
    .usb_dn_pullup_en_o                    (usb_dn_pullup_en     ),
    .pwrmgr_ast_req_o                      (pwrmgr_ast_req       ),
    .pwrmgr_ast_rsp_i                      (pwrmgr_ast_rsp       ),
    .otp_macro_pwr_seq_o                   (otp_macro_pwr_seq    ),
    .otp_macro_pwr_seq_h_i                 (otp_macro_pwr_seq_h  ),
    .otp_ext_voltage_h_io                  (                     ),
    .otp_obs_o                             (otp_obs              ),
    .por_n_i                               (por_n                ),
    .rstmgr_aon_resets_o                   (rstmgr_aon_resets    ),
    .rstmgr_aon_rst_en_o                   (                     ),
    .fpga_info_i                           ('0                   ),
    .sensor_ctrl_ast_alert_req_i           (ast_alert_req        ),
    .sensor_ctrl_ast_alert_rsp_o           (ast_alert_rsp        ),
    .sensor_ctrl_ast_status_i              (ast_pwst.io_pok      ),
    .ast2pinmux_i                          (ast2pinmux           ),
    .ast_init_done_i                       (ast_init_done        ),
    .sensor_ctrl_manual_pad_attr_o         (                     ),
    .sck_monitor_o                         (sck_monitor          ),
    .usbdev_usb_rx_d_i                     (usb_rx_d             ),
    .usbdev_usb_tx_d_o                     (usb_tx_d             ),
    .usbdev_usb_tx_se0_o                   (usb_tx_se0           ),
    .usbdev_usb_tx_use_d_se0_o             (usb_tx_use_d_se0     ),
    .usbdev_usb_rx_enable_o                (usb_rx_enable        ),
    .usbdev_usb_ref_val_o                  (usb_ref_val          ),
    .usbdev_usb_ref_pulse_o                (usb_ref_pulse        )
  );

endmodule
