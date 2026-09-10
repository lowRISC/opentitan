// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_darjeeling/data/top_darjeeling.hjson
//                -o hw/top_darjeeling/


module chip_darjeeling_verilator #(
  parameter bit SecRomCtrl0DisableScrambling = 1'b0,
  parameter bit SecRomCtrl1DisableScrambling = 1'b0
) (
  // Clock and Reset
  input clk_i,
  input rst_ni
);

  import top_darjeeling_pkg::*;
  import prim_pad_wrapper_pkg::*;


  // DFT and Debug signal positions in the pinout.
  localparam pinmux_pkg::target_cfg_t PinmuxTargetCfg = '{
    // Pad types for attribute WARL behavior
    dio_pad_type: {
      BidirStd, // DIO soc_proxy_soc_gpo
      BidirStd, // DIO soc_proxy_soc_gpo
      BidirStd, // DIO soc_proxy_soc_gpo
      BidirStd, // DIO soc_proxy_soc_gpo
      BidirStd, // DIO soc_proxy_soc_gpo
      BidirStd, // DIO soc_proxy_soc_gpo
      BidirStd, // DIO soc_proxy_soc_gpo
      BidirStd, // DIO soc_proxy_soc_gpo
      BidirStd, // DIO soc_proxy_soc_gpo
      BidirStd, // DIO soc_proxy_soc_gpo
      BidirStd, // DIO soc_proxy_soc_gpo
      BidirStd, // DIO soc_proxy_soc_gpo
      BidirStd, // DIO uart0_tx
      BidirStd, // DIO spi_host0_csb
      BidirStd, // DIO spi_host0_sck
      InputStd, // DIO soc_proxy_soc_gpi
      InputStd, // DIO soc_proxy_soc_gpi
      InputStd, // DIO soc_proxy_soc_gpi
      InputStd, // DIO soc_proxy_soc_gpi
      InputStd, // DIO soc_proxy_soc_gpi
      InputStd, // DIO soc_proxy_soc_gpi
      InputStd, // DIO soc_proxy_soc_gpi
      InputStd, // DIO soc_proxy_soc_gpi
      InputStd, // DIO soc_proxy_soc_gpi
      InputStd, // DIO soc_proxy_soc_gpi
      InputStd, // DIO soc_proxy_soc_gpi
      InputStd, // DIO soc_proxy_soc_gpi
      InputStd, // DIO uart0_rx
      InputStd, // DIO spi_device_tpm_csb
      InputStd, // DIO spi_device_csb
      InputStd, // DIO spi_device_sck
      BidirStd, // DIO gpio_gpio
      BidirStd, // DIO gpio_gpio
      BidirStd, // DIO gpio_gpio
      BidirStd, // DIO gpio_gpio
      BidirStd, // DIO gpio_gpio
      BidirStd, // DIO gpio_gpio
      BidirStd, // DIO gpio_gpio
      BidirStd, // DIO gpio_gpio
      BidirStd, // DIO gpio_gpio
      BidirStd, // DIO gpio_gpio
      BidirStd, // DIO gpio_gpio
      BidirStd, // DIO gpio_gpio
      BidirStd, // DIO gpio_gpio
      BidirStd, // DIO gpio_gpio
      BidirStd, // DIO gpio_gpio
      BidirStd, // DIO gpio_gpio
      BidirStd, // DIO gpio_gpio
      BidirStd, // DIO gpio_gpio
      BidirStd, // DIO gpio_gpio
      BidirStd, // DIO gpio_gpio
      BidirStd, // DIO gpio_gpio
      BidirStd, // DIO gpio_gpio
      BidirStd, // DIO gpio_gpio
      BidirStd, // DIO gpio_gpio
      BidirStd, // DIO gpio_gpio
      BidirStd, // DIO gpio_gpio
      BidirStd, // DIO gpio_gpio
      BidirStd, // DIO gpio_gpio
      BidirStd, // DIO gpio_gpio
      BidirStd, // DIO gpio_gpio
      BidirStd, // DIO gpio_gpio
      BidirStd, // DIO gpio_gpio
      BidirStd, // DIO i2c0_sda
      BidirStd, // DIO i2c0_scl
      BidirStd, // DIO spi_device_sd
      BidirStd, // DIO spi_device_sd
      BidirStd, // DIO spi_device_sd
      BidirStd, // DIO spi_device_sd
      BidirStd, // DIO spi_host0_sd
      BidirStd, // DIO spi_host0_sd
      BidirStd, // DIO spi_host0_sd
      BidirStd  // DIO spi_host0_sd
    },
    mio_pad_type: {
      BidirStd, // MIO Pad 11
      BidirStd, // MIO Pad 10
      BidirStd, // MIO Pad 9
      BidirStd, // MIO Pad 8
      BidirStd, // MIO Pad 7
      BidirStd, // MIO Pad 6
      BidirStd, // MIO Pad 5
      BidirStd, // MIO Pad 4
      BidirStd, // MIO Pad 3
      BidirStd, // MIO Pad 2
      BidirStd, // MIO Pad 1
      BidirStd  // MIO Pad 0
    },
    // Pad scan roles
    dio_scan_role: {
      scan_role_pkg::DioPadSocGpo11ScanRole, // DIO soc_proxy_soc_gpo
      scan_role_pkg::DioPadSocGpo10ScanRole, // DIO soc_proxy_soc_gpo
      scan_role_pkg::DioPadSocGpo9ScanRole, // DIO soc_proxy_soc_gpo
      scan_role_pkg::DioPadSocGpo8ScanRole, // DIO soc_proxy_soc_gpo
      scan_role_pkg::DioPadSocGpo7ScanRole, // DIO soc_proxy_soc_gpo
      scan_role_pkg::DioPadSocGpo6ScanRole, // DIO soc_proxy_soc_gpo
      scan_role_pkg::DioPadSocGpo5ScanRole, // DIO soc_proxy_soc_gpo
      scan_role_pkg::DioPadSocGpo4ScanRole, // DIO soc_proxy_soc_gpo
      scan_role_pkg::DioPadSocGpo3ScanRole, // DIO soc_proxy_soc_gpo
      scan_role_pkg::DioPadSocGpo2ScanRole, // DIO soc_proxy_soc_gpo
      scan_role_pkg::DioPadSocGpo1ScanRole, // DIO soc_proxy_soc_gpo
      scan_role_pkg::DioPadSocGpo0ScanRole, // DIO soc_proxy_soc_gpo
      scan_role_pkg::DioPadUartTxScanRole, // DIO uart0_tx
      scan_role_pkg::DioPadSpiHostCsLScanRole, // DIO spi_host0_csb
      scan_role_pkg::DioPadSpiHostClkScanRole, // DIO spi_host0_sck
      scan_role_pkg::DioPadSocGpi11ScanRole, // DIO soc_proxy_soc_gpi
      scan_role_pkg::DioPadSocGpi10ScanRole, // DIO soc_proxy_soc_gpi
      scan_role_pkg::DioPadSocGpi9ScanRole, // DIO soc_proxy_soc_gpi
      scan_role_pkg::DioPadSocGpi8ScanRole, // DIO soc_proxy_soc_gpi
      scan_role_pkg::DioPadSocGpi7ScanRole, // DIO soc_proxy_soc_gpi
      scan_role_pkg::DioPadSocGpi6ScanRole, // DIO soc_proxy_soc_gpi
      scan_role_pkg::DioPadSocGpi5ScanRole, // DIO soc_proxy_soc_gpi
      scan_role_pkg::DioPadSocGpi4ScanRole, // DIO soc_proxy_soc_gpi
      scan_role_pkg::DioPadSocGpi3ScanRole, // DIO soc_proxy_soc_gpi
      scan_role_pkg::DioPadSocGpi2ScanRole, // DIO soc_proxy_soc_gpi
      scan_role_pkg::DioPadSocGpi1ScanRole, // DIO soc_proxy_soc_gpi
      scan_role_pkg::DioPadSocGpi0ScanRole, // DIO soc_proxy_soc_gpi
      scan_role_pkg::DioPadUartRxScanRole, // DIO uart0_rx
      scan_role_pkg::DioPadSpiDevTpmCsLScanRole, // DIO spi_device_tpm_csb
      scan_role_pkg::DioPadSpiDevCsLScanRole, // DIO spi_device_csb
      scan_role_pkg::DioPadSpiDevClkScanRole, // DIO spi_device_sck
      scan_role_pkg::DioPadGpio31ScanRole, // DIO gpio_gpio
      scan_role_pkg::DioPadGpio30ScanRole, // DIO gpio_gpio
      scan_role_pkg::DioPadGpio29ScanRole, // DIO gpio_gpio
      scan_role_pkg::DioPadGpio28ScanRole, // DIO gpio_gpio
      scan_role_pkg::DioPadGpio27ScanRole, // DIO gpio_gpio
      scan_role_pkg::DioPadGpio26ScanRole, // DIO gpio_gpio
      scan_role_pkg::DioPadGpio25ScanRole, // DIO gpio_gpio
      scan_role_pkg::DioPadGpio24ScanRole, // DIO gpio_gpio
      scan_role_pkg::DioPadGpio23ScanRole, // DIO gpio_gpio
      scan_role_pkg::DioPadGpio22ScanRole, // DIO gpio_gpio
      scan_role_pkg::DioPadGpio21ScanRole, // DIO gpio_gpio
      scan_role_pkg::DioPadGpio20ScanRole, // DIO gpio_gpio
      scan_role_pkg::DioPadGpio19ScanRole, // DIO gpio_gpio
      scan_role_pkg::DioPadGpio18ScanRole, // DIO gpio_gpio
      scan_role_pkg::DioPadGpio17ScanRole, // DIO gpio_gpio
      scan_role_pkg::DioPadGpio16ScanRole, // DIO gpio_gpio
      scan_role_pkg::DioPadGpio15ScanRole, // DIO gpio_gpio
      scan_role_pkg::DioPadGpio14ScanRole, // DIO gpio_gpio
      scan_role_pkg::DioPadGpio13ScanRole, // DIO gpio_gpio
      scan_role_pkg::DioPadGpio12ScanRole, // DIO gpio_gpio
      scan_role_pkg::DioPadGpio11ScanRole, // DIO gpio_gpio
      scan_role_pkg::DioPadGpio10ScanRole, // DIO gpio_gpio
      scan_role_pkg::DioPadGpio9ScanRole, // DIO gpio_gpio
      scan_role_pkg::DioPadGpio8ScanRole, // DIO gpio_gpio
      scan_role_pkg::DioPadGpio7ScanRole, // DIO gpio_gpio
      scan_role_pkg::DioPadGpio6ScanRole, // DIO gpio_gpio
      scan_role_pkg::DioPadGpio5ScanRole, // DIO gpio_gpio
      scan_role_pkg::DioPadGpio4ScanRole, // DIO gpio_gpio
      scan_role_pkg::DioPadGpio3ScanRole, // DIO gpio_gpio
      scan_role_pkg::DioPadGpio2ScanRole, // DIO gpio_gpio
      scan_role_pkg::DioPadGpio1ScanRole, // DIO gpio_gpio
      scan_role_pkg::DioPadGpio0ScanRole, // DIO gpio_gpio
      scan_role_pkg::DioPadI2cSdaScanRole, // DIO i2c0_sda
      scan_role_pkg::DioPadI2cSclScanRole, // DIO i2c0_scl
      scan_role_pkg::DioPadSpiDevD3ScanRole, // DIO spi_device_sd
      scan_role_pkg::DioPadSpiDevD2ScanRole, // DIO spi_device_sd
      scan_role_pkg::DioPadSpiDevD1ScanRole, // DIO spi_device_sd
      scan_role_pkg::DioPadSpiDevD0ScanRole, // DIO spi_device_sd
      scan_role_pkg::DioPadSpiHostD3ScanRole, // DIO spi_host0_sd
      scan_role_pkg::DioPadSpiHostD2ScanRole, // DIO spi_host0_sd
      scan_role_pkg::DioPadSpiHostD1ScanRole, // DIO spi_host0_sd
      scan_role_pkg::DioPadSpiHostD0ScanRole // DIO spi_host0_sd
    },
    mio_scan_role: {
      scan_role_pkg::MioPadMio11ScanRole,
      scan_role_pkg::MioPadMio10ScanRole,
      scan_role_pkg::MioPadMio9ScanRole,
      scan_role_pkg::MioPadMio8ScanRole,
      scan_role_pkg::MioPadMio7ScanRole,
      scan_role_pkg::MioPadMio6ScanRole,
      scan_role_pkg::MioPadMio5ScanRole,
      scan_role_pkg::MioPadMio4ScanRole,
      scan_role_pkg::MioPadMio3ScanRole,
      scan_role_pkg::MioPadMio2ScanRole,
      scan_role_pkg::MioPadMio1ScanRole,
      scan_role_pkg::MioPadMio0ScanRole
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

  // AST signals needed in padring
  ast_pkg::ast_clks_t    ast_base_clks;
  prim_mubi_pkg::mubi4_t scanmode;

  // Padring substitute for the Verilator simulation top. The flat
  // per-peripheral `cio_*` pad signals live inside `u_padring` (see
  // padring_verilator.sv) and are driven and observed by the testbench DPI
  // models through hierarchical references.
  padring_verilator u_padring (
    .mio_in_o  (mio_in ),
    .mio_out_i (mio_out),
    .mio_oe_i  (mio_oe ),
    .mio_attr_i(mio_attr),

    .dio_in_o (dio_in ),
    .dio_out_i(dio_out),
    .dio_oe_i (dio_oe )
  );

  //////////////////////////////////
  // AST - Common for all targets //
  //////////////////////////////////

  // pwrmgr interface
  pwrmgr_pkg::pwr_ast_req_t pwrmgr_ast_req;
  pwrmgr_pkg::pwr_ast_rsp_t pwrmgr_ast_rsp;
  pwrmgr_pkg::pwr_boot_status_t pwrmgr_boot_status;

  // assorted ast status
  ast_pkg::ast_pwst_t ast_pwst;

  // TLUL interface
  tlul_pkg::tl_h2d_t ast_tl_req;
  tlul_pkg::tl_d2h_t ast_tl_rsp;

  // Generated clocks and resets
  clkmgr_pkg::clkmgr_out_t clkmgr_clocks;
  rstmgr_pkg::rstmgr_out_t rstmgr_resets;

  // monitored clock
  logic sck_monitor;

  // observe interface
  logic [7:0] otp_obs;
  ast_pkg::ast_obs_ctrl_t obs_ctrl;

  // otp power sequence
  otp_macro_pkg::otp_ast_req_t otp_macro_pwr_seq;
  otp_macro_pkg::otp_ast_rsp_t otp_macro_pwr_seq_h;

  // OTP DFT configuration
  otp_macro_pkg::otp_cfg_t otp_cfg;
  assign otp_cfg = otp_macro_pkg::OTP_CFG_DEFAULT;

  // entropy source interface
  logic es_rng_enable, es_rng_valid;
  logic [ast_pkg::EntropyStreams-1:0] es_rng_bit;
  logic es_rng_fips;

  // DFT connections
  logic scan_en;
  logic scan_rst_n;
  lc_ctrl_pkg::lc_tx_t lc_dft_en;

  // Jitter enable
  prim_mubi_pkg::mubi4_t clk_main_jitter_en;

  // reset domain connections
  import rstmgr_pkg::PowerDomains;
  import rstmgr_pkg::DomainAonSel;
  import rstmgr_pkg::DomainMainSel;

  // Memory configuration connections
  prim_ram_1p_pkg::ram_1p_cfg_req_t otbn_imem_ram_cfg_req;
  prim_ram_1p_pkg::ram_1p_cfg_rsp_t otbn_imem_ram_cfg_rsp;
  prim_ram_1p_pkg::ram_1p_cfg_req_t otbn_dmem_ram_cfg_req;
  prim_ram_1p_pkg::ram_1p_cfg_rsp_t otbn_dmem_ram_cfg_rsp;
  prim_ram_1p_pkg::ram_1p_cfg_req_t i2c0_ram_cfg_req;
  prim_ram_1p_pkg::ram_1p_cfg_rsp_t i2c0_ram_cfg_rsp;
  prim_ram_1p_pkg::ram_1p_cfg_req_t ctn_sram_ram_cfg_req;
  prim_ram_1p_pkg::ram_1p_cfg_rsp_t ctn_sram_ram_cfg_rsp;
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
  prim_ram_1p_pkg::ram_1p_cfg_req_t [ast_pkg::SramCtrlRetNumRamInst-1:0]
      sram_ctrl_ret_ram_cfg_req;
  prim_ram_1p_pkg::ram_1p_cfg_rsp_t [ast_pkg::SramCtrlRetNumRamInst-1:0]
      sram_ctrl_ret_ram_cfg_rsp;
  prim_ram_1p_pkg::ram_1p_cfg_req_t [ast_pkg::SramCtrlMboxNumRamInst-1:0]
      sram_ctrl_mbox_ram_cfg_req;
  prim_ram_1p_pkg::ram_1p_cfg_rsp_t [ast_pkg::SramCtrlMboxNumRamInst-1:0]
      sram_ctrl_mbox_ram_cfg_rsp;
  prim_ram_1r1w_pkg::ram_1r1w_cfg_req_t spi_device_sys2spi_ram_cfg_req;
  prim_ram_1r1w_pkg::ram_1r1w_cfg_rsp_t spi_device_sys2spi_ram_cfg_rsp;
  prim_ram_1r1w_pkg::ram_1r1w_cfg_req_t spi_device_spi2sys_ram_cfg_req;
  prim_ram_1r1w_pkg::ram_1r1w_cfg_rsp_t spi_device_spi2sys_ram_cfg_rsp;
  prim_rom_pkg::rom_cfg_req_t rom_ctrl0_rom_cfg_req;
  prim_rom_pkg::rom_cfg_rsp_t rom_ctrl0_rom_cfg_rsp;
  prim_rom_pkg::rom_cfg_req_t rom_ctrl1_rom_cfg_req;
  prim_rom_pkg::rom_cfg_rsp_t rom_ctrl1_rom_cfg_rsp;

  // The AST exposes memory configuration as a single aggregated struct.
  ast_pkg::ast_mem_cfg_req_t chip_mem_cfg_req;
  ast_pkg::ast_mem_cfg_rsp_t chip_mem_cfg_rsp;
  assign otbn_imem_ram_cfg_req                     = chip_mem_cfg_req.otbn_imem;
  assign chip_mem_cfg_rsp.otbn_imem                = otbn_imem_ram_cfg_rsp;
  assign otbn_dmem_ram_cfg_req                     = chip_mem_cfg_req.otbn_dmem;
  assign chip_mem_cfg_rsp.otbn_dmem                = otbn_dmem_ram_cfg_rsp;
  assign i2c0_ram_cfg_req                          = chip_mem_cfg_req.i2c0;
  assign chip_mem_cfg_rsp.i2c0                     = i2c0_ram_cfg_rsp;
  assign ctn_sram_ram_cfg_req                      = chip_mem_cfg_req.ctn_sram;
  assign chip_mem_cfg_rsp.ctn_sram                 = ctn_sram_ram_cfg_rsp;
  assign rv_core_ibex_icache_tag_ram_cfg_req       = chip_mem_cfg_req.rv_core_ibex_icache_tag;
  assign chip_mem_cfg_rsp.rv_core_ibex_icache_tag  = rv_core_ibex_icache_tag_ram_cfg_rsp;
  assign rv_core_ibex_icache_data_ram_cfg_req      = chip_mem_cfg_req.rv_core_ibex_icache_data;
  assign chip_mem_cfg_rsp.rv_core_ibex_icache_data = rv_core_ibex_icache_data_ram_cfg_rsp;
  assign sram_ctrl_main_ram_cfg_req                = chip_mem_cfg_req.sram_ctrl_main;
  assign chip_mem_cfg_rsp.sram_ctrl_main           = sram_ctrl_main_ram_cfg_rsp;
  assign sram_ctrl_ret_ram_cfg_req                 = chip_mem_cfg_req.sram_ctrl_ret;
  assign chip_mem_cfg_rsp.sram_ctrl_ret            = sram_ctrl_ret_ram_cfg_rsp;
  assign sram_ctrl_mbox_ram_cfg_req                = chip_mem_cfg_req.sram_ctrl_mbox;
  assign chip_mem_cfg_rsp.sram_ctrl_mbox           = sram_ctrl_mbox_ram_cfg_rsp;
  assign spi_device_sys2spi_ram_cfg_req            = chip_mem_cfg_req.spi_device_sys2spi;
  assign chip_mem_cfg_rsp.spi_device_sys2spi       = spi_device_sys2spi_ram_cfg_rsp;
  assign spi_device_spi2sys_ram_cfg_req            = chip_mem_cfg_req.spi_device_spi2sys;
  assign chip_mem_cfg_rsp.spi_device_spi2sys       = spi_device_spi2sys_ram_cfg_rsp;
  assign rom_ctrl0_rom_cfg_req                     = chip_mem_cfg_req.rom_ctrl0;
  assign chip_mem_cfg_rsp.rom_ctrl0                = rom_ctrl0_rom_cfg_rsp;
  assign rom_ctrl1_rom_cfg_req                     = chip_mem_cfg_req.rom_ctrl1;
  assign chip_mem_cfg_rsp.rom_ctrl1                = rom_ctrl1_rom_cfg_rsp;


  //////////////////////////////////
  // AST - Custom for targets     //
  //////////////////////////////////


  assign pwrmgr_ast_rsp.main_pok = ast_pwst.main_pok;

  logic [rstmgr_pkg::PowerDomains-1:0] por_n;
  assign por_n = {ast_pwst.main_pok, ast_pwst.aon_pok};

  wire unused_t0, unused_t1;
  assign unused_t0 = 1'b0;
  assign unused_t1 = 1'b0;

  // AST does not use all clocks / resets forwarded to it
  logic unused_slow_clk_en;
  assign unused_slow_clk_en = pwrmgr_ast_req.slow_clk_en;

  logic unused_pwr_clamp;
  assign unused_pwr_clamp = pwrmgr_ast_req.pwr_clamp;

  // Clock and power-on-reset generation specific to the Verilator top.
  // AON clock divider. Reset is not used because verilator uses only sync
  // resets (and does not model 'x'); resetting the divider would silence
  // clk_aon and the clk_aon logic inside top_darjeeling would not reset.
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

  ast_pkg::clks_osc_byp_t clks_osc_byp;
  assign clks_osc_byp = '{
    sys: clk_i,
    io:  clk_i,
    aon: clk_aon
  };

  // Target (Verilator) specific supply manipulation to create a synthetic POR condition.
  logic [3:0] cnt;
  logic vcc_supp;
  always_ff @(posedge clk_aon) begin
    if (cnt < 4'hf) begin
      cnt <= cnt + 1'b1;
    end
  end
  assign vcc_supp = cnt < 4'h4 ? 1'b0 :
                    cnt < 4'h8 ? 1'b1 :
                    cnt < 4'hc ? 1'b0 : 1'b1;

  ast #(
    .Ast2PadOutWidth(ast_pkg::Ast2PadOutWidth),
    .Pad2AstInWidth(ast_pkg::Pad2AstInWidth)
  ) u_ast (
    // external POR
    .por_ni                ( rst_ni ),

    // Direct short to PAD
    .ast2pad_t0_ao         ( unused_t0 ),
    .ast2pad_t1_ao         ( unused_t1 ),

    // clocks and resets supplied for detection
    .sns_clks_i            ( clkmgr_clocks ),
    .sns_rsts_i            ( rstmgr_resets ),
    .sns_spi_ext_clk_i     ( sck_monitor   ),
    // clocks' oscillator bypass for verilator
    .clk_osc_byp_i         ( clks_osc_byp ),
    // tlul
    .tl_i                  ( ast_tl_req ),
    .tl_o                  ( ast_tl_rsp ),
    // init done indication
    .ast_init_done_o       ( ),
    // buffered clocks & resets
    .clk_ast_tlul_i (clkmgr_clocks.clk_io_infra),
    .clk_ast_alert_i (clkmgr_clocks.clk_io_secure),
    .clk_ast_rng_i (clkmgr_clocks.clk_main_secure),
    .rst_ast_tlul_ni (rstmgr_resets.rst_lc_io_n[rstmgr_pkg::DomainMainSel]),
    .rst_ast_alert_ni (rstmgr_resets.rst_lc_io_n[rstmgr_pkg::DomainMainSel]),
    .rst_ast_rng_ni (rstmgr_resets.rst_lc_n[rstmgr_pkg::DomainMainSel]),

    // pok test for FPGA
    .vcc_supp_i            ( vcc_supp ),
    .vcaon_supp_i          ( 1'b1 ),
    .vcmain_supp_i         ( 1'b1 ),
    .vioa_supp_i           ( 1'b1 ),
    .viob_supp_i           ( 1'b1 ),
    // pok
    .ast_pwst_o            ( ast_pwst ),
    .ast_pwst_h_o          (          ),
    // main regulator
    .main_env_iso_en_i     ( pwrmgr_ast_req.pwr_clamp_env ),
    .main_pd_ni            ( pwrmgr_ast_req.main_pd_n ),
    // pdm control (otp)
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
    // rng
    .rng_en_i              ( es_rng_enable ),
    .rng_fips_i            ( es_rng_fips   ),
    .rng_val_o             ( es_rng_valid  ),
    .rng_b_o               ( es_rng_bit    ),
    // alerts
    .alert_rsp_i           ( '{default: {ast_pkg::NumAlerts{2'b01}}} ),
    .alert_req_o           (                                         ),
    // dft
    .lc_dft_en_i           ( lc_dft_en ),
    .otp_obs_i             ( otp_obs   ),
    .otm_obs_i             ( '0        ),
    .obs_ctrl_o            ( obs_ctrl  ),
    // pinmux related
    .padmux2ast_i          ( '0 ),
    .ast2padmux_o          (    ),
    // Memory configuration connections
    // Single aggregated request/response struct, driven from the AST's internal
    // margins and fanned out to the individual cut signals above.
    .mem_cfg_req_o         ( chip_mem_cfg_req ),
    .mem_cfg_rsp_i         ( chip_mem_cfg_rsp ),
    // scan
    .dft_scan_md_o         ( scanmode   ),
    .scan_shift_en_o       ( scan_en    ),
    .scan_reset_no         ( scan_rst_n )
  );

  //////////////////
  // TAP Instance //
  //////////////////

  tlul_pkg::tl_h2d_t dmi_req;
  tlul_pkg::tl_d2h_t dmi_rsp;
  jtag_pkg::jtag_req_t jtag_req;
  jtag_pkg::jtag_rsp_t jtag_rsp;

  assign jtag_req = '{default: '0};

  logic unused_jtag_rsp;
  assign unused_jtag_rsp = ^jtag_rsp;

  tlul_jtag_dtm #(
    .IdcodeValue(jtag_id_pkg::LC_DM_COMBINED_JTAG_IDCODE),
    // Notes:
    // - one RV_DM instance uses 9bits
    // - our crossbar tooling expects individual IPs to be spaced apart by 12bits at the moment
    // - the DMI address shifted through jtag is a word address and hence 2bits smaller than this
    // - setting this to 18bits effectively gives us 2^6 = 64 addressable 12bit ranges
    .NumDmiByteAbits(18)
  ) u_tlul_jtag_dtm (
    .clk_i      (clkmgr_clocks.clk_main_infra),
    .rst_ni     (rstmgr_resets.rst_sys_n[rstmgr_pkg::DomainMainSel]),
    .jtag_i     (jtag_req),
    .jtag_o     (jtag_rsp),
    .scan_rst_ni(scan_rst_n),
    .scanmode_i (scanmode),
    .tl_h2d_o   (dmi_req),
    .tl_d2h_i   (dmi_rsp)
  );

  // TODO: Resolve this and wire it up.
  tlul_pkg::tl_h2d_t ctn_misc_tl_h2d_i;
  assign ctn_misc_tl_h2d_i = tlul_pkg::TL_H2D_DEFAULT;
  tlul_pkg::tl_d2h_t ctn_misc_tl_d2h_o;

  // TODO: Over/ride/ all access range checks for now.
  prim_mubi_pkg::mubi8_t ac_range_check_overwrite_i;
  assign ac_range_check_overwrite_i = prim_mubi_pkg::MuBi8True;

  // TODO: External RACL error input.
  top_racl_pkg::racl_error_log_t ext_racl_error;
  assign ext_racl_error = '0;

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
    .clk_i  (clkmgr_clocks.clk_main_infra),
    .rst_ni (rstmgr_resets.rst_lc_n[rstmgr_pkg::DomainMainSel]),
    .tl_h_i (ctn_tl_h2d),
    .tl_h_o (ctn_tl_d2h),
    .tl_d_o (ctn_sm1_to_s1n_tl_h2d),
    .tl_d_i (ctn_sm1_to_s1n_tl_d2h)
  );

  ////////////////////////////////////////////
  // CTN Address decoding and SRAM Instance //
  ////////////////////////////////////////////

  localparam int CtnSramDw = top_pkg::TL_DW + tlul_pkg::DataIntgWidth;

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
    if ((ctn_sm1_to_s1n_tl_h2d.a_address & ~(TOP_DARJEELING_SOC_PROXY_RAM_CTN_SIZE_BYTES-1)) ==
        (TOP_DARJEELING_SOC_PROXY_RAM_CTN_BASE_ADDR - TOP_DARJEELING_SOC_PROXY_CTN_BASE_ADDR)) begin
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
    .clk_i        (clkmgr_clocks.clk_main_infra),
    .rst_ni       (rstmgr_resets.rst_lc_n[rstmgr_pkg::DomainMainSel]),
    .tl_h_i       (ctn_sm1_to_s1n_tl_h2d),
    .tl_h_o       (ctn_sm1_to_s1n_tl_d2h),
    .tl_d_o       (ctn_s1n_tl_h2d),
    .tl_d_i       (ctn_s1n_tl_d2h),
    .dev_select_i (ctn_dev_sel_s1n)
  );

  tlul_adapter_sram #(
    .SramAw(top_pkg::CtnSramAw),
    .SramDw(CtnSramDw - tlul_pkg::DataIntgWidth),
    .Outstanding(2),
    .ByteAccess(1),
    .CmdIntgCheck(1),
    .EnableRspIntgGen(1),
    .EnableDataIntgGen(0),
    .EnableDataIntgPt(1),
    .SecFifoPtr      (0)
  ) u_tlul_adapter_sram_ctn (
    .clk_i       (clkmgr_clocks.clk_main_infra),
    .rst_ni      (rstmgr_resets.rst_lc_n[rstmgr_pkg::DomainMainSel]),
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
    .clk_i    (clkmgr_clocks.clk_main_infra),
    .rst_ni   (rstmgr_resets.rst_lc_n[rstmgr_pkg::DomainMainSel]),
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
    .cfg_i(ctn_sram_ram_cfg_req),
    .cfg_o(ctn_sram_ram_cfg_rsp),
    .alert_o()
  );


  // The power manager waits until the external reset request is removed by the SoC before
  // proceeding to boot after an internal reset request. DV may also drive this signal briefly and
  // asynchronously to request a reset on behalf of the simulated SoC.
  //
  // Note that since the signal is filtered inside the SoC proxy it must be of at least 5
  // AON clock periods in duration.
  logic soc_rst_req_async;
  assign soc_rst_req_async = 1'b0;


  //////////////////////////////////////////////
  // top_darjeeling power domains wrapper //
  //////////////////////////////////////////////
  top_darjeeling #(
    .SecAesAllowForcingMasks(1'b1),
    .SecRomCtrl0DisableScrambling(SecRomCtrl0DisableScrambling),
    .SecRomCtrl1DisableScrambling(SecRomCtrl1DisableScrambling),
    .PinmuxTargetCfg(PinmuxTargetCfg)
  ) top_darjeeling (
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
    .ast_lc_dft_en_o                       (lc_dft_en                ),
    .ast_lc_hw_debug_en_o                  (                         ),
    .obs_ctrl_i                            (obs_ctrl                 ),
    .otbn_imem_ram_cfg_req_i               (otbn_imem_ram_cfg_req    ),
    .otbn_imem_ram_cfg_rsp_o               (otbn_imem_ram_cfg_rsp    ),
    .otbn_dmem_ram_cfg_req_i               (otbn_dmem_ram_cfg_req    ),
    .otbn_dmem_ram_cfg_rsp_o               (otbn_dmem_ram_cfg_rsp    ),
    .i2c0_ram_cfg_req_i                    (i2c0_ram_cfg_req         ),
    .i2c0_ram_cfg_rsp_o                    (i2c0_ram_cfg_rsp         ),
    .rv_core_ibex_icache_tag_ram_cfg_req_i (rv_core_ibex_icache_tag_ram_cfg_req),
    .rv_core_ibex_icache_tag_ram_cfg_rsp_o (rv_core_ibex_icache_tag_ram_cfg_rsp),
    .rv_core_ibex_icache_data_ram_cfg_req_i(rv_core_ibex_icache_data_ram_cfg_req),
    .rv_core_ibex_icache_data_ram_cfg_rsp_o(rv_core_ibex_icache_data_ram_cfg_rsp),
    .spi_device_sys2spi_ram_cfg_req_i      (spi_device_sys2spi_ram_cfg_req),
    .spi_device_sys2spi_ram_cfg_rsp_o      (spi_device_sys2spi_ram_cfg_rsp),
    .spi_device_spi2sys_ram_cfg_req_i      (spi_device_spi2sys_ram_cfg_req),
    .spi_device_spi2sys_ram_cfg_rsp_o      (spi_device_spi2sys_ram_cfg_rsp),
    .rom_ctrl0_rom_cfg_req_i               (rom_ctrl0_rom_cfg_req    ),
    .rom_ctrl0_rom_cfg_rsp_o               (rom_ctrl0_rom_cfg_rsp    ),
    .rom_ctrl1_rom_cfg_req_i               (rom_ctrl1_rom_cfg_req    ),
    .rom_ctrl1_rom_cfg_rsp_o               (rom_ctrl1_rom_cfg_rsp    ),
    .sram_ctrl_main_ram_cfg_req_i          (sram_ctrl_main_ram_cfg_req),
    .sram_ctrl_main_ram_cfg_rsp_o          (sram_ctrl_main_ram_cfg_rsp),
    .sram_ctrl_ret_ram_cfg_req_i           (sram_ctrl_ret_ram_cfg_req),
    .sram_ctrl_ret_ram_cfg_rsp_o           (sram_ctrl_ret_ram_cfg_rsp),
    .sram_ctrl_mbox_ram_cfg_req_i          (sram_ctrl_mbox_ram_cfg_req),
    .sram_ctrl_mbox_ram_cfg_rsp_o          (sram_ctrl_mbox_ram_cfg_rsp),
    .pwrmgr_boot_status_obs_o              (pwrmgr_boot_status       ),
    .pwrmgr_ext_rst_ack_i                  (1'b0                     ),
    .clkmgr_clocks_o                       (clkmgr_clocks            ),
    .clkmgr_cg_en_o                        (                         ),
    .clk_main_jitter_en_o                  (clk_main_jitter_en       ),
    .dma_sys_req_o                         (                         ),
    .dma_sys_rsp_i                         (dma_pkg::SYS_RSP_DEFAULT ),
    .es_rng_enable_o                       (es_rng_enable            ),
    .es_rng_valid_i                        (es_rng_valid             ),
    .es_rng_bit_i                          (es_rng_bit               ),
    .es_rng_fips_o                         (es_rng_fips              ),
    .mbx_tl_req_i                          (tlul_pkg::TL_H2D_DEFAULT ),
    .mbx_tl_rsp_o                          (                         ),
    .mbx0_doe_intr_o                       (                         ),
    .mbx0_doe_intr_en_o                    (                         ),
    .mbx0_doe_intr_support_o               (                         ),
    .mbx0_doe_async_msg_support_o          (                         ),
    .mbx1_doe_intr_o                       (                         ),
    .mbx1_doe_intr_en_o                    (                         ),
    .mbx1_doe_intr_support_o               (                         ),
    .mbx1_doe_async_msg_support_o          (                         ),
    .mbx2_doe_intr_o                       (                         ),
    .mbx2_doe_intr_en_o                    (                         ),
    .mbx2_doe_intr_support_o               (                         ),
    .mbx2_doe_async_msg_support_o          (                         ),
    .mbx3_doe_intr_o                       (                         ),
    .mbx3_doe_intr_en_o                    (                         ),
    .mbx3_doe_intr_support_o               (                         ),
    .mbx3_doe_async_msg_support_o          (                         ),
    .mbx4_doe_intr_o                       (                         ),
    .mbx4_doe_intr_en_o                    (                         ),
    .mbx4_doe_intr_support_o               (                         ),
    .mbx4_doe_async_msg_support_o          (                         ),
    .mbx5_doe_intr_o                       (                         ),
    .mbx5_doe_intr_en_o                    (                         ),
    .mbx5_doe_intr_support_o               (                         ),
    .mbx5_doe_async_msg_support_o          (                         ),
    .mbx6_doe_intr_o                       (                         ),
    .mbx6_doe_intr_en_o                    (                         ),
    .mbx6_doe_intr_support_o               (                         ),
    .mbx6_doe_async_msg_support_o          (                         ),
    .mbx_jtag_doe_intr_o                   (                         ),
    .mbx_jtag_doe_intr_en_o                (                         ),
    .mbx_jtag_doe_intr_support_o           (                         ),
    .mbx_jtag_doe_async_msg_support_o      (                         ),
    .mbx_pcie0_doe_intr_o                  (                         ),
    .mbx_pcie0_doe_intr_en_o               (                         ),
    .mbx_pcie0_doe_intr_support_o          (                         ),
    .mbx_pcie0_doe_async_msg_support_o     (                         ),
    .mbx_pcie1_doe_intr_o                  (                         ),
    .mbx_pcie1_doe_intr_en_o               (                         ),
    .mbx_pcie1_doe_intr_support_o          (                         ),
    .mbx_pcie1_doe_async_msg_support_o     (                         ),
    .dbg_tl_req_i                          (dmi_req                  ),
    .dbg_tl_rsp_o                          (dmi_rsp                  ),
    .rv_dm_next_dm_addr_i                  ('0                       ),
    .ast_tl_req_o                          (ast_tl_req               ),
    .ast_tl_rsp_i                          (ast_tl_rsp               ),
    .pwrmgr_ast_req_o                      (pwrmgr_ast_req           ),
    .pwrmgr_ast_rsp_i                      (pwrmgr_ast_rsp           ),
    .otp_macro_pwr_seq_o                   (otp_macro_pwr_seq        ),
    .otp_macro_pwr_seq_h_i                 (otp_macro_pwr_seq_h      ),
    .otp_ext_voltage_h_io                  (                         ),
    .otp_obs_o                             (otp_obs                  ),
    .otp_cfg_i                             (otp_cfg                  ),
    .por_n_i                               (por_n                    ),
    .rstmgr_resets_o                       (rstmgr_resets            ),
    .rstmgr_rst_en_o                       (                         ),
    .fpga_info_i                           ('0                       ),
    .ctn_misc_tl_h2d_i                     (ctn_misc_tl_h2d_i        ),
    .ctn_misc_tl_d2h_o                     (ctn_misc_tl_d2h_o        ),
    .soc_wkup_async_i                      (1'b0                     ),
    .soc_rst_req_async_i                   (soc_rst_req_async        ),
    .soc_lsio_trigger_i                    ('0                       ),
    .soc_gpi_async_o                       (                         ),
    .soc_gpo_async_i                       ('0                       ),
    .integrator_id_i                       ('0                       ),
    .sck_monitor_o                         (sck_monitor              ),
    .soc_dbg_policy_bus_o                  (                         ),
    .debug_halt_cpu_boot_i                 (1'b0                     ),
    .racl_policies_o                       (                         ),
    .racl_error_i                          (ext_racl_error           ),
    .ac_range_check_overwrite_i            (ac_range_check_overwrite_i),
    .ctn_tl_h2d_o                          (ctn_tl_h2d[0]            ),
    .ctn_tl_d2h_i                          (ctn_tl_d2h[0]            )
  );

  // pwrmgr_boot_status is only used for dv observability
  logic unused_signals;
  assign unused_signals = ^{pwrmgr_boot_status.clk_status,
                            pwrmgr_boot_status.cpu_fetch_en,
                            pwrmgr_boot_status.lc_done,
                            pwrmgr_boot_status.otp_done,
                            pwrmgr_boot_status.rom_ctrl_status,
                            pwrmgr_boot_status.strap_sampled,
                            pwrmgr_boot_status.light_reset_req};

endmodule
