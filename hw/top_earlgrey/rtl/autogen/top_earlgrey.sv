// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_earlgrey/data/top_earlgrey.hjson
//                -o hw/top_earlgrey/


// This wrapper hosts all power domain wrappers and the connections between them for earlgrey.
module top_earlgrey #(
  // Auto-inferred parameters
  // parameters for gpio
  parameter bit GpioGpioAsyncOn = 1,
  parameter bit GpioGpioAsHwStrapsEn = 0,
  // parameters for spi_device
  parameter spi_device_pkg::sram_type_e SpiDeviceSramType = spi_device_pkg::SramType1r1w,
  // parameters for i2c0
  parameter int I2c0InputDelayCycles = 0,
  // parameters for i2c1
  parameter int I2c1InputDelayCycles = 0,
  // parameters for i2c2
  parameter int I2c2InputDelayCycles = 0,
  // parameters for otp_macro
  parameter OtpMacroMemInitFile = "",
  // parameters for lc_ctrl
  parameter bit SecLcCtrlVolatileRawUnlockEn = top_pkg::SecVolatileRawUnlockEn,
  parameter bit LcCtrlUseDmiInterface = 0,
  parameter logic [15:0] LcCtrlSiliconCreatorId = 16'h 4001,
  parameter logic [15:0] LcCtrlProductId = 16'h 0010,
  parameter logic [7:0] LcCtrlRevisionId = 8'h 01,
  parameter logic [31:0] LcCtrlIdcodeValue = jtag_id_pkg::LC_CTRL_JTAG_IDCODE,
  // parameters for alert_handler
  parameter int AlertHandlerEscNumSeverities = 4,
  parameter int AlertHandlerEscPingCountWidth = 16,
  // parameters for usbdev
  parameter bit UsbdevStub = 0,
  parameter int UsbdevRcvrWakeTimeUs = 100,
  // parameters for rstmgr
  parameter bit SecRstmgrCheck = 1'b1,
  parameter int SecRstmgrMaxSyncDelay = 2,
  // parameters for pinmux
  parameter bit SecPinmuxVolatileRawUnlockEn = top_pkg::SecVolatileRawUnlockEn,
  parameter pinmux_pkg::target_cfg_t PinmuxTargetCfg = pinmux_pkg::DefaultTargetCfg,
  // parameters for sram_ctrl_ret
  parameter int SramCtrlRetInstSize = 4096,
  parameter int SramCtrlRetNumRamInst = 1,
  parameter bit SramCtrlRetInstrExec = 0,
  parameter int SramCtrlRetNumPrinceRoundsHalf = 3,
  parameter bit SramCtrlRetEccCorrection = 0,
  // parameters for flash_ctrl
  parameter bit SecFlashCtrlScrambleEn = 1,
  parameter int FlashCtrlProgFifoDepth = 4,
  parameter int FlashCtrlRdFifoDepth = 16,
  // parameters for rram_ctrl
  parameter bit SecRramCtrlScrambleEn = 1,
  parameter int RramCtrlWrFifoDepth = 4,
  parameter int RramCtrlRdFifoDepth = 16,
  // parameters for rv_dm
  parameter logic [31:0] RvDmIdcodeValue = jtag_id_pkg::RV_DM_JTAG_IDCODE,
  parameter bit RvDmUseDmiInterface = 0,
  parameter bit SecRvDmVolatileRawUnlockEn = 1'b0,
  parameter logic [tlul_pkg::RsvdWidth-1:0] RvDmTlulHostUserRsvdBits = '0,
  // parameters for aes
  parameter bit AesAESGCMEnable = 0,
  parameter bit SecAesMasking = 1,
  parameter aes_pkg::sbox_impl_e SecAesSBoxImpl = aes_pkg::SBoxImplDom,
  parameter int unsigned SecAesStartTriggerDelay = 0,
  parameter bit SecAesAllowForcingMasks = 1'b0,
  parameter bit SecAesSkipPRNGReseeding = 1'b0,
  // parameters for kmac
  parameter bit KmacEnMasking = 1,
  parameter bit KmacSwKeyMasked = 0,
  parameter int SecKmacCmdDelay = 0,
  parameter bit SecKmacIdleAcceptSwMsg = 0,
  parameter int KmacNumAppIntf = 4,
  parameter kmac_pkg::app_config_t KmacAppCfg[KmacNumAppIntf] =
      '{kmac_pkg::AppCfgKeyMgr, kmac_pkg::AppCfgLcCtrl, kmac_pkg::AppCfgRomCtrl, kmac_pkg::AppCfgOtbn},
  // parameters for otbn
  parameter bit OtbnStub = 0,
  parameter otbn_pkg::regfile_e OtbnRegFile = otbn_pkg::RegFileFF,
  parameter bit SecOtbnMuteUrnd = 0,
  parameter bit SecOtbnFixMaiOpSeq = 0,
  parameter bit SecOtbnSkipUrndReseedAtStart = 0,
  parameter bit OtbnFeatStubMai = 0,
  // parameters for keymgr
  parameter bit KeymgrUseOtpSeedsInsteadOfFlash = 0,
  parameter bit KeymgrKmacEnMasking = 1,
  // parameters for csrng
  parameter aes_pkg::sbox_impl_e CsrngSBoxImpl = aes_pkg::SBoxImplCanright,
  // parameters for entropy_src
  parameter int EntropySrcRngBusWidth = 4,
  parameter int EntropySrcRngBusBitSelWidth = 2,
  parameter int EntropySrcHealthTestWindowWidth = 18,
  parameter bit EntropySrcStub = 0,
  // parameters for sram_ctrl_main
  parameter int SramCtrlMainInstSize = 131072,
  parameter int SramCtrlMainNumRamInst = 1,
  parameter bit SramCtrlMainInstrExec = 1,
  parameter int SramCtrlMainNumPrinceRoundsHalf = 2,
  parameter bit SramCtrlMainEccCorrection = 0,
  // parameters for rom_ctrl
  parameter RomCtrlBootRomInitFile = "",
  parameter bit SecRomCtrlDisableScrambling = 1'b0,
  // parameters for rv_core_ibex
  parameter bit RvCoreIbexPMPEnable = 1,
  parameter int unsigned RvCoreIbexPMPGranularity = 0,
  parameter int unsigned RvCoreIbexPMPNumRegions = 16,
  parameter int unsigned RvCoreIbexMHPMCounterNum = 2,
  parameter int unsigned RvCoreIbexMHPMCounterWidth = 32,
  parameter ibex_pkg::pmp_cfg_t RvCoreIbexPMPRstCfg[16] = ibex_pmp_reset_pkg::PmpCfgRst,
  parameter logic [33:0] RvCoreIbexPMPRstAddr[16] = ibex_pmp_reset_pkg::PmpAddrRst,
  parameter ibex_pkg::pmp_mseccfg_t RvCoreIbexPMPRstMsecCfg = ibex_pmp_reset_pkg::PmpMseccfgRst,
  parameter bit RvCoreIbexRV32E = 0,
  parameter ibex_pkg::rv32m_e RvCoreIbexRV32M = ibex_pkg::RV32MSingleCycle,
  parameter ibex_pkg::rv32b_e RvCoreIbexRV32B = ibex_pkg::RV32BOTEarlGrey,
  parameter ibex_pkg::rv32zc_e RvCoreIbexRV32ZC = ibex_pkg::RV32ZcaZcbZcmp,
  parameter ibex_pkg::regfile_e RvCoreIbexRegFile = ibex_pkg::RegFileFF,
  parameter bit RvCoreIbexBranchTargetALU = 1,
  parameter bit RvCoreIbexWritebackStage = 1,
  parameter bit RvCoreIbexICache = 1,
  parameter bit RvCoreIbexICacheECC = 1,
  parameter bit RvCoreIbexICacheScramble = 1,
  parameter int unsigned RvCoreIbexICacheNWays = 2,
  parameter bit RvCoreIbexBranchPredictor = 0,
  parameter bit RvCoreIbexDbgTriggerEn = 1,
  parameter int RvCoreIbexDbgHwBreakNum = 4,
  parameter bit RvCoreIbexSecureIbex = 1,
  parameter int unsigned RvCoreIbexDmBaseAddr = tl_main_pkg::ADDR_SPACE_RV_DM__MEM,
  parameter int unsigned RvCoreIbexDmAddrMask = tl_main_pkg::ADDR_MASK_RV_DM__MEM,
  parameter int unsigned RvCoreIbexDmHaltAddr =
      tl_main_pkg::ADDR_SPACE_RV_DM__MEM + dm::HaltAddress[31:0],
  parameter int unsigned RvCoreIbexDmExceptionAddr =
      tl_main_pkg::ADDR_SPACE_RV_DM__MEM + dm::ExceptionAddress[31:0],
  parameter bit RvCoreIbexPipeLine = 0,
  parameter logic [tlul_pkg::RsvdWidth-1:0] RvCoreIbexTlulHostUserRsvdBits = '0,
  parameter logic [31:0] RvCoreIbexCsrMvendorId = '0,
  parameter logic [31:0] RvCoreIbexCsrMimpId = '0
) (
  // Base clocks from AST
  input ast_pkg::ast_clks_t ast_base_clks_i,

  // Manual DFT signals
  input                        scan_rst_ni, // reset used for test mode
  input                        scan_en_i,
  input prim_mubi_pkg::mubi4_t scanmode_i,  // lc_ctrl_pkg::On for Scan

  // Multiplexed I/O
  input  logic [46:0] mio_in_i,
  output logic [46:0] mio_out_o,
  output logic [46:0] mio_oe_o,

  // Dedicated I/O
  input  logic [15:0] dio_in_i,
  output logic [15:0] dio_out_o,
  output logic [15:0] dio_oe_o,

  // Pad attributes to padring
  output prim_pad_wrapper_pkg::pad_attr_t [pinmux_reg_pkg::NMioPads-1:0] mio_attr_o,
  output prim_pad_wrapper_pkg::pad_attr_t [pinmux_reg_pkg::NDioPads-1:0] dio_attr_o,

  // Inter-module Signal External type
  output ast_pkg::adc_ast_req_t       adc_req_o,
  input  ast_pkg::adc_ast_rsp_t       adc_rsp_i,
  input  edn_pkg::edn_req_t       ast_edn_req_i,
  output edn_pkg::edn_rsp_t       ast_edn_rsp_o,
  output lc_ctrl_pkg::lc_tx_t       ast_lc_dft_en_o,
  input  ast_pkg::ast_obs_ctrl_t       obs_ctrl_i,
  input  prim_ram_1p_pkg::ram_1p_cfg_req_t       otbn_imem_ram_cfg_req_i,
  output prim_ram_1p_pkg::ram_1p_cfg_rsp_t       otbn_imem_ram_cfg_rsp_o,
  input  prim_ram_1p_pkg::ram_1p_cfg_req_t       otbn_dmem_ram_cfg_req_i,
  output prim_ram_1p_pkg::ram_1p_cfg_rsp_t       otbn_dmem_ram_cfg_rsp_o,
  input  prim_ram_1p_pkg::ram_1p_cfg_req_t       i2c0_ram_cfg_req_i,
  output prim_ram_1p_pkg::ram_1p_cfg_rsp_t       i2c0_ram_cfg_rsp_o,
  input  prim_ram_1p_pkg::ram_1p_cfg_req_t       i2c1_ram_cfg_req_i,
  output prim_ram_1p_pkg::ram_1p_cfg_rsp_t       i2c1_ram_cfg_rsp_o,
  input  prim_ram_1p_pkg::ram_1p_cfg_req_t       i2c2_ram_cfg_req_i,
  output prim_ram_1p_pkg::ram_1p_cfg_rsp_t       i2c2_ram_cfg_rsp_o,
  input  prim_ram_1p_pkg::ram_1p_cfg_req_t       usbdev_ram_cfg_req_i,
  output prim_ram_1p_pkg::ram_1p_cfg_rsp_t       usbdev_ram_cfg_rsp_o,
  input  prim_ram_1p_pkg::ram_1p_cfg_req_t [RvCoreIbexICacheNWays-1:0] rv_core_ibex_icache_tag_ram_cfg_req_i,
  output prim_ram_1p_pkg::ram_1p_cfg_rsp_t [RvCoreIbexICacheNWays-1:0] rv_core_ibex_icache_tag_ram_cfg_rsp_o,
  input  prim_ram_1p_pkg::ram_1p_cfg_req_t [RvCoreIbexICacheNWays-1:0] rv_core_ibex_icache_data_ram_cfg_req_i,
  output prim_ram_1p_pkg::ram_1p_cfg_rsp_t [RvCoreIbexICacheNWays-1:0] rv_core_ibex_icache_data_ram_cfg_rsp_o,
  input  prim_ram_1r1w_pkg::ram_1r1w_cfg_req_t       spi_device_sys2spi_ram_cfg_req_i,
  output prim_ram_1r1w_pkg::ram_1r1w_cfg_rsp_t       spi_device_sys2spi_ram_cfg_rsp_o,
  input  prim_ram_1r1w_pkg::ram_1r1w_cfg_req_t       spi_device_spi2sys_ram_cfg_req_i,
  output prim_ram_1r1w_pkg::ram_1r1w_cfg_rsp_t       spi_device_spi2sys_ram_cfg_rsp_o,
  input  prim_rom_pkg::rom_cfg_req_t       rom_ctrl_rom_cfg_req_i,
  output prim_rom_pkg::rom_cfg_rsp_t       rom_ctrl_rom_cfg_rsp_o,
  input  prim_ram_1p_pkg::ram_1p_cfg_req_t [SramCtrlMainNumRamInst-1:0] sram_ctrl_main_ram_cfg_req_i,
  output prim_ram_1p_pkg::ram_1p_cfg_rsp_t [SramCtrlMainNumRamInst-1:0] sram_ctrl_main_ram_cfg_rsp_o,
  input  prim_ram_1p_pkg::ram_1p_cfg_req_t [SramCtrlRetNumRamInst-1:0] sram_ctrl_ret_ram_cfg_req_i,
  output prim_ram_1p_pkg::ram_1p_cfg_rsp_t [SramCtrlRetNumRamInst-1:0] sram_ctrl_ret_ram_cfg_rsp_o,
  output clkmgr_pkg::clkmgr_out_t       clkmgr_clocks_o,
  output clkmgr_pkg::clkmgr_cg_en_t       clkmgr_cg_en_o,
  output prim_mubi_pkg::mubi4_t       clk_main_jitter_en_o,
  output prim_mubi_pkg::mubi4_t       io_clk_byp_req_o,
  input  prim_mubi_pkg::mubi4_t       io_clk_byp_ack_i,
  output prim_mubi_pkg::mubi4_t       all_clk_byp_req_o,
  input  prim_mubi_pkg::mubi4_t       all_clk_byp_ack_i,
  output prim_mubi_pkg::mubi4_t       hi_speed_sel_o,
  input  prim_mubi_pkg::mubi4_t       div_step_down_req_i,
  input  prim_mubi_pkg::mubi4_t       calib_rdy_i,
  input  prim_mubi_pkg::mubi4_t       flash_bist_enable_i,
  input  logic       flash_power_down_h_i,
  input  logic       flash_power_ready_h_i,
  inout   [1:0] flash_test_mode_a_io,
  inout         flash_test_voltage_h_io,
  output logic [7:0] flash_obs_o,
  output logic       es_rng_enable_o,
  input  logic       es_rng_valid_i,
  input  logic [EntropySrcRngBusWidth-1:0] es_rng_bit_i,
  output logic       es_rng_fips_o,
  output tlul_pkg::tl_h2d_t       ast_tl_req_o,
  input  tlul_pkg::tl_d2h_t       ast_tl_rsp_i,
  output pinmux_pkg::dft_strap_test_req_t       dft_strap_test_o,
  input  logic       dft_hold_tap_sel_i,
  output logic       usb_dp_pullup_en_o,
  output logic       usb_dn_pullup_en_o,
  output pwrmgr_pkg::pwr_ast_req_t       pwrmgr_ast_req_o,
  input  pwrmgr_pkg::pwr_ast_rsp_t       pwrmgr_ast_rsp_i,
  output otp_macro_pkg::pwr_seq_t       otp_macro_pwr_seq_o,
  input  otp_macro_pkg::pwr_seq_t       otp_macro_pwr_seq_h_i,
  inout         otp_ext_voltage_h_io,
  output logic [7:0] otp_obs_o,
  input  logic [1:0] por_n_i,
  output rstmgr_pkg::rstmgr_out_t       rstmgr_resets_o,
  output rstmgr_pkg::rstmgr_rst_en_t       rstmgr_rst_en_o,
  input  logic [31:0] fpga_info_i,
  input  ast_pkg::ast_alert_req_t       sensor_ctrl_ast_alert_req_i,
  output ast_pkg::ast_alert_rsp_t       sensor_ctrl_ast_alert_rsp_o,
  input  ast_pkg::ast_status_t       sensor_ctrl_ast_status_i,
  input  logic [8:0] ast2pinmux_i,
  input  prim_mubi_pkg::mubi4_t       ast_init_done_i,
  output prim_pad_wrapper_pkg::pad_attr_t [3:0] sensor_ctrl_manual_pad_attr_o,
  output logic       sck_monitor_o,
  input  logic       usbdev_usb_rx_d_i,
  output logic       usbdev_usb_tx_d_o,
  output logic       usbdev_usb_tx_se0_o,
  output logic       usbdev_usb_tx_use_d_se0_o,
  output logic       usbdev_usb_rx_enable_o,
  output logic       usbdev_usb_ref_val_o,
  output logic       usbdev_usb_ref_pulse_o

);

  import top_earlgrey_pkg::*;
  import prim_pad_wrapper_pkg::*;

  // Inter-Power Domain signals
  logic [6:0] intr_vector_pd_aon;
  prim_alert_pkg::alert_tx_t [10:0] alert_tx_pd_aon;
  prim_alert_pkg::alert_rx_t [10:0] alert_rx_pd_aon;
  alert_handler_pkg::alert_crashdump_t       alert_handler_crashdump;
  prim_esc_pkg::esc_rx_t       alert_handler_esc_rx;
  prim_esc_pkg::esc_tx_t       alert_handler_esc_tx;
  logic       aon_timer_nmi_wdog_timer_bark;
  otp_ctrl_pkg::sram_otp_key_req_t       otp_ctrl_sram_otp_key_req;
  otp_ctrl_pkg::sram_otp_key_rsp_t       otp_ctrl_sram_otp_key_rsp;
  pwrmgr_pkg::pwr_nvm_t       pwrmgr_pwr_nvm;
  pwrmgr_pkg::pwr_otp_req_t       pwrmgr_pwr_otp_req;
  pwrmgr_pkg::pwr_otp_rsp_t       pwrmgr_pwr_otp_rsp;
  lc_ctrl_pkg::pwr_lc_req_t       pwrmgr_pwr_lc_req;
  lc_ctrl_pkg::pwr_lc_rsp_t       pwrmgr_pwr_lc_rsp;
  logic       pwrmgr_strap;
  logic       pwrmgr_low_power;
  lc_ctrl_pkg::lc_tx_t       pwrmgr_fetch_en;
  rom_ctrl_pkg::pwrmgr_data_t       rom_ctrl_pwrmgr_data;
  prim_mubi_pkg::mubi4_t [3:0] clkmgr_idle;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_dft_en;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_hw_debug_en;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_escalate_en;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_clk_byp_req;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_clk_byp_ack;
  rv_core_ibex_pkg::cpu_crash_dump_t       rv_core_ibex_crash_dump;
  rv_core_ibex_pkg::cpu_pwrmgr_t       rv_core_ibex_pwrmgr;
  logic       rv_dm_ndmreset_req;
  logic [1:0] pwrmgr_wakeups;
  tlul_pkg::tl_h2d_t       pwrmgr_tl_req;
  tlul_pkg::tl_d2h_t       pwrmgr_tl_rsp;
  tlul_pkg::tl_h2d_t       rstmgr_tl_req;
  tlul_pkg::tl_d2h_t       rstmgr_tl_rsp;
  tlul_pkg::tl_h2d_t       clkmgr_tl_req;
  tlul_pkg::tl_d2h_t       clkmgr_tl_rsp;
  tlul_pkg::tl_h2d_t       sensor_ctrl_tl_req;
  tlul_pkg::tl_d2h_t       sensor_ctrl_tl_rsp;
  tlul_pkg::tl_h2d_t       sram_ctrl_ret_regs_tl_req;
  tlul_pkg::tl_d2h_t       sram_ctrl_ret_regs_tl_rsp;
  tlul_pkg::tl_h2d_t       sram_ctrl_ret_ram_tl_req;
  tlul_pkg::tl_d2h_t       sram_ctrl_ret_ram_tl_rsp;
  tlul_pkg::tl_h2d_t       aon_timer_tl_req;
  tlul_pkg::tl_d2h_t       aon_timer_tl_rsp;
  tlul_pkg::tl_h2d_t       sysrst_ctrl_tl_req;
  tlul_pkg::tl_d2h_t       sysrst_ctrl_tl_rsp;
  tlul_pkg::tl_h2d_t       adc_ctrl_tl_req;
  tlul_pkg::tl_d2h_t       adc_ctrl_tl_rsp;
  logic       cio_sysrst_ctrl_ec_rst_l_d2p;
  logic       cio_sysrst_ctrl_ec_rst_l_en_d2p;
  logic       cio_sysrst_ctrl_ec_rst_l_p2d;
  logic       cio_sysrst_ctrl_flash_wp_l_d2p;
  logic       cio_sysrst_ctrl_flash_wp_l_en_d2p;
  logic       cio_sysrst_ctrl_flash_wp_l_p2d;
  logic       cio_sysrst_ctrl_ac_present_p2d;
  logic       cio_sysrst_ctrl_key0_in_p2d;
  logic       cio_sysrst_ctrl_key1_in_p2d;
  logic       cio_sysrst_ctrl_key2_in_p2d;
  logic       cio_sysrst_ctrl_pwrb_in_p2d;
  logic       cio_sysrst_ctrl_lid_open_p2d;
  logic       cio_sysrst_ctrl_bat_disable_d2p;
  logic       cio_sysrst_ctrl_bat_disable_en_d2p;
  logic       cio_sysrst_ctrl_key0_out_d2p;
  logic       cio_sysrst_ctrl_key0_out_en_d2p;
  logic       cio_sysrst_ctrl_key1_out_d2p;
  logic       cio_sysrst_ctrl_key1_out_en_d2p;
  logic       cio_sysrst_ctrl_key2_out_d2p;
  logic       cio_sysrst_ctrl_key2_out_en_d2p;
  logic       cio_sysrst_ctrl_pwrb_out_d2p;
  logic       cio_sysrst_ctrl_pwrb_out_en_d2p;
  logic       cio_sysrst_ctrl_z3_wakeup_d2p;
  logic       cio_sysrst_ctrl_z3_wakeup_en_d2p;
  logic [8:0] cio_sensor_ctrl_ast_debug_out_d2p;
  logic [8:0] cio_sensor_ctrl_ast_debug_out_en_d2p;


  ///////////////////////////
  // Top-level Main Domain //
  ///////////////////////////
  earlgrey_pd_main #(
  // Auto-inferred parameters
  .GpioGpioAsyncOn(GpioGpioAsyncOn),
  .GpioGpioAsHwStrapsEn(GpioGpioAsHwStrapsEn),
  .SpiDeviceSramType(SpiDeviceSramType),
  .I2c0InputDelayCycles(I2c0InputDelayCycles),
  .I2c1InputDelayCycles(I2c1InputDelayCycles),
  .I2c2InputDelayCycles(I2c2InputDelayCycles),
  .OtpMacroMemInitFile(OtpMacroMemInitFile),
  .SecLcCtrlVolatileRawUnlockEn(SecLcCtrlVolatileRawUnlockEn),
  .LcCtrlUseDmiInterface(LcCtrlUseDmiInterface),
  .LcCtrlSiliconCreatorId(LcCtrlSiliconCreatorId),
  .LcCtrlProductId(LcCtrlProductId),
  .LcCtrlRevisionId(LcCtrlRevisionId),
  .LcCtrlIdcodeValue(LcCtrlIdcodeValue),
  .AlertHandlerEscNumSeverities(AlertHandlerEscNumSeverities),
  .AlertHandlerEscPingCountWidth(AlertHandlerEscPingCountWidth),
  .UsbdevStub(UsbdevStub),
  .UsbdevRcvrWakeTimeUs(UsbdevRcvrWakeTimeUs),
  .SecPinmuxVolatileRawUnlockEn(SecPinmuxVolatileRawUnlockEn),
  .PinmuxTargetCfg(PinmuxTargetCfg),
  .SecFlashCtrlScrambleEn(SecFlashCtrlScrambleEn),
  .FlashCtrlProgFifoDepth(FlashCtrlProgFifoDepth),
  .FlashCtrlRdFifoDepth(FlashCtrlRdFifoDepth),
  .SecRramCtrlScrambleEn(SecRramCtrlScrambleEn),
  .RramCtrlWrFifoDepth(RramCtrlWrFifoDepth),
  .RramCtrlRdFifoDepth(RramCtrlRdFifoDepth),
  .RvDmIdcodeValue(RvDmIdcodeValue),
  .RvDmUseDmiInterface(RvDmUseDmiInterface),
  .SecRvDmVolatileRawUnlockEn(SecRvDmVolatileRawUnlockEn),
  .RvDmTlulHostUserRsvdBits(RvDmTlulHostUserRsvdBits),
  .AesAESGCMEnable(AesAESGCMEnable),
  .SecAesMasking(SecAesMasking),
  .SecAesSBoxImpl(SecAesSBoxImpl),
  .SecAesStartTriggerDelay(SecAesStartTriggerDelay),
  .SecAesAllowForcingMasks(SecAesAllowForcingMasks),
  .SecAesSkipPRNGReseeding(SecAesSkipPRNGReseeding),
  .KmacEnMasking(KmacEnMasking),
  .KmacSwKeyMasked(KmacSwKeyMasked),
  .SecKmacCmdDelay(SecKmacCmdDelay),
  .SecKmacIdleAcceptSwMsg(SecKmacIdleAcceptSwMsg),
  .KmacNumAppIntf(KmacNumAppIntf),
  .KmacAppCfg(KmacAppCfg),
  .OtbnStub(OtbnStub),
  .OtbnRegFile(OtbnRegFile),
  .SecOtbnMuteUrnd(SecOtbnMuteUrnd),
  .SecOtbnFixMaiOpSeq(SecOtbnFixMaiOpSeq),
  .SecOtbnSkipUrndReseedAtStart(SecOtbnSkipUrndReseedAtStart),
  .OtbnFeatStubMai(OtbnFeatStubMai),
  .KeymgrUseOtpSeedsInsteadOfFlash(KeymgrUseOtpSeedsInsteadOfFlash),
  .KeymgrKmacEnMasking(KeymgrKmacEnMasking),
  .CsrngSBoxImpl(CsrngSBoxImpl),
  .EntropySrcRngBusWidth(EntropySrcRngBusWidth),
  .EntropySrcRngBusBitSelWidth(EntropySrcRngBusBitSelWidth),
  .EntropySrcHealthTestWindowWidth(EntropySrcHealthTestWindowWidth),
  .EntropySrcStub(EntropySrcStub),
  .SramCtrlMainInstSize(SramCtrlMainInstSize),
  .SramCtrlMainNumRamInst(SramCtrlMainNumRamInst),
  .SramCtrlMainInstrExec(SramCtrlMainInstrExec),
  .SramCtrlMainNumPrinceRoundsHalf(SramCtrlMainNumPrinceRoundsHalf),
  .SramCtrlMainEccCorrection(SramCtrlMainEccCorrection),
  .RomCtrlBootRomInitFile(RomCtrlBootRomInitFile),
  .SecRomCtrlDisableScrambling(SecRomCtrlDisableScrambling),
  .RvCoreIbexPMPEnable(RvCoreIbexPMPEnable),
  .RvCoreIbexPMPGranularity(RvCoreIbexPMPGranularity),
  .RvCoreIbexPMPNumRegions(RvCoreIbexPMPNumRegions),
  .RvCoreIbexMHPMCounterNum(RvCoreIbexMHPMCounterNum),
  .RvCoreIbexMHPMCounterWidth(RvCoreIbexMHPMCounterWidth),
  .RvCoreIbexPMPRstCfg(RvCoreIbexPMPRstCfg),
  .RvCoreIbexPMPRstAddr(RvCoreIbexPMPRstAddr),
  .RvCoreIbexPMPRstMsecCfg(RvCoreIbexPMPRstMsecCfg),
  .RvCoreIbexRV32E(RvCoreIbexRV32E),
  .RvCoreIbexRV32M(RvCoreIbexRV32M),
  .RvCoreIbexRV32B(RvCoreIbexRV32B),
  .RvCoreIbexRV32ZC(RvCoreIbexRV32ZC),
  .RvCoreIbexRegFile(RvCoreIbexRegFile),
  .RvCoreIbexBranchTargetALU(RvCoreIbexBranchTargetALU),
  .RvCoreIbexWritebackStage(RvCoreIbexWritebackStage),
  .RvCoreIbexICache(RvCoreIbexICache),
  .RvCoreIbexICacheECC(RvCoreIbexICacheECC),
  .RvCoreIbexICacheScramble(RvCoreIbexICacheScramble),
  .RvCoreIbexICacheNWays(RvCoreIbexICacheNWays),
  .RvCoreIbexBranchPredictor(RvCoreIbexBranchPredictor),
  .RvCoreIbexDbgTriggerEn(RvCoreIbexDbgTriggerEn),
  .RvCoreIbexDbgHwBreakNum(RvCoreIbexDbgHwBreakNum),
  .RvCoreIbexSecureIbex(RvCoreIbexSecureIbex),
  .RvCoreIbexDmBaseAddr(RvCoreIbexDmBaseAddr),
  .RvCoreIbexDmAddrMask(RvCoreIbexDmAddrMask),
  .RvCoreIbexDmHaltAddr(RvCoreIbexDmHaltAddr),
  .RvCoreIbexDmExceptionAddr(RvCoreIbexDmExceptionAddr),
  .RvCoreIbexPipeLine(RvCoreIbexPipeLine),
  .RvCoreIbexTlulHostUserRsvdBits(RvCoreIbexTlulHostUserRsvdBits),
  .RvCoreIbexCsrMvendorId(RvCoreIbexCsrMvendorId),
  .RvCoreIbexCsrMimpId(RvCoreIbexCsrMimpId)
  ) earlgrey_pd_main (
    // Clocks and clock gating control from clkmgr
    .clkmgr_clocks_i(clkmgr_clocks_o),
    .clkmgr_cg_en_i (clkmgr_cg_en_o),

    // Resets and reset assert info from rstmgr
    .rstmgr_resets_i(rstmgr_resets_o),
    .rstmgr_rst_en_i(rstmgr_rst_en_o),

    // Manual DFT signals
    .scan_rst_ni,
    .scan_en_i,
    .scanmode_i,

    // Multiplexed I/O
    .mio_in_i,
    .mio_out_o,
    .mio_oe_o,

    // Dedicated I/O
    .dio_in_i,
    .dio_out_o,
    .dio_oe_o,

    // Pad attributes
    .mio_attr_o,
    .dio_attr_o,

    // Special inter-power domain signals (interrupts, alerts)
    .intr_vector_pd_aon_i(intr_vector_pd_aon),

    .alert_tx_pd_aon_i(alert_tx_pd_aon),
    .alert_rx_pd_aon_o(alert_rx_pd_aon),

    // Ports to and from other power domains (auto-generated)
    .alert_handler_crashdump_o             (alert_handler_crashdump  ),
    .alert_handler_esc_rx_i                (alert_handler_esc_rx     ),
    .alert_handler_esc_tx_o                (alert_handler_esc_tx     ),
    .aon_timer_nmi_wdog_timer_bark_i       (aon_timer_nmi_wdog_timer_bark),
    .otp_ctrl_sram_otp_key_req_i           (otp_ctrl_sram_otp_key_req),
    .otp_ctrl_sram_otp_key_rsp_o           (otp_ctrl_sram_otp_key_rsp),
    .pwrmgr_pwr_nvm_o                      (pwrmgr_pwr_nvm           ),
    .pwrmgr_pwr_otp_req_i                  (pwrmgr_pwr_otp_req       ),
    .pwrmgr_pwr_otp_rsp_o                  (pwrmgr_pwr_otp_rsp       ),
    .pwrmgr_pwr_lc_req_i                   (pwrmgr_pwr_lc_req        ),
    .pwrmgr_pwr_lc_rsp_o                   (pwrmgr_pwr_lc_rsp        ),
    .pwrmgr_strap_i                        (pwrmgr_strap             ),
    .pwrmgr_low_power_i                    (pwrmgr_low_power         ),
    .pwrmgr_fetch_en_i                     (pwrmgr_fetch_en          ),
    .rom_ctrl_pwrmgr_data_o                (rom_ctrl_pwrmgr_data     ),
    .clkmgr_idle_o                         (clkmgr_idle              ),
    .lc_ctrl_lc_dft_en_o                   (lc_ctrl_lc_dft_en        ),
    .lc_ctrl_lc_hw_debug_en_o              (lc_ctrl_lc_hw_debug_en   ),
    .lc_ctrl_lc_escalate_en_o              (lc_ctrl_lc_escalate_en   ),
    .lc_ctrl_lc_clk_byp_req_o              (lc_ctrl_lc_clk_byp_req   ),
    .lc_ctrl_lc_clk_byp_ack_i              (lc_ctrl_lc_clk_byp_ack   ),
    .rv_core_ibex_crash_dump_o             (rv_core_ibex_crash_dump  ),
    .rv_core_ibex_pwrmgr_o                 (rv_core_ibex_pwrmgr      ),
    .rv_dm_ndmreset_req_o                  (rv_dm_ndmreset_req       ),
    .pwrmgr_wakeups_o                      (pwrmgr_wakeups           ),
    .pwrmgr_tl_req_o                       (pwrmgr_tl_req            ),
    .pwrmgr_tl_rsp_i                       (pwrmgr_tl_rsp            ),
    .rstmgr_tl_req_o                       (rstmgr_tl_req            ),
    .rstmgr_tl_rsp_i                       (rstmgr_tl_rsp            ),
    .clkmgr_tl_req_o                       (clkmgr_tl_req            ),
    .clkmgr_tl_rsp_i                       (clkmgr_tl_rsp            ),
    .sensor_ctrl_tl_req_o                  (sensor_ctrl_tl_req       ),
    .sensor_ctrl_tl_rsp_i                  (sensor_ctrl_tl_rsp       ),
    .sram_ctrl_ret_regs_tl_req_o           (sram_ctrl_ret_regs_tl_req),
    .sram_ctrl_ret_regs_tl_rsp_i           (sram_ctrl_ret_regs_tl_rsp),
    .sram_ctrl_ret_ram_tl_req_o            (sram_ctrl_ret_ram_tl_req ),
    .sram_ctrl_ret_ram_tl_rsp_i            (sram_ctrl_ret_ram_tl_rsp ),
    .aon_timer_tl_req_o                    (aon_timer_tl_req         ),
    .aon_timer_tl_rsp_i                    (aon_timer_tl_rsp         ),
    .sysrst_ctrl_tl_req_o                  (sysrst_ctrl_tl_req       ),
    .sysrst_ctrl_tl_rsp_i                  (sysrst_ctrl_tl_rsp       ),
    .adc_ctrl_tl_req_o                     (adc_ctrl_tl_req          ),
    .adc_ctrl_tl_rsp_i                     (adc_ctrl_tl_rsp          ),
    .cio_sysrst_ctrl_ec_rst_l_d2p_i        (cio_sysrst_ctrl_ec_rst_l_d2p),
    .cio_sysrst_ctrl_ec_rst_l_en_d2p_i     (cio_sysrst_ctrl_ec_rst_l_en_d2p),
    .cio_sysrst_ctrl_ec_rst_l_p2d_o        (cio_sysrst_ctrl_ec_rst_l_p2d),
    .cio_sysrst_ctrl_flash_wp_l_d2p_i      (cio_sysrst_ctrl_flash_wp_l_d2p),
    .cio_sysrst_ctrl_flash_wp_l_en_d2p_i   (cio_sysrst_ctrl_flash_wp_l_en_d2p),
    .cio_sysrst_ctrl_flash_wp_l_p2d_o      (cio_sysrst_ctrl_flash_wp_l_p2d),
    .cio_sysrst_ctrl_ac_present_p2d_o      (cio_sysrst_ctrl_ac_present_p2d),
    .cio_sysrst_ctrl_key0_in_p2d_o         (cio_sysrst_ctrl_key0_in_p2d),
    .cio_sysrst_ctrl_key1_in_p2d_o         (cio_sysrst_ctrl_key1_in_p2d),
    .cio_sysrst_ctrl_key2_in_p2d_o         (cio_sysrst_ctrl_key2_in_p2d),
    .cio_sysrst_ctrl_pwrb_in_p2d_o         (cio_sysrst_ctrl_pwrb_in_p2d),
    .cio_sysrst_ctrl_lid_open_p2d_o        (cio_sysrst_ctrl_lid_open_p2d),
    .cio_sysrst_ctrl_bat_disable_d2p_i     (cio_sysrst_ctrl_bat_disable_d2p),
    .cio_sysrst_ctrl_bat_disable_en_d2p_i  (cio_sysrst_ctrl_bat_disable_en_d2p),
    .cio_sysrst_ctrl_key0_out_d2p_i        (cio_sysrst_ctrl_key0_out_d2p),
    .cio_sysrst_ctrl_key0_out_en_d2p_i     (cio_sysrst_ctrl_key0_out_en_d2p),
    .cio_sysrst_ctrl_key1_out_d2p_i        (cio_sysrst_ctrl_key1_out_d2p),
    .cio_sysrst_ctrl_key1_out_en_d2p_i     (cio_sysrst_ctrl_key1_out_en_d2p),
    .cio_sysrst_ctrl_key2_out_d2p_i        (cio_sysrst_ctrl_key2_out_d2p),
    .cio_sysrst_ctrl_key2_out_en_d2p_i     (cio_sysrst_ctrl_key2_out_en_d2p),
    .cio_sysrst_ctrl_pwrb_out_d2p_i        (cio_sysrst_ctrl_pwrb_out_d2p),
    .cio_sysrst_ctrl_pwrb_out_en_d2p_i     (cio_sysrst_ctrl_pwrb_out_en_d2p),
    .cio_sysrst_ctrl_z3_wakeup_d2p_i       (cio_sysrst_ctrl_z3_wakeup_d2p),
    .cio_sysrst_ctrl_z3_wakeup_en_d2p_i    (cio_sysrst_ctrl_z3_wakeup_en_d2p),
    .cio_sensor_ctrl_ast_debug_out_d2p_i   (cio_sensor_ctrl_ast_debug_out_d2p),
    .cio_sensor_ctrl_ast_debug_out_en_d2p_i(cio_sensor_ctrl_ast_debug_out_en_d2p),

    // Regular ports (auto-generated)
    .ast_edn_req_i,
    .ast_edn_rsp_o,
    .ast_lc_dft_en_o,
    .obs_ctrl_i,
    .otbn_imem_ram_cfg_req_i,
    .otbn_imem_ram_cfg_rsp_o,
    .otbn_dmem_ram_cfg_req_i,
    .otbn_dmem_ram_cfg_rsp_o,
    .i2c0_ram_cfg_req_i,
    .i2c0_ram_cfg_rsp_o,
    .i2c1_ram_cfg_req_i,
    .i2c1_ram_cfg_rsp_o,
    .i2c2_ram_cfg_req_i,
    .i2c2_ram_cfg_rsp_o,
    .usbdev_ram_cfg_req_i,
    .usbdev_ram_cfg_rsp_o,
    .rv_core_ibex_icache_tag_ram_cfg_req_i,
    .rv_core_ibex_icache_tag_ram_cfg_rsp_o,
    .rv_core_ibex_icache_data_ram_cfg_req_i,
    .rv_core_ibex_icache_data_ram_cfg_rsp_o,
    .spi_device_sys2spi_ram_cfg_req_i,
    .spi_device_sys2spi_ram_cfg_rsp_o,
    .spi_device_spi2sys_ram_cfg_req_i,
    .spi_device_spi2sys_ram_cfg_rsp_o,
    .rom_ctrl_rom_cfg_req_i,
    .rom_ctrl_rom_cfg_rsp_o,
    .sram_ctrl_main_ram_cfg_req_i,
    .sram_ctrl_main_ram_cfg_rsp_o,
    .flash_bist_enable_i,
    .flash_power_down_h_i,
    .flash_power_ready_h_i,
    .flash_test_mode_a_io,
    .flash_test_voltage_h_io,
    .flash_obs_o,
    .es_rng_enable_o,
    .es_rng_valid_i,
    .es_rng_bit_i,
    .es_rng_fips_o,
    .ast_tl_req_o,
    .ast_tl_rsp_i,
    .dft_strap_test_o,
    .dft_hold_tap_sel_i,
    .usb_dp_pullup_en_o,
    .usb_dn_pullup_en_o,
    .otp_macro_pwr_seq_o,
    .otp_macro_pwr_seq_h_i,
    .otp_ext_voltage_h_io,
    .otp_obs_o,
    .fpga_info_i,
    .sck_monitor_o,
    .usbdev_usb_rx_d_i,
    .usbdev_usb_tx_d_o,
    .usbdev_usb_tx_se0_o,
    .usbdev_usb_tx_use_d_se0_o,
    .usbdev_usb_rx_enable_o,
    .usbdev_usb_ref_val_o,
    .usbdev_usb_ref_pulse_o
  );

  //////////////////////////
  // Top-level Aon Domain //
  //////////////////////////
  earlgrey_pd_aon #(
  // Auto-inferred parameters
  .SecRstmgrCheck(SecRstmgrCheck),
  .SecRstmgrMaxSyncDelay(SecRstmgrMaxSyncDelay),
  .SramCtrlRetInstSize(SramCtrlRetInstSize),
  .SramCtrlRetNumRamInst(SramCtrlRetNumRamInst),
  .SramCtrlRetInstrExec(SramCtrlRetInstrExec),
  .SramCtrlRetNumPrinceRoundsHalf(SramCtrlRetNumPrinceRoundsHalf),
  .SramCtrlRetEccCorrection(SramCtrlRetEccCorrection)
  ) earlgrey_pd_aon (
    // All externally supplied clocks
    .clk_main_i(ast_base_clks_i.clk_sys),
    .clk_io_i  (ast_base_clks_i.clk_io ),
    .clk_usb_i (ast_base_clks_i.clk_usb),
    .clk_aon_i (ast_base_clks_i.clk_aon),

    // Manual DFT signals
    .scan_rst_ni,
    .scanmode_i,

    // Special inter-power domain signals (interrupts, alerts)
    .intr_vector_o(intr_vector_pd_aon),

    .alert_tx_o(alert_tx_pd_aon),
    .alert_rx_i(alert_rx_pd_aon),

    // Ports to and from other power domains (auto-generated)
    .alert_handler_crashdump_i             (alert_handler_crashdump  ),
    .alert_handler_esc_rx_o                (alert_handler_esc_rx     ),
    .alert_handler_esc_tx_i                (alert_handler_esc_tx     ),
    .aon_timer_nmi_wdog_timer_bark_o       (aon_timer_nmi_wdog_timer_bark),
    .otp_ctrl_sram_otp_key_req_o           (otp_ctrl_sram_otp_key_req),
    .otp_ctrl_sram_otp_key_rsp_i           (otp_ctrl_sram_otp_key_rsp),
    .pwrmgr_pwr_nvm_i                      (pwrmgr_pwr_nvm           ),
    .pwrmgr_pwr_otp_req_o                  (pwrmgr_pwr_otp_req       ),
    .pwrmgr_pwr_otp_rsp_i                  (pwrmgr_pwr_otp_rsp       ),
    .pwrmgr_pwr_lc_req_o                   (pwrmgr_pwr_lc_req        ),
    .pwrmgr_pwr_lc_rsp_i                   (pwrmgr_pwr_lc_rsp        ),
    .pwrmgr_strap_o                        (pwrmgr_strap             ),
    .pwrmgr_low_power_o                    (pwrmgr_low_power         ),
    .pwrmgr_fetch_en_o                     (pwrmgr_fetch_en          ),
    .rom_ctrl_pwrmgr_data_i                (rom_ctrl_pwrmgr_data     ),
    .clkmgr_idle_i                         (clkmgr_idle              ),
    .lc_ctrl_lc_dft_en_i                   (lc_ctrl_lc_dft_en        ),
    .lc_ctrl_lc_hw_debug_en_i              (lc_ctrl_lc_hw_debug_en   ),
    .lc_ctrl_lc_escalate_en_i              (lc_ctrl_lc_escalate_en   ),
    .lc_ctrl_lc_clk_byp_req_i              (lc_ctrl_lc_clk_byp_req   ),
    .lc_ctrl_lc_clk_byp_ack_o              (lc_ctrl_lc_clk_byp_ack   ),
    .rv_core_ibex_crash_dump_i             (rv_core_ibex_crash_dump  ),
    .rv_core_ibex_pwrmgr_i                 (rv_core_ibex_pwrmgr      ),
    .rv_dm_ndmreset_req_i                  (rv_dm_ndmreset_req       ),
    .pwrmgr_wakeups_i                      (pwrmgr_wakeups           ),
    .pwrmgr_tl_req_i                       (pwrmgr_tl_req            ),
    .pwrmgr_tl_rsp_o                       (pwrmgr_tl_rsp            ),
    .rstmgr_tl_req_i                       (rstmgr_tl_req            ),
    .rstmgr_tl_rsp_o                       (rstmgr_tl_rsp            ),
    .clkmgr_tl_req_i                       (clkmgr_tl_req            ),
    .clkmgr_tl_rsp_o                       (clkmgr_tl_rsp            ),
    .sensor_ctrl_tl_req_i                  (sensor_ctrl_tl_req       ),
    .sensor_ctrl_tl_rsp_o                  (sensor_ctrl_tl_rsp       ),
    .sram_ctrl_ret_regs_tl_req_i           (sram_ctrl_ret_regs_tl_req),
    .sram_ctrl_ret_regs_tl_rsp_o           (sram_ctrl_ret_regs_tl_rsp),
    .sram_ctrl_ret_ram_tl_req_i            (sram_ctrl_ret_ram_tl_req ),
    .sram_ctrl_ret_ram_tl_rsp_o            (sram_ctrl_ret_ram_tl_rsp ),
    .aon_timer_tl_req_i                    (aon_timer_tl_req         ),
    .aon_timer_tl_rsp_o                    (aon_timer_tl_rsp         ),
    .sysrst_ctrl_tl_req_i                  (sysrst_ctrl_tl_req       ),
    .sysrst_ctrl_tl_rsp_o                  (sysrst_ctrl_tl_rsp       ),
    .adc_ctrl_tl_req_i                     (adc_ctrl_tl_req          ),
    .adc_ctrl_tl_rsp_o                     (adc_ctrl_tl_rsp          ),
    .cio_sysrst_ctrl_ec_rst_l_d2p_o        (cio_sysrst_ctrl_ec_rst_l_d2p),
    .cio_sysrst_ctrl_ec_rst_l_en_d2p_o     (cio_sysrst_ctrl_ec_rst_l_en_d2p),
    .cio_sysrst_ctrl_ec_rst_l_p2d_i        (cio_sysrst_ctrl_ec_rst_l_p2d),
    .cio_sysrst_ctrl_flash_wp_l_d2p_o      (cio_sysrst_ctrl_flash_wp_l_d2p),
    .cio_sysrst_ctrl_flash_wp_l_en_d2p_o   (cio_sysrst_ctrl_flash_wp_l_en_d2p),
    .cio_sysrst_ctrl_flash_wp_l_p2d_i      (cio_sysrst_ctrl_flash_wp_l_p2d),
    .cio_sysrst_ctrl_ac_present_p2d_i      (cio_sysrst_ctrl_ac_present_p2d),
    .cio_sysrst_ctrl_key0_in_p2d_i         (cio_sysrst_ctrl_key0_in_p2d),
    .cio_sysrst_ctrl_key1_in_p2d_i         (cio_sysrst_ctrl_key1_in_p2d),
    .cio_sysrst_ctrl_key2_in_p2d_i         (cio_sysrst_ctrl_key2_in_p2d),
    .cio_sysrst_ctrl_pwrb_in_p2d_i         (cio_sysrst_ctrl_pwrb_in_p2d),
    .cio_sysrst_ctrl_lid_open_p2d_i        (cio_sysrst_ctrl_lid_open_p2d),
    .cio_sysrst_ctrl_bat_disable_d2p_o     (cio_sysrst_ctrl_bat_disable_d2p),
    .cio_sysrst_ctrl_bat_disable_en_d2p_o  (cio_sysrst_ctrl_bat_disable_en_d2p),
    .cio_sysrst_ctrl_key0_out_d2p_o        (cio_sysrst_ctrl_key0_out_d2p),
    .cio_sysrst_ctrl_key0_out_en_d2p_o     (cio_sysrst_ctrl_key0_out_en_d2p),
    .cio_sysrst_ctrl_key1_out_d2p_o        (cio_sysrst_ctrl_key1_out_d2p),
    .cio_sysrst_ctrl_key1_out_en_d2p_o     (cio_sysrst_ctrl_key1_out_en_d2p),
    .cio_sysrst_ctrl_key2_out_d2p_o        (cio_sysrst_ctrl_key2_out_d2p),
    .cio_sysrst_ctrl_key2_out_en_d2p_o     (cio_sysrst_ctrl_key2_out_en_d2p),
    .cio_sysrst_ctrl_pwrb_out_d2p_o        (cio_sysrst_ctrl_pwrb_out_d2p),
    .cio_sysrst_ctrl_pwrb_out_en_d2p_o     (cio_sysrst_ctrl_pwrb_out_en_d2p),
    .cio_sysrst_ctrl_z3_wakeup_d2p_o       (cio_sysrst_ctrl_z3_wakeup_d2p),
    .cio_sysrst_ctrl_z3_wakeup_en_d2p_o    (cio_sysrst_ctrl_z3_wakeup_en_d2p),
    .cio_sensor_ctrl_ast_debug_out_d2p_o   (cio_sensor_ctrl_ast_debug_out_d2p),
    .cio_sensor_ctrl_ast_debug_out_en_d2p_o(cio_sensor_ctrl_ast_debug_out_en_d2p),

    // Regular ports (auto-generated)
    .adc_req_o,
    .adc_rsp_i,
    .sram_ctrl_ret_ram_cfg_req_i,
    .sram_ctrl_ret_ram_cfg_rsp_o,
    .clkmgr_clocks_o,
    .clkmgr_cg_en_o,
    .clk_main_jitter_en_o,
    .io_clk_byp_req_o,
    .io_clk_byp_ack_i,
    .all_clk_byp_req_o,
    .all_clk_byp_ack_i,
    .hi_speed_sel_o,
    .div_step_down_req_i,
    .calib_rdy_i,
    .pwrmgr_ast_req_o,
    .pwrmgr_ast_rsp_i,
    .por_n_i,
    .rstmgr_resets_o,
    .rstmgr_rst_en_o,
    .sensor_ctrl_ast_alert_req_i,
    .sensor_ctrl_ast_alert_rsp_o,
    .sensor_ctrl_ast_status_i,
    .ast2pinmux_i,
    .ast_init_done_i,
    .sensor_ctrl_manual_pad_attr_o
  );

endmodule
