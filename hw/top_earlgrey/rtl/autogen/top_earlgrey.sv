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
  // parameters for ast
  parameter int unsigned AstUsbCalibWidth = 20,
  parameter int unsigned AstPad2AstInWidth = 8,
  // parameters for sram_ctrl_ret
  parameter int SramCtrlRetInstSize = 4096,
  parameter int SramCtrlRetNumRamInst = 1,
  parameter bit SramCtrlRetInstrExec = 0,
  parameter int SramCtrlRetNumPrinceRoundsHalf = 3,
  parameter int SramCtrlRetNumAddrScrRounds = 2,
  parameter bit SramCtrlRetEccCorrection = 0,
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
  parameter bit SecOtbnFixMaiOpSeq = 0,
  parameter bit SecOtbnFixMacOpSeq = 0,
  parameter bit SecOtbnSkipUrndReseedAtStart = 0,
  parameter bit OtbnFeatStubMai = 0,
  // parameters for keymgr_dpe
  parameter bit KeymgrDpeKmacEnMasking = 1,
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
  parameter int SramCtrlMainNumAddrScrRounds = 2,
  parameter bit SramCtrlMainEccCorrection = 0,
  // parameters for sram_ctrl_sec
  parameter int SramCtrlSecInstSize = 65536,
  parameter int SramCtrlSecNumRamInst = 1,
  parameter bit SramCtrlSecInstrExec = 1,
  parameter int SramCtrlSecNumPrinceRoundsHalf = 2,
  parameter int SramCtrlSecNumAddrScrRounds = 2,
  parameter bit SramCtrlSecEccCorrection = 0,
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
  parameter int unsigned RvCoreIbexCheriotRevBitmapAddrWidth = 12,
  parameter int unsigned RvCoreIbexCheriotRevBitmapBaseAddr = 32'h1100_0000,
  parameter int unsigned RvCoreIbexCheriotTrvkHeapBaseAddr = 32'h1000_0000,
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
  parameter logic [31:0] RvCoreIbexCsrMimpId = '0,
  // parameters for cheriot
  parameter logic [top_pkg::TL_AW-1:0] CheriotMainSramBaseAddr = 32'h1000_0000,
  parameter logic [top_pkg::TL_AW-1:0] CheriotMainSramTopAddr = 32'h1003_0000,
  parameter logic [top_pkg::TL_AW-1:0] CheriotNvmBaseAddr = 32'h3000_0000,
  parameter logic [top_pkg::TL_AW-1:0] CheriotNvmTopAddr = 32'h3020_0000,
  parameter logic [top_pkg::TL_AW-1:0] CheriotMetaSramBaseAddr = 32'h1100_0000,
  // parameters for sram_ctrl_meta
  parameter int SramCtrlMetaInstSize = 38912,
  parameter int SramCtrlMetaNumRamInst = 1,
  parameter bit SramCtrlMetaInstrExec = 0,
  parameter int SramCtrlMetaNumPrinceRoundsHalf = 2,
  parameter int SramCtrlMetaNumAddrScrRounds = 0,
  parameter bit SramCtrlMetaEccCorrection = 0
) (

  // Unmanaged external clocks
  input                        clk_ast_ext_i,
  input prim_mubi_pkg::mubi4_t cg_en_ast_ext_i,

  // Manual DFT signals
  output logic padring_scan_clk_o,

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
  input  logic       manual_in_por_n_i,
  output prim_mubi_pkg::mubi4_t       scanmode_o,
  output logic       scan_en_o,
  output logic       scan_rst_n_o,
  output logic [AstUsbCalibWidth-1:0] usb_io_pu_cal_o,
  input  logic [AstPad2AstInWidth-1:0] padmux2ast_i,
  output logic [3:0] mux_iob_sel_o,
  input  ast_pkg::ast_vx_supp_t       ast_vx_supp_i,
  input  ast_pkg::ast_obs_bus_t       ast_obs_i,
  input  ast_pkg::awire_t       ast_adc_a0_a_i,
  input  ast_pkg::awire_t       ast_adc_a1_a_i,
  output ast_pkg::awire_t       ast2pad_t0_a_o,
  output ast_pkg::awire_t       ast2pad_t1_a_o,
  input  ast_pkg::clks_osc_byp_t       clk_osc_byp_pd_main_i,
  input  ast_pkg::clks_osc_byp_t       clk_osc_byp_pd_aon_i,
  output ast_pkg::ast_pwst_t       ast_pwst_h_o,
  input  logic       dft_hold_tap_sel_i,
  output logic       usb_dp_pullup_en_o,
  output logic       usb_dn_pullup_en_o,
  inout         rram_test_analog_io,
  input  logic [31:0] fpga_info_i,
  output prim_pad_wrapper_pkg::pad_attr_t [3:0] sensor_ctrl_manual_pad_attr_o,
  input  logic       usbdev_usb_rx_d_i,
  output logic       usbdev_usb_tx_d_o,
  output logic       usbdev_usb_tx_se0_o,
  output logic       usbdev_usb_tx_use_d_se0_o,
  output logic       usbdev_usb_rx_enable_o

);

  import top_earlgrey_pkg::*;
  import prim_pad_wrapper_pkg::*;

  // Inter-Power Domain signals
  logic [6:0] intr_vector_pd_aon;
  prim_alert_pkg::alert_tx_t [10:0] alert_tx_pd_aon;
  prim_alert_pkg::alert_rx_t [10:0] alert_rx_pd_aon;
  ast_pkg::ast_obs_ctrl_t       ast_obs_ctrl;
  prim_mubi_pkg::mubi4_t       ast_clk_src_sys_jen;
  prim_mubi_pkg::mubi4_t       ast_init_done;
  logic       spi_device_sck_monitor;
  logic       usbdev_usb_ref_pulse;
  logic       usbdev_usb_ref_val;
  pinmux_pkg::dft_strap_test_req_t       pinmux_dft_strap_test;
  prim_mubi_pkg::mubi4_t       clkmgr_all_clk_byp_req;
  prim_mubi_pkg::mubi4_t       clkmgr_all_clk_byp_ack;
  prim_mubi_pkg::mubi4_t       clkmgr_io_clk_byp_req;
  prim_mubi_pkg::mubi4_t       clkmgr_io_clk_byp_ack;
  prim_mubi_pkg::mubi4_t       clkmgr_hi_speed_sel;
  prim_mubi_pkg::mubi4_t       clkmgr_div_step_down_req;
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
  ast_intraip_pkg::s2p_t       ast_intraip_s2p;
  ast_intraip_pkg::p2s_t       ast_intraip_p2s;
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
  logic       ast_clk_src_sys;
  logic       ast_clk_src_io;
  logic       ast_clk_src_usb;

  // Clockmgr and rstmgr info from AON to MAIN
  // TODO: Manual wiring due to topgen limtation that signals defined as 'top' in the hjson are
  //       local to the PD the IP is in.
  clkmgr_pkg::clkmgr_out_t    clkmgr_clocks;
  clkmgr_pkg::clkmgr_cg_en_t  clkmgr_cg_en;
  rstmgr_pkg::rstmgr_out_t    rstmgr_resets;
  rstmgr_pkg::rstmgr_rst_en_t rstmgr_rst_en;

  // Expose scan clock to padring
  assign padring_scan_clk_o = ast_clk_src_sys;

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
  .SecOtbnFixMaiOpSeq(SecOtbnFixMaiOpSeq),
  .SecOtbnFixMacOpSeq(SecOtbnFixMacOpSeq),
  .SecOtbnSkipUrndReseedAtStart(SecOtbnSkipUrndReseedAtStart),
  .OtbnFeatStubMai(OtbnFeatStubMai),
  .KeymgrDpeKmacEnMasking(KeymgrDpeKmacEnMasking),
  .CsrngSBoxImpl(CsrngSBoxImpl),
  .EntropySrcRngBusWidth(EntropySrcRngBusWidth),
  .EntropySrcRngBusBitSelWidth(EntropySrcRngBusBitSelWidth),
  .EntropySrcHealthTestWindowWidth(EntropySrcHealthTestWindowWidth),
  .EntropySrcStub(EntropySrcStub),
  .SramCtrlMainInstSize(SramCtrlMainInstSize),
  .SramCtrlMainNumRamInst(SramCtrlMainNumRamInst),
  .SramCtrlMainInstrExec(SramCtrlMainInstrExec),
  .SramCtrlMainNumPrinceRoundsHalf(SramCtrlMainNumPrinceRoundsHalf),
  .SramCtrlMainNumAddrScrRounds(SramCtrlMainNumAddrScrRounds),
  .SramCtrlMainEccCorrection(SramCtrlMainEccCorrection),
  .SramCtrlSecInstSize(SramCtrlSecInstSize),
  .SramCtrlSecNumRamInst(SramCtrlSecNumRamInst),
  .SramCtrlSecInstrExec(SramCtrlSecInstrExec),
  .SramCtrlSecNumPrinceRoundsHalf(SramCtrlSecNumPrinceRoundsHalf),
  .SramCtrlSecNumAddrScrRounds(SramCtrlSecNumAddrScrRounds),
  .SramCtrlSecEccCorrection(SramCtrlSecEccCorrection),
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
  .RvCoreIbexCheriotRevBitmapAddrWidth(RvCoreIbexCheriotRevBitmapAddrWidth),
  .RvCoreIbexCheriotRevBitmapBaseAddr(RvCoreIbexCheriotRevBitmapBaseAddr),
  .RvCoreIbexCheriotTrvkHeapBaseAddr(RvCoreIbexCheriotTrvkHeapBaseAddr),
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
  .RvCoreIbexCsrMimpId(RvCoreIbexCsrMimpId),
  .CheriotMainSramBaseAddr(CheriotMainSramBaseAddr),
  .CheriotMainSramTopAddr(CheriotMainSramTopAddr),
  .CheriotNvmBaseAddr(CheriotNvmBaseAddr),
  .CheriotNvmTopAddr(CheriotNvmTopAddr),
  .CheriotMetaSramBaseAddr(CheriotMetaSramBaseAddr),
  .SramCtrlMetaInstSize(SramCtrlMetaInstSize),
  .SramCtrlMetaNumRamInst(SramCtrlMetaNumRamInst),
  .SramCtrlMetaInstrExec(SramCtrlMetaInstrExec),
  .SramCtrlMetaNumPrinceRoundsHalf(SramCtrlMetaNumPrinceRoundsHalf),
  .SramCtrlMetaNumAddrScrRounds(SramCtrlMetaNumAddrScrRounds),
  .SramCtrlMetaEccCorrection(SramCtrlMetaEccCorrection)
  ) earlgrey_pd_main (
    // Clocks and clock gating control from clkmgr
    .clkmgr_clocks_i(clkmgr_clocks),
    .clkmgr_cg_en_i (clkmgr_cg_en),

    // Unmanaged external clocks
    .clk_ast_ext_i,
    .cg_en_ast_ext_i,

    // Resets and reset assert info from rstmgr
    .rstmgr_resets_i(rstmgr_resets),
    .rstmgr_rst_en_i(rstmgr_rst_en),

    // Manual DFT signals
    .scan_rst_ni(scan_rst_n_o),
    .scan_en_i  (scan_en_o),
    .scanmode_i (scanmode_o),

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
    .ast_obs_ctrl_i                        (ast_obs_ctrl             ),
    .ast_clk_src_sys_jen_i                 (ast_clk_src_sys_jen      ),
    .ast_init_done_o                       (ast_init_done            ),
    .spi_device_sck_monitor_o              (spi_device_sck_monitor   ),
    .usbdev_usb_ref_pulse_o                (usbdev_usb_ref_pulse     ),
    .usbdev_usb_ref_val_o                  (usbdev_usb_ref_val       ),
    .pinmux_dft_strap_test_o               (pinmux_dft_strap_test    ),
    .clkmgr_all_clk_byp_req_i              (clkmgr_all_clk_byp_req   ),
    .clkmgr_all_clk_byp_ack_o              (clkmgr_all_clk_byp_ack   ),
    .clkmgr_io_clk_byp_req_i               (clkmgr_io_clk_byp_req    ),
    .clkmgr_io_clk_byp_ack_o               (clkmgr_io_clk_byp_ack    ),
    .clkmgr_hi_speed_sel_i                 (clkmgr_hi_speed_sel      ),
    .clkmgr_div_step_down_req_o            (clkmgr_div_step_down_req ),
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
    .ast_intraip_s2p_i                     (ast_intraip_s2p          ),
    .ast_intraip_p2s_o                     (ast_intraip_p2s          ),
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
    .ast_clk_src_sys_o                     (ast_clk_src_sys          ),
    .ast_clk_src_io_o                      (ast_clk_src_io           ),
    .ast_clk_src_usb_o                     (ast_clk_src_usb          ),

    // Regular ports (auto-generated)
    .clk_osc_byp_pd_main_i,
    .dft_hold_tap_sel_i,
    .usb_dp_pullup_en_o,
    .usb_dn_pullup_en_o,
    .rram_test_analog_io,
    .fpga_info_i,
    .usbdev_usb_rx_d_i,
    .usbdev_usb_tx_d_o,
    .usbdev_usb_tx_se0_o,
    .usbdev_usb_tx_use_d_se0_o,
    .usbdev_usb_rx_enable_o
  );

  //////////////////////////
  // Top-level Aon Domain //
  //////////////////////////
  earlgrey_pd_aon #(
  // Auto-inferred parameters
  .SecRstmgrCheck(SecRstmgrCheck),
  .SecRstmgrMaxSyncDelay(SecRstmgrMaxSyncDelay),
  .AstUsbCalibWidth(AstUsbCalibWidth),
  .AstPad2AstInWidth(AstPad2AstInWidth),
  .SramCtrlRetInstSize(SramCtrlRetInstSize),
  .SramCtrlRetNumRamInst(SramCtrlRetNumRamInst),
  .SramCtrlRetInstrExec(SramCtrlRetInstrExec),
  .SramCtrlRetNumPrinceRoundsHalf(SramCtrlRetNumPrinceRoundsHalf),
  .SramCtrlRetNumAddrScrRounds(SramCtrlRetNumAddrScrRounds),
  .SramCtrlRetEccCorrection(SramCtrlRetEccCorrection)
  ) earlgrey_pd_aon (
    // Clocks and clock gating control from clkmgr
    .clkmgr_clocks_o(clkmgr_clocks),
    .clkmgr_cg_en_o (clkmgr_cg_en),

    // Unmanaged external clocks
    .clk_ast_ext_i,
    .cg_en_ast_ext_i,

    // Resets and reset assert info from rstmgr
    .rstmgr_resets_o(rstmgr_resets),
    .rstmgr_rst_en_o(rstmgr_rst_en),

    // Special inter-power domain signals (interrupts, alerts)
    .intr_vector_o(intr_vector_pd_aon),

    .alert_tx_o(alert_tx_pd_aon),
    .alert_rx_i(alert_rx_pd_aon),

    // Ports to and from other power domains (auto-generated)
    .ast_obs_ctrl_o                        (ast_obs_ctrl             ),
    .ast_clk_src_sys_jen_o                 (ast_clk_src_sys_jen      ),
    .ast_init_done_i                       (ast_init_done            ),
    .spi_device_sck_monitor_i              (spi_device_sck_monitor   ),
    .usbdev_usb_ref_pulse_i                (usbdev_usb_ref_pulse     ),
    .usbdev_usb_ref_val_i                  (usbdev_usb_ref_val       ),
    .pinmux_dft_strap_test_i               (pinmux_dft_strap_test    ),
    .clkmgr_all_clk_byp_req_o              (clkmgr_all_clk_byp_req   ),
    .clkmgr_all_clk_byp_ack_i              (clkmgr_all_clk_byp_ack   ),
    .clkmgr_io_clk_byp_req_o               (clkmgr_io_clk_byp_req    ),
    .clkmgr_io_clk_byp_ack_i               (clkmgr_io_clk_byp_ack    ),
    .clkmgr_hi_speed_sel_o                 (clkmgr_hi_speed_sel      ),
    .clkmgr_div_step_down_req_i            (clkmgr_div_step_down_req ),
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
    .ast_intraip_s2p_o                     (ast_intraip_s2p          ),
    .ast_intraip_p2s_i                     (ast_intraip_p2s          ),
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
    .ast_clk_src_sys_i                     (ast_clk_src_sys          ),
    .ast_clk_src_io_i                      (ast_clk_src_io           ),
    .ast_clk_src_usb_i                     (ast_clk_src_usb          ),

    // Regular ports (auto-generated)
    .manual_in_por_n_i,
    .scanmode_o,
    .scan_en_o,
    .scan_rst_n_o,
    .usb_io_pu_cal_o,
    .padmux2ast_i,
    .mux_iob_sel_o,
    .ast_vx_supp_i,
    .ast_obs_i,
    .ast_adc_a0_a_i,
    .ast_adc_a1_a_i,
    .ast2pad_t0_a_o,
    .ast2pad_t1_a_o,
    .clk_osc_byp_pd_aon_i,
    .ast_pwst_h_o,
    .sensor_ctrl_manual_pad_attr_o
  );

endmodule
