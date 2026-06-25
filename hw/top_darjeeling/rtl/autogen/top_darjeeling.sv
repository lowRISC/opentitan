// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_darjeeling/data/top_darjeeling.hjson
//                -o hw/top_darjeeling/


// This wrapper hosts all power domain wrappers and the connections between them for darjeeling.
module top_darjeeling #(
  // Auto-inferred parameters
  // parameters for gpio
  parameter bit GpioGpioAsyncOn = 1,
  parameter bit GpioGpioAsHwStrapsEn = 1,
  // parameters for spi_device
  parameter spi_device_pkg::sram_type_e SpiDeviceSramType = spi_device_pkg::SramType1r1w,
  // parameters for i2c0
  parameter int I2c0InputDelayCycles = 0,
  // parameters for otp_macro
  parameter OtpMacroMemInitFile = "",
  // parameters for lc_ctrl
  parameter bit SecLcCtrlVolatileRawUnlockEn = top_pkg::SecVolatileRawUnlockEn,
  parameter bit LcCtrlUseDmiInterface = 1,
  parameter logic [15:0] LcCtrlSiliconCreatorId = 16'h 4002,
  parameter logic [15:0] LcCtrlProductId = 16'h 4000,
  parameter logic [7:0] LcCtrlRevisionId = 8'h 01,
  parameter logic [31:0] LcCtrlIdcodeValue = 32'h00000001,
  // parameters for alert_handler
  parameter int AlertHandlerEscNumSeverities = 4,
  parameter int AlertHandlerEscPingCountWidth = 16,
  // parameters for rstmgr_aon
  parameter bit SecRstmgrAonCheck = 1'b1,
  parameter int SecRstmgrAonMaxSyncDelay = 2,
  // parameters for pinmux_aon
  parameter pinmux_pkg::target_cfg_t PinmuxAonTargetCfg = pinmux_pkg::DefaultTargetCfg,
  // parameters for sram_ctrl_ret_aon
  parameter int SramCtrlRetAonInstSize = 4096,
  parameter int SramCtrlRetAonNumRamInst = 1,
  parameter bit SramCtrlRetAonInstrExec = 0,
  parameter int SramCtrlRetAonNumPrinceRoundsHalf = 3,
  parameter bit SramCtrlRetAonEccCorrection = 0,
  // parameters for rv_dm
  parameter logic [31:0] RvDmIdcodeValue = 32'h 0000_0001,
  parameter bit RvDmUseDmiInterface = 1,
  parameter bit SecRvDmVolatileRawUnlockEn = top_pkg::SecVolatileRawUnlockEn,
  parameter logic [tlul_pkg::RsvdWidth-1:0] RvDmTlulHostUserRsvdBits = '0,
  // parameters for aes
  parameter bit AesAESGCMEnable = 1,
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
      '{kmac_pkg::AppCfgKeyMgr,
        kmac_pkg::AppCfgLcCtrl,
        kmac_pkg::AppCfgRomCtrl,
        kmac_pkg::AppCfgRomCtrl},
  // parameters for otbn
  parameter bit OtbnStub = 0,
  parameter otbn_pkg::regfile_e OtbnRegFile = otbn_pkg::RegFileFF,
  parameter bit SecOtbnMuteUrnd = 0,
  parameter bit SecOtbnFixMaiOpSeq = 0,
  parameter bit SecOtbnSkipUrndReseedAtStart = 0,
  parameter bit OtbnFeatStubMai = 0,
  // parameters for keymgr_dpe
  parameter bit KeymgrDpeKmacEnMasking = 1,
  // parameters for csrng
  parameter aes_pkg::sbox_impl_e CsrngSBoxImpl = aes_pkg::SBoxImplCanright,
  // parameters for entropy_src
  parameter int EntropySrcRngBusWidth = 16,
  parameter int EntropySrcRngBusBitSelWidth = 4,
  parameter int EntropySrcHealthTestWindowWidth = 20,
  parameter bit EntropySrcStub = 0,
  // parameters for sram_ctrl_main
  parameter int SramCtrlMainInstSize = 65536,
  parameter int SramCtrlMainNumRamInst = 1,
  parameter bit SramCtrlMainInstrExec = 1,
  parameter int SramCtrlMainNumPrinceRoundsHalf = 3,
  parameter bit SramCtrlMainEccCorrection = 0,
  // parameters for sram_ctrl_mbox
  parameter int SramCtrlMboxInstSize = 4096,
  parameter int SramCtrlMboxNumRamInst = 1,
  parameter bit SramCtrlMboxInstrExec = 0,
  parameter int SramCtrlMboxNumPrinceRoundsHalf = 3,
  parameter bit SramCtrlMboxEccCorrection = 0,
  // parameters for rom_ctrl0
  parameter RomCtrl0BootRomInitFile = "",
  parameter bit SecRomCtrl0DisableScrambling = 1'b0,
  // parameters for rom_ctrl1
  parameter RomCtrl1BootRomInitFile = "",
  parameter bit SecRomCtrl1DisableScrambling = 1'b0,
  // parameters for dma
  parameter bit DmaEnableDataIntgGen = 1'b1,
  parameter bit DmaEnableRspDataIntgCheck = 1'b1,
  parameter logic [tlul_pkg::RsvdWidth-1:0] DmaTlUserRsvd = '0,
  parameter top_racl_pkg::racl_role_t DmaSysRaclRole = '0,
  parameter int unsigned DmaOtAgentId = 0,
  // parameters for racl_ctrl
  parameter int RaclCtrlNumExternalSubscribingIps = 1,
  // parameters for ac_range_check
  parameter bit AcRangeCheckRangeCheckErrorRsp = 1,
  // parameters for rv_core_ibex
  parameter bit RvCoreIbexPMPEnable = 1,
  parameter int unsigned RvCoreIbexPMPGranularity = 0,
  parameter int unsigned RvCoreIbexPMPNumRegions = 16,
  parameter int unsigned RvCoreIbexMHPMCounterNum = 10,
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
  parameter bit RvCoreIbexPipeLine = 1,
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
  input  logic [11:0] mio_in_i,
  output logic [11:0] mio_out_o,
  output logic [11:0] mio_oe_o,

  // Dedicated I/O
  input  logic [72:0] dio_in_i,
  output logic [72:0] dio_out_o,
  output logic [72:0] dio_oe_o,

  // Pad attributes to padring
  output prim_pad_wrapper_pkg::pad_attr_t [pinmux_reg_pkg::NMioPads-1:0] mio_attr_o,
  output prim_pad_wrapper_pkg::pad_attr_t [pinmux_reg_pkg::NDioPads-1:0] dio_attr_o,

  // Inter-module Signal External type
  output lc_ctrl_pkg::lc_tx_t       ast_lc_dft_en_o,
  output lc_ctrl_pkg::lc_tx_t       ast_lc_hw_debug_en_o,
  input  ast_pkg::ast_obs_ctrl_t       obs_ctrl_i,
  input  prim_ram_1p_pkg::ram_1p_cfg_req_t       otbn_imem_ram_cfg_req_i,
  output prim_ram_1p_pkg::ram_1p_cfg_rsp_t       otbn_imem_ram_cfg_rsp_o,
  input  prim_ram_1p_pkg::ram_1p_cfg_req_t       otbn_dmem_ram_cfg_req_i,
  output prim_ram_1p_pkg::ram_1p_cfg_rsp_t       otbn_dmem_ram_cfg_rsp_o,
  input  prim_ram_1p_pkg::ram_1p_cfg_req_t       i2c0_ram_cfg_req_i,
  output prim_ram_1p_pkg::ram_1p_cfg_rsp_t       i2c0_ram_cfg_rsp_o,
  input  prim_ram_1p_pkg::ram_1p_cfg_req_t [RvCoreIbexICacheNWays-1:0] rv_core_ibex_icache_tag_ram_cfg_req_i,
  output prim_ram_1p_pkg::ram_1p_cfg_rsp_t [RvCoreIbexICacheNWays-1:0] rv_core_ibex_icache_tag_ram_cfg_rsp_o,
  input  prim_ram_1p_pkg::ram_1p_cfg_req_t [RvCoreIbexICacheNWays-1:0] rv_core_ibex_icache_data_ram_cfg_req_i,
  output prim_ram_1p_pkg::ram_1p_cfg_rsp_t [RvCoreIbexICacheNWays-1:0] rv_core_ibex_icache_data_ram_cfg_rsp_o,
  input  prim_ram_1r1w_pkg::ram_1r1w_cfg_req_t       spi_device_sys2spi_ram_cfg_req_i,
  output prim_ram_1r1w_pkg::ram_1r1w_cfg_rsp_t       spi_device_sys2spi_ram_cfg_rsp_o,
  input  prim_ram_1r1w_pkg::ram_1r1w_cfg_req_t       spi_device_spi2sys_ram_cfg_req_i,
  output prim_ram_1r1w_pkg::ram_1r1w_cfg_rsp_t       spi_device_spi2sys_ram_cfg_rsp_o,
  input  prim_rom_pkg::rom_cfg_req_t       rom_ctrl0_rom_cfg_req_i,
  output prim_rom_pkg::rom_cfg_rsp_t       rom_ctrl0_rom_cfg_rsp_o,
  input  prim_rom_pkg::rom_cfg_req_t       rom_ctrl1_rom_cfg_req_i,
  output prim_rom_pkg::rom_cfg_rsp_t       rom_ctrl1_rom_cfg_rsp_o,
  input  prim_ram_1p_pkg::ram_1p_cfg_req_t [SramCtrlMainNumRamInst-1:0] sram_ctrl_main_ram_cfg_req_i,
  output prim_ram_1p_pkg::ram_1p_cfg_rsp_t [SramCtrlMainNumRamInst-1:0] sram_ctrl_main_ram_cfg_rsp_o,
  input  prim_ram_1p_pkg::ram_1p_cfg_req_t [SramCtrlRetAonNumRamInst-1:0] sram_ctrl_ret_aon_ram_cfg_req_i,
  output prim_ram_1p_pkg::ram_1p_cfg_rsp_t [SramCtrlRetAonNumRamInst-1:0] sram_ctrl_ret_aon_ram_cfg_rsp_o,
  input  prim_ram_1p_pkg::ram_1p_cfg_req_t [SramCtrlMboxNumRamInst-1:0] sram_ctrl_mbox_ram_cfg_req_i,
  output prim_ram_1p_pkg::ram_1p_cfg_rsp_t [SramCtrlMboxNumRamInst-1:0] sram_ctrl_mbox_ram_cfg_rsp_o,
  output pwrmgr_pkg::pwr_boot_status_t       pwrmgr_boot_status_o,
  input  logic       pwrmgr_ext_rst_ack_i,
  output clkmgr_pkg::clkmgr_out_t       clkmgr_aon_clocks_o,
  output clkmgr_pkg::clkmgr_cg_en_t       clkmgr_aon_cg_en_o,
  output prim_mubi_pkg::mubi4_t       clk_main_jitter_en_o,
  output dma_pkg::sys_req_t       dma_sys_req_o,
  input  dma_pkg::sys_rsp_t       dma_sys_rsp_i,
  output logic       es_rng_enable_o,
  input  logic       es_rng_valid_i,
  input  logic [EntropySrcRngBusWidth-1:0] es_rng_bit_i,
  output logic       es_rng_fips_o,
  input  tlul_pkg::tl_h2d_t       mbx_tl_req_i,
  output tlul_pkg::tl_d2h_t       mbx_tl_rsp_o,
  output logic       mbx0_doe_intr_o,
  output logic       mbx0_doe_intr_en_o,
  output logic       mbx0_doe_intr_support_o,
  output logic       mbx0_doe_async_msg_support_o,
  output logic       mbx1_doe_intr_o,
  output logic       mbx1_doe_intr_en_o,
  output logic       mbx1_doe_intr_support_o,
  output logic       mbx1_doe_async_msg_support_o,
  output logic       mbx2_doe_intr_o,
  output logic       mbx2_doe_intr_en_o,
  output logic       mbx2_doe_intr_support_o,
  output logic       mbx2_doe_async_msg_support_o,
  output logic       mbx3_doe_intr_o,
  output logic       mbx3_doe_intr_en_o,
  output logic       mbx3_doe_intr_support_o,
  output logic       mbx3_doe_async_msg_support_o,
  output logic       mbx4_doe_intr_o,
  output logic       mbx4_doe_intr_en_o,
  output logic       mbx4_doe_intr_support_o,
  output logic       mbx4_doe_async_msg_support_o,
  output logic       mbx5_doe_intr_o,
  output logic       mbx5_doe_intr_en_o,
  output logic       mbx5_doe_intr_support_o,
  output logic       mbx5_doe_async_msg_support_o,
  output logic       mbx6_doe_intr_o,
  output logic       mbx6_doe_intr_en_o,
  output logic       mbx6_doe_intr_support_o,
  output logic       mbx6_doe_async_msg_support_o,
  output logic       mbx_jtag_doe_intr_o,
  output logic       mbx_jtag_doe_intr_en_o,
  output logic       mbx_jtag_doe_intr_support_o,
  output logic       mbx_jtag_doe_async_msg_support_o,
  output logic       mbx_pcie0_doe_intr_o,
  output logic       mbx_pcie0_doe_intr_en_o,
  output logic       mbx_pcie0_doe_intr_support_o,
  output logic       mbx_pcie0_doe_async_msg_support_o,
  output logic       mbx_pcie1_doe_intr_o,
  output logic       mbx_pcie1_doe_intr_en_o,
  output logic       mbx_pcie1_doe_intr_support_o,
  output logic       mbx_pcie1_doe_async_msg_support_o,
  input  tlul_pkg::tl_h2d_t       dbg_tl_req_i,
  output tlul_pkg::tl_d2h_t       dbg_tl_rsp_o,
  input  rv_dm_pkg::next_dm_addr_t       rv_dm_next_dm_addr_i,
  output tlul_pkg::tl_h2d_t       ast_tl_req_o,
  input  tlul_pkg::tl_d2h_t       ast_tl_rsp_i,
  output pwrmgr_pkg::pwr_ast_req_t       pwrmgr_ast_req_o,
  input  pwrmgr_pkg::pwr_ast_rsp_t       pwrmgr_ast_rsp_i,
  output otp_macro_pkg::pwr_seq_t       otp_macro_pwr_seq_o,
  input  otp_macro_pkg::pwr_seq_t       otp_macro_pwr_seq_h_i,
  inout         otp_ext_voltage_h_io,
  output logic [7:0] otp_obs_o,
  input  otp_macro_pkg::otp_cfg_t       otp_cfg_i,
  input  logic [1:0] por_n_i,
  output rstmgr_pkg::rstmgr_out_t       rstmgr_aon_resets_o,
  output rstmgr_pkg::rstmgr_rst_en_t       rstmgr_aon_rst_en_o,
  input  logic [31:0] fpga_info_i,
  input  tlul_pkg::tl_h2d_t       ctn_misc_tl_h2d_i,
  output tlul_pkg::tl_d2h_t       ctn_misc_tl_d2h_o,
  input  logic       soc_wkup_async_i,
  input  logic       soc_rst_req_async_i,
  input  logic [7:0] soc_lsio_trigger_i,
  output logic [15:0] soc_gpi_async_o,
  input  logic [15:0] soc_gpo_async_i,
  input  logic [3:0] integrator_id_i,
  output logic       sck_monitor_o,
  output soc_dbg_ctrl_pkg::soc_dbg_policy_t       soc_dbg_policy_bus_o,
  input  logic       debug_halt_cpu_boot_i,
  output top_racl_pkg::racl_policy_vec_t       racl_policies_o,
  input  top_racl_pkg::racl_error_log_t [RaclCtrlNumExternalSubscribingIps-1:0] racl_error_i,
  input  prim_mubi_pkg::mubi8_t       ac_range_check_overwrite_i,
  output tlul_pkg::tl_h2d_t       ctn_tl_h2d_o,
  input  tlul_pkg::tl_d2h_t       ctn_tl_d2h_i

);

  import top_darjeeling_pkg::*;
  import prim_pad_wrapper_pkg::*;

  // Inter-Power Domain signals
  logic [2:0] intr_vector_pd_aon;
  prim_alert_pkg::alert_tx_t [7:0] alert_tx_pd_aon;
  prim_alert_pkg::alert_rx_t [7:0] alert_rx_pd_aon;
  alert_handler_pkg::alert_crashdump_t       alert_handler_crashdump;
  prim_esc_pkg::esc_rx_t       alert_handler_esc_rx;
  prim_esc_pkg::esc_tx_t       alert_handler_esc_tx;
  logic       aon_timer_aon_nmi_wdog_timer_bark;
  otp_ctrl_pkg::sram_otp_key_req_t       otp_ctrl_sram_otp_key_req;
  otp_ctrl_pkg::sram_otp_key_rsp_t       otp_ctrl_sram_otp_key_rsp;
  pwrmgr_pkg::pwr_otp_req_t       pwrmgr_aon_pwr_otp_req;
  pwrmgr_pkg::pwr_otp_rsp_t       pwrmgr_aon_pwr_otp_rsp;
  lc_ctrl_pkg::pwr_lc_req_t       pwrmgr_aon_pwr_lc_req;
  lc_ctrl_pkg::pwr_lc_rsp_t       pwrmgr_aon_pwr_lc_rsp;
  logic       pwrmgr_aon_strap;
  logic       pwrmgr_aon_low_power;
  lc_ctrl_pkg::lc_tx_t       pwrmgr_aon_fetch_en;
  rom_ctrl_pkg::pwrmgr_data_t [2:0] pwrmgr_aon_rom_ctrl;
  pwrmgr_pkg::pwr_boot_status_t       pwrmgr_aon_boot_status;
  dma_pkg::lsio_trigger_t       dma_lsio_trigger;
  logic       i2c0_lsio_trigger;
  logic       spi_host0_lsio_trigger;
  logic       uart0_lsio_trigger;
  prim_mubi_pkg::mubi4_t [3:0] clkmgr_aon_idle;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_dft_en;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_hw_debug_en;
  lc_ctrl_pkg::lc_tx_t       lc_ctrl_lc_escalate_en;
  rv_core_ibex_pkg::cpu_crash_dump_t       rv_core_ibex_crash_dump;
  rv_core_ibex_pkg::cpu_pwrmgr_t       rv_core_ibex_pwrmgr;
  logic       rv_dm_ndmreset_req;
  tlul_pkg::tl_h2d_t       soc_proxy_dma_tl_h2d;
  tlul_pkg::tl_d2h_t       soc_proxy_dma_tl_d2h;
  tlul_pkg::tl_h2d_t       soc_proxy_ctn_tl_h2d;
  tlul_pkg::tl_d2h_t       soc_proxy_ctn_tl_d2h;
  logic       pwrmgr_aon_wakeups;
  tlul_pkg::tl_h2d_t       soc_proxy_core_tl_req;
  tlul_pkg::tl_d2h_t       soc_proxy_core_tl_rsp;
  tlul_pkg::tl_h2d_t       soc_proxy_ctn_tl_req;
  tlul_pkg::tl_d2h_t       soc_proxy_ctn_tl_rsp;
  tlul_pkg::tl_h2d_t       pwrmgr_aon_tl_req;
  tlul_pkg::tl_d2h_t       pwrmgr_aon_tl_rsp;
  tlul_pkg::tl_h2d_t       rstmgr_aon_tl_req;
  tlul_pkg::tl_d2h_t       rstmgr_aon_tl_rsp;
  tlul_pkg::tl_h2d_t       clkmgr_aon_tl_req;
  tlul_pkg::tl_d2h_t       clkmgr_aon_tl_rsp;
  tlul_pkg::tl_h2d_t       sram_ctrl_ret_aon_regs_tl_req;
  tlul_pkg::tl_d2h_t       sram_ctrl_ret_aon_regs_tl_rsp;
  tlul_pkg::tl_h2d_t       sram_ctrl_ret_aon_ram_tl_req;
  tlul_pkg::tl_d2h_t       sram_ctrl_ret_aon_ram_tl_rsp;
  tlul_pkg::tl_h2d_t       aon_timer_aon_tl_req;
  tlul_pkg::tl_d2h_t       aon_timer_aon_tl_rsp;
  logic [15:0] cio_soc_proxy_soc_gpi_p2d;
  logic [15:0] cio_soc_proxy_soc_gpo_d2p;
  logic [15:0] cio_soc_proxy_soc_gpo_en_d2p;


  ///////////////////////////
  // Top-level Main Domain //
  ///////////////////////////
  darjeeling_pd_main #(
  // Auto-inferred parameters
  .GpioGpioAsyncOn(GpioGpioAsyncOn),
  .GpioGpioAsHwStrapsEn(GpioGpioAsHwStrapsEn),
  .SpiDeviceSramType(SpiDeviceSramType),
  .I2c0InputDelayCycles(I2c0InputDelayCycles),
  .OtpMacroMemInitFile(OtpMacroMemInitFile),
  .SecLcCtrlVolatileRawUnlockEn(SecLcCtrlVolatileRawUnlockEn),
  .LcCtrlUseDmiInterface(LcCtrlUseDmiInterface),
  .LcCtrlSiliconCreatorId(LcCtrlSiliconCreatorId),
  .LcCtrlProductId(LcCtrlProductId),
  .LcCtrlRevisionId(LcCtrlRevisionId),
  .LcCtrlIdcodeValue(LcCtrlIdcodeValue),
  .AlertHandlerEscNumSeverities(AlertHandlerEscNumSeverities),
  .AlertHandlerEscPingCountWidth(AlertHandlerEscPingCountWidth),
  .PinmuxAonTargetCfg(PinmuxAonTargetCfg),
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
  .SramCtrlMainEccCorrection(SramCtrlMainEccCorrection),
  .SramCtrlMboxInstSize(SramCtrlMboxInstSize),
  .SramCtrlMboxNumRamInst(SramCtrlMboxNumRamInst),
  .SramCtrlMboxInstrExec(SramCtrlMboxInstrExec),
  .SramCtrlMboxNumPrinceRoundsHalf(SramCtrlMboxNumPrinceRoundsHalf),
  .SramCtrlMboxEccCorrection(SramCtrlMboxEccCorrection),
  .RomCtrl0BootRomInitFile(RomCtrl0BootRomInitFile),
  .SecRomCtrl0DisableScrambling(SecRomCtrl0DisableScrambling),
  .RomCtrl1BootRomInitFile(RomCtrl1BootRomInitFile),
  .SecRomCtrl1DisableScrambling(SecRomCtrl1DisableScrambling),
  .DmaEnableDataIntgGen(DmaEnableDataIntgGen),
  .DmaEnableRspDataIntgCheck(DmaEnableRspDataIntgCheck),
  .DmaTlUserRsvd(DmaTlUserRsvd),
  .DmaSysRaclRole(DmaSysRaclRole),
  .DmaOtAgentId(DmaOtAgentId),
  .RaclCtrlNumExternalSubscribingIps(RaclCtrlNumExternalSubscribingIps),
  .AcRangeCheckRangeCheckErrorRsp(AcRangeCheckRangeCheckErrorRsp),
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
  ) darjeeling_pd_main (
    // Clocks and clock gating control from clkmgr_aon
    .clkmgr_aon_clocks_i(clkmgr_aon_clocks_o),
    .clkmgr_aon_cg_en_i (clkmgr_aon_cg_en_o),

    // Resets and reset assert info from rstmgr_aon
    .rstmgr_aon_resets_i(rstmgr_aon_resets_o),
    .rstmgr_aon_rst_en_i(rstmgr_aon_rst_en_o),

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
    .alert_handler_crashdump_o          (alert_handler_crashdump  ),
    .alert_handler_esc_rx_i             (alert_handler_esc_rx     ),
    .alert_handler_esc_tx_o             (alert_handler_esc_tx     ),
    .aon_timer_aon_nmi_wdog_timer_bark_i(aon_timer_aon_nmi_wdog_timer_bark),
    .otp_ctrl_sram_otp_key_req_i        (otp_ctrl_sram_otp_key_req),
    .otp_ctrl_sram_otp_key_rsp_o        (otp_ctrl_sram_otp_key_rsp),
    .pwrmgr_aon_pwr_otp_req_i           (pwrmgr_aon_pwr_otp_req   ),
    .pwrmgr_aon_pwr_otp_rsp_o           (pwrmgr_aon_pwr_otp_rsp   ),
    .pwrmgr_aon_pwr_lc_req_i            (pwrmgr_aon_pwr_lc_req    ),
    .pwrmgr_aon_pwr_lc_rsp_o            (pwrmgr_aon_pwr_lc_rsp    ),
    .pwrmgr_aon_strap_i                 (pwrmgr_aon_strap         ),
    .pwrmgr_aon_low_power_i             (pwrmgr_aon_low_power     ),
    .pwrmgr_aon_fetch_en_i              (pwrmgr_aon_fetch_en      ),
    .pwrmgr_aon_rom_ctrl_o              (pwrmgr_aon_rom_ctrl      ),
    .pwrmgr_aon_boot_status_i           (pwrmgr_aon_boot_status   ),
    .dma_lsio_trigger_i                 (dma_lsio_trigger         ),
    .i2c0_lsio_trigger_o                (i2c0_lsio_trigger        ),
    .spi_host0_lsio_trigger_o           (spi_host0_lsio_trigger   ),
    .uart0_lsio_trigger_o               (uart0_lsio_trigger       ),
    .clkmgr_aon_idle_o                  (clkmgr_aon_idle          ),
    .lc_ctrl_lc_dft_en_o                (lc_ctrl_lc_dft_en        ),
    .lc_ctrl_lc_hw_debug_en_o           (lc_ctrl_lc_hw_debug_en   ),
    .lc_ctrl_lc_escalate_en_o           (lc_ctrl_lc_escalate_en   ),
    .rv_core_ibex_crash_dump_o          (rv_core_ibex_crash_dump  ),
    .rv_core_ibex_pwrmgr_o              (rv_core_ibex_pwrmgr      ),
    .rv_dm_ndmreset_req_o               (rv_dm_ndmreset_req       ),
    .soc_proxy_dma_tl_h2d_o             (soc_proxy_dma_tl_h2d     ),
    .soc_proxy_dma_tl_d2h_i             (soc_proxy_dma_tl_d2h     ),
    .soc_proxy_ctn_tl_h2d_i             (soc_proxy_ctn_tl_h2d     ),
    .soc_proxy_ctn_tl_d2h_o             (soc_proxy_ctn_tl_d2h     ),
    .pwrmgr_aon_wakeups_o               (pwrmgr_aon_wakeups       ),
    .soc_proxy_core_tl_req_o            (soc_proxy_core_tl_req    ),
    .soc_proxy_core_tl_rsp_i            (soc_proxy_core_tl_rsp    ),
    .soc_proxy_ctn_tl_req_o             (soc_proxy_ctn_tl_req     ),
    .soc_proxy_ctn_tl_rsp_i             (soc_proxy_ctn_tl_rsp     ),
    .pwrmgr_aon_tl_req_o                (pwrmgr_aon_tl_req        ),
    .pwrmgr_aon_tl_rsp_i                (pwrmgr_aon_tl_rsp        ),
    .rstmgr_aon_tl_req_o                (rstmgr_aon_tl_req        ),
    .rstmgr_aon_tl_rsp_i                (rstmgr_aon_tl_rsp        ),
    .clkmgr_aon_tl_req_o                (clkmgr_aon_tl_req        ),
    .clkmgr_aon_tl_rsp_i                (clkmgr_aon_tl_rsp        ),
    .sram_ctrl_ret_aon_regs_tl_req_o    (sram_ctrl_ret_aon_regs_tl_req),
    .sram_ctrl_ret_aon_regs_tl_rsp_i    (sram_ctrl_ret_aon_regs_tl_rsp),
    .sram_ctrl_ret_aon_ram_tl_req_o     (sram_ctrl_ret_aon_ram_tl_req),
    .sram_ctrl_ret_aon_ram_tl_rsp_i     (sram_ctrl_ret_aon_ram_tl_rsp),
    .aon_timer_aon_tl_req_o             (aon_timer_aon_tl_req     ),
    .aon_timer_aon_tl_rsp_i             (aon_timer_aon_tl_rsp     ),
    .cio_soc_proxy_soc_gpi_p2d_o        (cio_soc_proxy_soc_gpi_p2d),
    .cio_soc_proxy_soc_gpo_d2p_i        (cio_soc_proxy_soc_gpo_d2p),
    .cio_soc_proxy_soc_gpo_en_d2p_i     (cio_soc_proxy_soc_gpo_en_d2p),

    // Regular ports (auto-generated)
    .ast_lc_dft_en_o,
    .ast_lc_hw_debug_en_o,
    .obs_ctrl_i,
    .otbn_imem_ram_cfg_req_i,
    .otbn_imem_ram_cfg_rsp_o,
    .otbn_dmem_ram_cfg_req_i,
    .otbn_dmem_ram_cfg_rsp_o,
    .i2c0_ram_cfg_req_i,
    .i2c0_ram_cfg_rsp_o,
    .rv_core_ibex_icache_tag_ram_cfg_req_i,
    .rv_core_ibex_icache_tag_ram_cfg_rsp_o,
    .rv_core_ibex_icache_data_ram_cfg_req_i,
    .rv_core_ibex_icache_data_ram_cfg_rsp_o,
    .spi_device_sys2spi_ram_cfg_req_i,
    .spi_device_sys2spi_ram_cfg_rsp_o,
    .spi_device_spi2sys_ram_cfg_req_i,
    .spi_device_spi2sys_ram_cfg_rsp_o,
    .rom_ctrl0_rom_cfg_req_i,
    .rom_ctrl0_rom_cfg_rsp_o,
    .rom_ctrl1_rom_cfg_req_i,
    .rom_ctrl1_rom_cfg_rsp_o,
    .sram_ctrl_main_ram_cfg_req_i,
    .sram_ctrl_main_ram_cfg_rsp_o,
    .sram_ctrl_mbox_ram_cfg_req_i,
    .sram_ctrl_mbox_ram_cfg_rsp_o,
    .dma_sys_req_o,
    .dma_sys_rsp_i,
    .es_rng_enable_o,
    .es_rng_valid_i,
    .es_rng_bit_i,
    .es_rng_fips_o,
    .mbx_tl_req_i,
    .mbx_tl_rsp_o,
    .mbx0_doe_intr_o,
    .mbx0_doe_intr_en_o,
    .mbx0_doe_intr_support_o,
    .mbx0_doe_async_msg_support_o,
    .mbx1_doe_intr_o,
    .mbx1_doe_intr_en_o,
    .mbx1_doe_intr_support_o,
    .mbx1_doe_async_msg_support_o,
    .mbx2_doe_intr_o,
    .mbx2_doe_intr_en_o,
    .mbx2_doe_intr_support_o,
    .mbx2_doe_async_msg_support_o,
    .mbx3_doe_intr_o,
    .mbx3_doe_intr_en_o,
    .mbx3_doe_intr_support_o,
    .mbx3_doe_async_msg_support_o,
    .mbx4_doe_intr_o,
    .mbx4_doe_intr_en_o,
    .mbx4_doe_intr_support_o,
    .mbx4_doe_async_msg_support_o,
    .mbx5_doe_intr_o,
    .mbx5_doe_intr_en_o,
    .mbx5_doe_intr_support_o,
    .mbx5_doe_async_msg_support_o,
    .mbx6_doe_intr_o,
    .mbx6_doe_intr_en_o,
    .mbx6_doe_intr_support_o,
    .mbx6_doe_async_msg_support_o,
    .mbx_jtag_doe_intr_o,
    .mbx_jtag_doe_intr_en_o,
    .mbx_jtag_doe_intr_support_o,
    .mbx_jtag_doe_async_msg_support_o,
    .mbx_pcie0_doe_intr_o,
    .mbx_pcie0_doe_intr_en_o,
    .mbx_pcie0_doe_intr_support_o,
    .mbx_pcie0_doe_async_msg_support_o,
    .mbx_pcie1_doe_intr_o,
    .mbx_pcie1_doe_intr_en_o,
    .mbx_pcie1_doe_intr_support_o,
    .mbx_pcie1_doe_async_msg_support_o,
    .dbg_tl_req_i,
    .dbg_tl_rsp_o,
    .rv_dm_next_dm_addr_i,
    .ast_tl_req_o,
    .ast_tl_rsp_i,
    .otp_macro_pwr_seq_o,
    .otp_macro_pwr_seq_h_i,
    .otp_ext_voltage_h_io,
    .otp_obs_o,
    .otp_cfg_i,
    .fpga_info_i,
    .sck_monitor_o,
    .soc_dbg_policy_bus_o,
    .debug_halt_cpu_boot_i,
    .racl_policies_o,
    .racl_error_i,
    .ac_range_check_overwrite_i,
    .ctn_tl_h2d_o,
    .ctn_tl_d2h_i
  );

  //////////////////////////
  // Top-level Aon Domain //
  //////////////////////////
  darjeeling_pd_aon #(
  // Auto-inferred parameters
  .SecRstmgrAonCheck(SecRstmgrAonCheck),
  .SecRstmgrAonMaxSyncDelay(SecRstmgrAonMaxSyncDelay),
  .SramCtrlRetAonInstSize(SramCtrlRetAonInstSize),
  .SramCtrlRetAonNumRamInst(SramCtrlRetAonNumRamInst),
  .SramCtrlRetAonInstrExec(SramCtrlRetAonInstrExec),
  .SramCtrlRetAonNumPrinceRoundsHalf(SramCtrlRetAonNumPrinceRoundsHalf),
  .SramCtrlRetAonEccCorrection(SramCtrlRetAonEccCorrection)
  ) darjeeling_pd_aon (
    // All externally supplied clocks
    .clk_main_i(ast_base_clks_i.clk_sys),
    .clk_io_i  (ast_base_clks_i.clk_io ),
    .clk_aon_i (ast_base_clks_i.clk_aon),

    // Manual DFT signals
    .scan_rst_ni,
    .scanmode_i,

    // Special inter-power domain signals (interrupts, alerts)
    .intr_vector_o(intr_vector_pd_aon),

    .alert_tx_o(alert_tx_pd_aon),
    .alert_rx_i(alert_rx_pd_aon),

    // Ports to and from other power domains (auto-generated)
    .alert_handler_crashdump_i          (alert_handler_crashdump  ),
    .alert_handler_esc_rx_o             (alert_handler_esc_rx     ),
    .alert_handler_esc_tx_i             (alert_handler_esc_tx     ),
    .aon_timer_aon_nmi_wdog_timer_bark_o(aon_timer_aon_nmi_wdog_timer_bark),
    .otp_ctrl_sram_otp_key_req_o        (otp_ctrl_sram_otp_key_req),
    .otp_ctrl_sram_otp_key_rsp_i        (otp_ctrl_sram_otp_key_rsp),
    .pwrmgr_aon_pwr_otp_req_o           (pwrmgr_aon_pwr_otp_req   ),
    .pwrmgr_aon_pwr_otp_rsp_i           (pwrmgr_aon_pwr_otp_rsp   ),
    .pwrmgr_aon_pwr_lc_req_o            (pwrmgr_aon_pwr_lc_req    ),
    .pwrmgr_aon_pwr_lc_rsp_i            (pwrmgr_aon_pwr_lc_rsp    ),
    .pwrmgr_aon_strap_o                 (pwrmgr_aon_strap         ),
    .pwrmgr_aon_low_power_o             (pwrmgr_aon_low_power     ),
    .pwrmgr_aon_fetch_en_o              (pwrmgr_aon_fetch_en      ),
    .pwrmgr_aon_rom_ctrl_i              (pwrmgr_aon_rom_ctrl      ),
    .pwrmgr_aon_boot_status_o           (pwrmgr_aon_boot_status   ),
    .dma_lsio_trigger_o                 (dma_lsio_trigger         ),
    .i2c0_lsio_trigger_i                (i2c0_lsio_trigger        ),
    .spi_host0_lsio_trigger_i           (spi_host0_lsio_trigger   ),
    .uart0_lsio_trigger_i               (uart0_lsio_trigger       ),
    .clkmgr_aon_idle_i                  (clkmgr_aon_idle          ),
    .lc_ctrl_lc_dft_en_i                (lc_ctrl_lc_dft_en        ),
    .lc_ctrl_lc_hw_debug_en_i           (lc_ctrl_lc_hw_debug_en   ),
    .lc_ctrl_lc_escalate_en_i           (lc_ctrl_lc_escalate_en   ),
    .rv_core_ibex_crash_dump_i          (rv_core_ibex_crash_dump  ),
    .rv_core_ibex_pwrmgr_i              (rv_core_ibex_pwrmgr      ),
    .rv_dm_ndmreset_req_i               (rv_dm_ndmreset_req       ),
    .soc_proxy_dma_tl_h2d_i             (soc_proxy_dma_tl_h2d     ),
    .soc_proxy_dma_tl_d2h_o             (soc_proxy_dma_tl_d2h     ),
    .soc_proxy_ctn_tl_h2d_o             (soc_proxy_ctn_tl_h2d     ),
    .soc_proxy_ctn_tl_d2h_i             (soc_proxy_ctn_tl_d2h     ),
    .pwrmgr_aon_wakeups_i               (pwrmgr_aon_wakeups       ),
    .soc_proxy_core_tl_req_i            (soc_proxy_core_tl_req    ),
    .soc_proxy_core_tl_rsp_o            (soc_proxy_core_tl_rsp    ),
    .soc_proxy_ctn_tl_req_i             (soc_proxy_ctn_tl_req     ),
    .soc_proxy_ctn_tl_rsp_o             (soc_proxy_ctn_tl_rsp     ),
    .pwrmgr_aon_tl_req_i                (pwrmgr_aon_tl_req        ),
    .pwrmgr_aon_tl_rsp_o                (pwrmgr_aon_tl_rsp        ),
    .rstmgr_aon_tl_req_i                (rstmgr_aon_tl_req        ),
    .rstmgr_aon_tl_rsp_o                (rstmgr_aon_tl_rsp        ),
    .clkmgr_aon_tl_req_i                (clkmgr_aon_tl_req        ),
    .clkmgr_aon_tl_rsp_o                (clkmgr_aon_tl_rsp        ),
    .sram_ctrl_ret_aon_regs_tl_req_i    (sram_ctrl_ret_aon_regs_tl_req),
    .sram_ctrl_ret_aon_regs_tl_rsp_o    (sram_ctrl_ret_aon_regs_tl_rsp),
    .sram_ctrl_ret_aon_ram_tl_req_i     (sram_ctrl_ret_aon_ram_tl_req),
    .sram_ctrl_ret_aon_ram_tl_rsp_o     (sram_ctrl_ret_aon_ram_tl_rsp),
    .aon_timer_aon_tl_req_i             (aon_timer_aon_tl_req     ),
    .aon_timer_aon_tl_rsp_o             (aon_timer_aon_tl_rsp     ),
    .cio_soc_proxy_soc_gpi_p2d_i        (cio_soc_proxy_soc_gpi_p2d),
    .cio_soc_proxy_soc_gpo_d2p_o        (cio_soc_proxy_soc_gpo_d2p),
    .cio_soc_proxy_soc_gpo_en_d2p_o     (cio_soc_proxy_soc_gpo_en_d2p),

    // Regular ports (auto-generated)
    .sram_ctrl_ret_aon_ram_cfg_req_i,
    .sram_ctrl_ret_aon_ram_cfg_rsp_o,
    .pwrmgr_boot_status_o,
    .pwrmgr_ext_rst_ack_i,
    .clkmgr_aon_clocks_o,
    .clkmgr_aon_cg_en_o,
    .clk_main_jitter_en_o,
    .pwrmgr_ast_req_o,
    .pwrmgr_ast_rsp_i,
    .por_n_i,
    .rstmgr_aon_resets_o,
    .rstmgr_aon_rst_en_o,
    .ctn_misc_tl_h2d_i,
    .ctn_misc_tl_d2h_o,
    .soc_wkup_async_i,
    .soc_rst_req_async_i,
    .soc_lsio_trigger_i,
    .soc_gpi_async_o,
    .soc_gpo_async_i,
    .integrator_id_i
  );

endmodule
