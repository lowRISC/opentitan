// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_englishbreakfast/data/top_englishbreakfast.hjson
//                -o hw/top_englishbreakfast/


// This wrapper hosts all power domain wrappers and the connections between them for englishbreakfast.
module top_englishbreakfast #(
  // Auto-inferred parameters
  // parameters for gpio
  parameter bit GpioGpioAsyncOn = 1,
  parameter bit GpioGpioAsHwStrapsEn = 1'b1,
  // parameters for spi_device
  parameter spi_device_pkg::sram_type_e SpiDeviceSramType = spi_device_pkg::DefaultSramType,
  // parameters for usbdev
  parameter bit UsbdevStub = 0,
  parameter int UsbdevRcvrWakeTimeUs = 1,
  // parameters for rstmgr_aon
  parameter bit SecRstmgrAonCheck = 0,
  parameter int SecRstmgrAonMaxSyncDelay = 2,
  // parameters for pinmux_aon
  parameter bit SecPinmuxAonVolatileRawUnlockEn = 1'b0,
  parameter pinmux_pkg::target_cfg_t PinmuxAonTargetCfg = pinmux_pkg::DefaultTargetCfg,
  // parameters for flash_ctrl
  parameter bit SecFlashCtrlScrambleEn = 0,
  parameter int FlashCtrlProgFifoDepth = 16,
  parameter int FlashCtrlRdFifoDepth = 16,
  // parameters for aes
  parameter bit AesAESGCMEnable = 1,
  parameter bit SecAesMasking = 1,
  parameter aes_pkg::sbox_impl_e SecAesSBoxImpl = aes_pkg::SBoxImplDom,
  parameter int unsigned SecAesStartTriggerDelay = 0,
  parameter bit SecAesAllowForcingMasks = 1'b0,
  parameter bit SecAesSkipPRNGReseeding = 1'b0,
  // parameters for sram_ctrl_main
  parameter int SramCtrlMainInstSize = 4096,
  parameter int SramCtrlMainNumRamInst = 1,
  parameter bit SramCtrlMainInstrExec = 1,
  parameter int SramCtrlMainNumPrinceRoundsHalf = 3,
  parameter bit SramCtrlMainEccCorrection = 0,
  // parameters for rom_ctrl
  parameter RomCtrlBootRomInitFile = "",
  parameter bit SecRomCtrlDisableScrambling = 1'b1,
  // parameters for rv_core_ibex
  parameter bit RvCoreIbexPMPEnable = 0,
  parameter int unsigned RvCoreIbexPMPGranularity = 0,
  parameter int unsigned RvCoreIbexPMPNumRegions = 16,
  parameter int unsigned RvCoreIbexMHPMCounterNum = 0,
  parameter int unsigned RvCoreIbexMHPMCounterWidth = 32,
  parameter ibex_pkg::pmp_cfg_t RvCoreIbexPMPRstCfg[16] = ibex_pkg::PmpCfgRst,
  parameter logic [33:0] RvCoreIbexPMPRstAddr[16] = ibex_pkg::PmpAddrRst,
  parameter ibex_pkg::pmp_mseccfg_t RvCoreIbexPMPRstMsecCfg = ibex_pkg::PmpMseccfgRst,
  parameter bit RvCoreIbexRV32E = 0,
  parameter ibex_pkg::rv32m_e RvCoreIbexRV32M = ibex_pkg::RV32MSingleCycle,
  parameter ibex_pkg::rv32b_e RvCoreIbexRV32B = ibex_pkg::RV32BNone,
  parameter ibex_pkg::rv32zc_e RvCoreIbexRV32ZC = ibex_pkg::RV32ZcaZcbZcmp,
  parameter ibex_pkg::regfile_e RvCoreIbexRegFile = ibex_pkg::RegFileFF,
  parameter bit RvCoreIbexBranchTargetALU = 1,
  parameter bit RvCoreIbexWritebackStage = 1,
  parameter bit RvCoreIbexICache = 0,
  parameter bit RvCoreIbexICacheECC = 0,
  parameter bit RvCoreIbexICacheScramble = 0,
  parameter int unsigned RvCoreIbexICacheNWays = 2,
  parameter bit RvCoreIbexBranchPredictor = 0,
  parameter bit RvCoreIbexDbgTriggerEn = 1,
  parameter int RvCoreIbexDbgHwBreakNum = 1,
  parameter bit RvCoreIbexSecureIbex = 0,
  parameter int unsigned RvCoreIbexDmBaseAddr = 437321728,
  parameter int unsigned RvCoreIbexDmAddrMask = 4095,
  parameter int unsigned RvCoreIbexDmHaltAddr = 0,
  parameter int unsigned RvCoreIbexDmExceptionAddr = 0,
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
  input  logic [13:0] dio_in_i,
  output logic [13:0] dio_out_o,
  output logic [13:0] dio_oe_o,

  // Pad attributes to padring
  output prim_pad_wrapper_pkg::pad_attr_t [pinmux_reg_pkg::NMioPads-1:0] mio_attr_o,
  output prim_pad_wrapper_pkg::pad_attr_t [pinmux_reg_pkg::NDioPads-1:0] dio_attr_o,

  // Inter-module Signal External type
  output clkmgr_pkg::clkmgr_out_t       clkmgr_aon_clocks_o,
  output clkmgr_pkg::clkmgr_cg_en_t       clkmgr_aon_cg_en_o,
  output prim_mubi_pkg::mubi4_t       clk_main_jitter_en_o,
  output prim_mubi_pkg::mubi4_t       hi_speed_sel_o,
  input  prim_mubi_pkg::mubi4_t       div_step_down_req_i,
  output prim_mubi_pkg::mubi4_t       all_clk_byp_req_o,
  input  prim_mubi_pkg::mubi4_t       all_clk_byp_ack_i,
  output prim_mubi_pkg::mubi4_t       io_clk_byp_req_o,
  input  prim_mubi_pkg::mubi4_t       io_clk_byp_ack_i,
  input  prim_mubi_pkg::mubi4_t       flash_bist_enable_i,
  input  logic       flash_power_down_h_i,
  input  logic       flash_power_ready_h_i,
  input  ast_pkg::ast_obs_ctrl_t       obs_ctrl_i,
  output logic [7:0] flash_obs_o,
  output tlul_pkg::tl_h2d_t       ast_tl_req_o,
  input  tlul_pkg::tl_d2h_t       ast_tl_rsp_i,
  output pinmux_pkg::dft_strap_test_req_t       dft_strap_test_o,
  input  logic       dft_hold_tap_sel_i,
  output logic       usb_dp_pullup_en_o,
  output logic       usb_dn_pullup_en_o,
  output pwrmgr_pkg::pwr_ast_req_t       pwrmgr_ast_req_o,
  input  pwrmgr_pkg::pwr_ast_rsp_t       pwrmgr_ast_rsp_i,
  input  logic [1:0] por_n_i,
  output rstmgr_pkg::rstmgr_out_t       rstmgr_aon_resets_o,
  output rstmgr_pkg::rstmgr_rst_en_t       rstmgr_aon_rst_en_o,
  input  logic [31:0] fpga_info_i,
  input  logic       usbdev_usb_rx_d_i,
  output logic       usbdev_usb_tx_d_o,
  output logic       usbdev_usb_tx_se0_o,
  output logic       usbdev_usb_tx_use_d_se0_o,
  output logic       usbdev_usb_rx_enable_o,
  output logic       usbdev_usb_ref_val_o,
  output logic       usbdev_usb_ref_pulse_o,
  output logic       sck_monitor_o

);

  import top_englishbreakfast_pkg::*;
  import prim_pad_wrapper_pkg::*;

  // Inter-Power Domain signals
  logic [2:0] intr_vector_pd_aon;
  prim_alert_pkg::alert_tx_t [5:0] alertenglishbreakfast_tx_pd_aon;
  prim_alert_pkg::alert_rx_t [5:0] alertenglishbreakfast_rx_pd_aon;
  prim_alert_pkg::alert_tx_t [21:0] alertenglishbreakfast_tx_pd_main;
  prim_alert_pkg::alert_rx_t [21:0] alertenglishbreakfast_rx_pd_main;
  prim_mubi_pkg::mubi4_t [12:0] outgoing_lpg_cg_en_englishbreakfast;
  prim_mubi_pkg::mubi4_t [12:0] outgoing_lpg_rst_en_englishbreakfast;
  pwrmgr_pkg::pwr_nvm_t       pwrmgr_aon_pwr_nvm;
  logic       pwrmgr_aon_strap;
  logic       pwrmgr_aon_low_power;
  lc_ctrl_pkg::lc_tx_t       pwrmgr_aon_fetch_en;
  prim_mubi_pkg::mubi4_t       clkmgr_aon_idle;
  rv_core_ibex_pkg::cpu_crash_dump_t       rv_core_ibex_crash_dump;
  rv_core_ibex_pkg::cpu_pwrmgr_t       rv_core_ibex_pwrmgr;
  logic [1:0] pwrmgr_aon_wakeups;
  tlul_pkg::tl_h2d_t       pwrmgr_aon_tl_req;
  tlul_pkg::tl_d2h_t       pwrmgr_aon_tl_rsp;
  tlul_pkg::tl_h2d_t       rstmgr_aon_tl_req;
  tlul_pkg::tl_d2h_t       rstmgr_aon_tl_rsp;
  tlul_pkg::tl_h2d_t       clkmgr_aon_tl_req;
  tlul_pkg::tl_d2h_t       clkmgr_aon_tl_rsp;

  // Outgoing alerts are currently unused
  assign alertenglishbreakfast_rx_pd_main = '{default: prim_alert_pkg::ALERT_RX_DEFAULT};
  assign alertenglishbreakfast_rx_pd_aon  = '{default: prim_alert_pkg::ALERT_RX_DEFAULT};

  logic unused_alertenglishbreakfast_tx;
  assign unused_alertenglishbreakfast_tx = ^{
    alertenglishbreakfast_tx_pd_main,
    alertenglishbreakfast_tx_pd_aon
  };

  logic unused_outgoing_lpg_englishbreakfast;
  assign unused_outgoing_lpg_englishbreakfast = ^{
    outgoing_lpg_cg_en_englishbreakfast,
    outgoing_lpg_rst_en_englishbreakfast
  };

  ///////////////////////////
  // Top-level Main Domain //
  ///////////////////////////
  englishbreakfast_pd_main #(
  // Auto-inferred parameters
  .GpioGpioAsyncOn(GpioGpioAsyncOn),
  .GpioGpioAsHwStrapsEn(GpioGpioAsHwStrapsEn),
  .SpiDeviceSramType(SpiDeviceSramType),
  .UsbdevStub(UsbdevStub),
  .UsbdevRcvrWakeTimeUs(UsbdevRcvrWakeTimeUs),
  .SecPinmuxAonVolatileRawUnlockEn(SecPinmuxAonVolatileRawUnlockEn),
  .PinmuxAonTargetCfg(PinmuxAonTargetCfg),
  .SecFlashCtrlScrambleEn(SecFlashCtrlScrambleEn),
  .FlashCtrlProgFifoDepth(FlashCtrlProgFifoDepth),
  .FlashCtrlRdFifoDepth(FlashCtrlRdFifoDepth),
  .AesAESGCMEnable(AesAESGCMEnable),
  .SecAesMasking(SecAesMasking),
  .SecAesSBoxImpl(SecAesSBoxImpl),
  .SecAesStartTriggerDelay(SecAesStartTriggerDelay),
  .SecAesAllowForcingMasks(SecAesAllowForcingMasks),
  .SecAesSkipPRNGReseeding(SecAesSkipPRNGReseeding),
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
  ) englishbreakfast_pd_main (
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

    // Outgoing alerts for group englishbreakfast
    .outgoing_alert_englishbreakfast_tx_o(alertenglishbreakfast_tx_pd_main),
    .outgoing_alert_englishbreakfast_rx_i(alertenglishbreakfast_rx_pd_main),

    // Ports to and from other power domains (auto-generated)
    .pwrmgr_aon_pwr_nvm_o     (pwrmgr_aon_pwr_nvm     ),
    .pwrmgr_aon_strap_i       (pwrmgr_aon_strap       ),
    .pwrmgr_aon_low_power_i   (pwrmgr_aon_low_power   ),
    .pwrmgr_aon_fetch_en_i    (pwrmgr_aon_fetch_en    ),
    .clkmgr_aon_idle_o        (clkmgr_aon_idle        ),
    .rv_core_ibex_crash_dump_o(rv_core_ibex_crash_dump),
    .rv_core_ibex_pwrmgr_o    (rv_core_ibex_pwrmgr    ),
    .pwrmgr_aon_wakeups_o     (pwrmgr_aon_wakeups     ),
    .pwrmgr_aon_tl_req_o      (pwrmgr_aon_tl_req      ),
    .pwrmgr_aon_tl_rsp_i      (pwrmgr_aon_tl_rsp      ),
    .rstmgr_aon_tl_req_o      (rstmgr_aon_tl_req      ),
    .rstmgr_aon_tl_rsp_i      (rstmgr_aon_tl_rsp      ),
    .clkmgr_aon_tl_req_o      (clkmgr_aon_tl_req      ),
    .clkmgr_aon_tl_rsp_i      (clkmgr_aon_tl_rsp      ),

    // Regular ports (auto-generated)
    .flash_bist_enable_i,
    .flash_power_down_h_i,
    .flash_power_ready_h_i,
    .obs_ctrl_i,
    .flash_obs_o,
    .ast_tl_req_o,
    .ast_tl_rsp_i,
    .dft_strap_test_o,
    .dft_hold_tap_sel_i,
    .usb_dp_pullup_en_o,
    .usb_dn_pullup_en_o,
    .fpga_info_i,
    .usbdev_usb_rx_d_i,
    .usbdev_usb_tx_d_o,
    .usbdev_usb_tx_se0_o,
    .usbdev_usb_tx_use_d_se0_o,
    .usbdev_usb_rx_enable_o,
    .usbdev_usb_ref_val_o,
    .usbdev_usb_ref_pulse_o,
    .sck_monitor_o
  );

  //////////////////////////
  // Top-level Aon Domain //
  //////////////////////////
  englishbreakfast_pd_aon #(
  // Auto-inferred parameters
  .SecRstmgrAonCheck(SecRstmgrAonCheck),
  .SecRstmgrAonMaxSyncDelay(SecRstmgrAonMaxSyncDelay)
  ) englishbreakfast_pd_aon (
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

    // Outgoing alerts for group englishbreakfast
    .outgoing_alert_englishbreakfast_tx_o(alertenglishbreakfast_tx_pd_aon),
    .outgoing_alert_englishbreakfast_rx_i(alertenglishbreakfast_rx_pd_aon),
    .outgoing_lpg_cg_en_englishbreakfast_o(outgoing_lpg_cg_en_englishbreakfast),
    .outgoing_lpg_rst_en_englishbreakfast_o(outgoing_lpg_rst_en_englishbreakfast),

    // Ports to and from other power domains (auto-generated)
    .pwrmgr_aon_pwr_nvm_i     (pwrmgr_aon_pwr_nvm     ),
    .pwrmgr_aon_strap_o       (pwrmgr_aon_strap       ),
    .pwrmgr_aon_low_power_o   (pwrmgr_aon_low_power   ),
    .pwrmgr_aon_fetch_en_o    (pwrmgr_aon_fetch_en    ),
    .clkmgr_aon_idle_i        (clkmgr_aon_idle        ),
    .rv_core_ibex_crash_dump_i(rv_core_ibex_crash_dump),
    .rv_core_ibex_pwrmgr_i    (rv_core_ibex_pwrmgr    ),
    .pwrmgr_aon_wakeups_i     (pwrmgr_aon_wakeups     ),
    .pwrmgr_aon_tl_req_i      (pwrmgr_aon_tl_req      ),
    .pwrmgr_aon_tl_rsp_o      (pwrmgr_aon_tl_rsp      ),
    .rstmgr_aon_tl_req_i      (rstmgr_aon_tl_req      ),
    .rstmgr_aon_tl_rsp_o      (rstmgr_aon_tl_rsp      ),
    .clkmgr_aon_tl_req_i      (clkmgr_aon_tl_req      ),
    .clkmgr_aon_tl_rsp_o      (clkmgr_aon_tl_rsp      ),

    // Regular ports (auto-generated)
    .clkmgr_aon_clocks_o,
    .clkmgr_aon_cg_en_o,
    .clk_main_jitter_en_o,
    .hi_speed_sel_o,
    .div_step_down_req_i,
    .all_clk_byp_req_o,
    .all_clk_byp_ack_i,
    .io_clk_byp_req_o,
    .io_clk_byp_ack_i,
    .pwrmgr_ast_req_o,
    .pwrmgr_ast_rsp_i,
    .por_n_i,
    .rstmgr_aon_resets_o,
    .rstmgr_aon_rst_en_o
  );

endmodule
