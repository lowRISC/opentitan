// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_englishbreakfast/data/top_englishbreakfast.hjson
//                -o hw/top_englishbreakfast/

`include "prim_assert.sv"

module englishbreakfast_pd_main #(
  // Auto-inferred parameters
  // parameters for gpio
  parameter bit GpioGpioAsyncOn = 1,
  parameter bit GpioGpioAsHwStrapsEn = 1'b1,
  // parameters for spi_device
  parameter spi_device_pkg::sram_type_e SpiDeviceSramType = spi_device_pkg::DefaultSramType,
  // parameters for usbdev
  parameter bit UsbdevStub = 0,
  parameter int UsbdevRcvrWakeTimeUs = 1,
  // parameters for pinmux
  parameter bit SecPinmuxVolatileRawUnlockEn = 1'b0,
  parameter pinmux_pkg::target_cfg_t PinmuxTargetCfg = pinmux_pkg::DefaultTargetCfg,
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
  // Inter-module Signal External type
  output pwrmgr_pkg::pwr_nvm_t       pwrmgr_pwr_nvm_o,
  input  logic       pwrmgr_strap_i,
  input  logic       pwrmgr_low_power_i,
  input  lc_ctrl_pkg::lc_tx_t       pwrmgr_fetch_en_i,
  output prim_mubi_pkg::mubi4_t       clkmgr_idle_o,
  output rv_core_ibex_pkg::cpu_crash_dump_t       rv_core_ibex_crash_dump_o,
  output rv_core_ibex_pkg::cpu_pwrmgr_t       rv_core_ibex_pwrmgr_o,
  output logic [1:0] pwrmgr_wakeups_o,
  output tlul_pkg::tl_h2d_t       pwrmgr_tl_req_o,
  input  tlul_pkg::tl_d2h_t       pwrmgr_tl_rsp_i,
  output tlul_pkg::tl_h2d_t       rstmgr_tl_req_o,
  input  tlul_pkg::tl_d2h_t       rstmgr_tl_rsp_i,
  output tlul_pkg::tl_h2d_t       clkmgr_tl_req_o,
  input  tlul_pkg::tl_d2h_t       clkmgr_tl_rsp_i,
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
  input  logic [31:0] fpga_info_i,
  input  logic       usbdev_usb_rx_d_i,
  output logic       usbdev_usb_tx_d_o,
  output logic       usbdev_usb_tx_se0_o,
  output logic       usbdev_usb_tx_use_d_se0_o,
  output logic       usbdev_usb_rx_enable_o,
  output logic       usbdev_usb_ref_val_o,
  output logic       usbdev_usb_ref_pulse_o,
  output logic       sck_monitor_o,

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

  // Interrupts from power domain Aon
  input  logic [2:0] intr_vector_pd_aon_i,

  // Outgoing alerts for group englishbreakfast
  output prim_alert_pkg::alert_tx_t [top_englishbreakfast_pkg::NOutgoingAlertsEnglishbreakfastPdMain-1:0] outgoing_alert_englishbreakfast_tx_o,
  input  prim_alert_pkg::alert_rx_t [top_englishbreakfast_pkg::NOutgoingAlertsEnglishbreakfastPdMain-1:0] outgoing_alert_englishbreakfast_rx_i,

  // Clocks from clkmgr in power domain Aon
  input clkmgr_pkg::clkmgr_out_t    clkmgr_clocks_i,
  input clkmgr_pkg::clkmgr_cg_en_t  clkmgr_cg_en_i,

  // Resets from rstmgr in power domain Aon
  input rstmgr_pkg::rstmgr_out_t    rstmgr_resets_i,
  input rstmgr_pkg::rstmgr_rst_en_t rstmgr_rst_en_i,

  // Manual DFT signals
  input                        scan_rst_ni, // reset used for test mode
  input                        scan_en_i,
  input prim_mubi_pkg::mubi4_t scanmode_i   // lc_ctrl_pkg::On for Scan
);

  import top_englishbreakfast_pkg::*;
  // Compile-time random constants
  import top_englishbreakfast_rnd_cnst_pkg::*;

  // Local Parameters
  // local parameters for spi_host0
  localparam int SpiHost0NumCS = 1;
  // local parameters for sram_ctrl_main
  localparam int SramCtrlMainOutstanding = 2;
  // local parameters for rom_ctrl
  localparam bit RomCtrlFlopToKmac = 1'b0;
  // local parameters for rv_core_ibex
  localparam bit RvCoreIbexInstructionPipeline = 1'b0;

  // Signals
  logic [37:0] mio_p2d;
  logic [34:0] mio_d2p;
  logic [34:0] mio_en_d2p;
  logic [13:0] dio_p2d;
  logic [13:0] dio_d2p;
  logic [13:0] dio_en_d2p;
  // uart0
  logic        cio_uart0_rx_p2d;
  logic        cio_uart0_tx_d2p;
  logic        cio_uart0_tx_en_d2p;
  // uart1
  logic        cio_uart1_rx_p2d;
  logic        cio_uart1_tx_d2p;
  logic        cio_uart1_tx_en_d2p;
  // gpio
  logic [31:0] cio_gpio_gpio_p2d;
  logic [31:0] cio_gpio_gpio_d2p;
  logic [31:0] cio_gpio_gpio_en_d2p;
  // spi_device
  logic        cio_spi_device_sck_p2d;
  logic        cio_spi_device_csb_p2d;
  logic        cio_spi_device_tpm_csb_p2d;
  logic [3:0]  cio_spi_device_sd_p2d;
  logic [3:0]  cio_spi_device_sd_d2p;
  logic [3:0]  cio_spi_device_sd_en_d2p;
  // spi_host0
  logic [3:0]  cio_spi_host0_sd_p2d;
  logic        cio_spi_host0_sck_d2p;
  logic        cio_spi_host0_sck_en_d2p;
  logic        cio_spi_host0_csb_d2p;
  logic        cio_spi_host0_csb_en_d2p;
  logic [3:0]  cio_spi_host0_sd_d2p;
  logic [3:0]  cio_spi_host0_sd_en_d2p;
  // rv_timer
  // usbdev
  logic        cio_usbdev_sense_p2d;
  logic        cio_usbdev_usb_dp_p2d;
  logic        cio_usbdev_usb_dn_p2d;
  logic        cio_usbdev_usb_dp_d2p;
  logic        cio_usbdev_usb_dp_en_d2p;
  logic        cio_usbdev_usb_dn_d2p;
  logic        cio_usbdev_usb_dn_en_d2p;
  // pinmux
  // flash_ctrl
  logic        cio_flash_ctrl_tck_p2d;
  logic        cio_flash_ctrl_tms_p2d;
  logic        cio_flash_ctrl_tdi_p2d;
  logic        cio_flash_ctrl_tdo_d2p;
  logic        cio_flash_ctrl_tdo_en_d2p;
  // rv_plic
  // aes
  // sram_ctrl_main
  // rom_ctrl
  // rv_core_ibex


  logic [87:0] intr_vector;
  // Interrupt source list
  logic intr_uart0_tx_watermark;
  logic intr_uart0_rx_watermark;
  logic intr_uart0_tx_done;
  logic intr_uart0_rx_overflow;
  logic intr_uart0_rx_frame_err;
  logic intr_uart0_rx_break_err;
  logic intr_uart0_rx_timeout;
  logic intr_uart0_rx_parity_err;
  logic intr_uart0_tx_empty;
  logic intr_uart1_tx_watermark;
  logic intr_uart1_rx_watermark;
  logic intr_uart1_tx_done;
  logic intr_uart1_rx_overflow;
  logic intr_uart1_rx_frame_err;
  logic intr_uart1_rx_break_err;
  logic intr_uart1_rx_timeout;
  logic intr_uart1_rx_parity_err;
  logic intr_uart1_tx_empty;
  logic [31:0] intr_gpio_gpio;
  logic intr_spi_device_upload_cmdfifo_not_empty;
  logic intr_spi_device_upload_payload_not_empty;
  logic intr_spi_device_upload_payload_overflow;
  logic intr_spi_device_readbuf_watermark;
  logic intr_spi_device_readbuf_flip;
  logic intr_spi_device_tpm_header_not_empty;
  logic intr_spi_device_tpm_rdfifo_cmd_end;
  logic intr_spi_device_tpm_rdfifo_drop;
  logic intr_spi_host0_error;
  logic intr_spi_host0_spi_event;
  logic intr_rv_timer_timer_expired_hart0_timer0;
  logic intr_usbdev_pkt_received;
  logic intr_usbdev_pkt_sent;
  logic intr_usbdev_disconnected;
  logic intr_usbdev_host_lost;
  logic intr_usbdev_link_reset;
  logic intr_usbdev_link_suspend;
  logic intr_usbdev_link_resume;
  logic intr_usbdev_av_out_empty;
  logic intr_usbdev_rx_full;
  logic intr_usbdev_av_overflow;
  logic intr_usbdev_link_in_err;
  logic intr_usbdev_rx_crc_err;
  logic intr_usbdev_rx_pid_err;
  logic intr_usbdev_rx_bitstuff_err;
  logic intr_usbdev_frame;
  logic intr_usbdev_powered;
  logic intr_usbdev_link_out_err;
  logic intr_usbdev_av_setup_empty;
  logic intr_flash_ctrl_prog_empty;
  logic intr_flash_ctrl_prog_lvl;
  logic intr_flash_ctrl_rd_full;
  logic intr_flash_ctrl_rd_lvl;
  logic intr_flash_ctrl_op_done;
  logic intr_flash_ctrl_corr_err;


  // Define inter-module signals
  logic       usbdev_usb_dp_pullup;
  logic       usbdev_usb_dn_pullup;
  logic       usbdev_usb_aon_suspend_req;
  logic       usbdev_usb_aon_wake_ack;
  logic       usbdev_usb_aon_bus_reset;
  logic       usbdev_usb_aon_sense_lost;
  logic       pinmux_usbdev_wake_detect_active;
  logic       rv_plic_msip;
  logic       rv_plic_irq;
  spi_device_pkg::passthrough_req_t       spi_device_passthrough_req;
  spi_device_pkg::passthrough_rsp_t       spi_device_passthrough_rsp;
  tlul_pkg::tl_h2d_t       main_tl_rv_core_ibex__corei_req;
  tlul_pkg::tl_d2h_t       main_tl_rv_core_ibex__corei_rsp;
  tlul_pkg::tl_h2d_t       main_tl_rv_core_ibex__cored_req;
  tlul_pkg::tl_d2h_t       main_tl_rv_core_ibex__cored_rsp;
  tlul_pkg::tl_h2d_t       rom_ctrl_rom_tl_req;
  tlul_pkg::tl_d2h_t       rom_ctrl_rom_tl_rsp;
  tlul_pkg::tl_h2d_t       rom_ctrl_regs_tl_req;
  tlul_pkg::tl_d2h_t       rom_ctrl_regs_tl_rsp;
  tlul_pkg::tl_h2d_t       main_tl_peri_req;
  tlul_pkg::tl_d2h_t       main_tl_peri_rsp;
  tlul_pkg::tl_h2d_t       flash_ctrl_core_tl_req;
  tlul_pkg::tl_d2h_t       flash_ctrl_core_tl_rsp;
  tlul_pkg::tl_h2d_t       flash_ctrl_prim_tl_req;
  tlul_pkg::tl_d2h_t       flash_ctrl_prim_tl_rsp;
  tlul_pkg::tl_h2d_t       flash_ctrl_mem_tl_req;
  tlul_pkg::tl_d2h_t       flash_ctrl_mem_tl_rsp;
  tlul_pkg::tl_h2d_t       aes_tl_req;
  tlul_pkg::tl_d2h_t       aes_tl_rsp;
  tlul_pkg::tl_h2d_t       rv_plic_tl_req;
  tlul_pkg::tl_d2h_t       rv_plic_tl_rsp;
  tlul_pkg::tl_h2d_t       rv_core_ibex_cfg_tl_d_req;
  tlul_pkg::tl_d2h_t       rv_core_ibex_cfg_tl_d_rsp;
  tlul_pkg::tl_h2d_t       sram_ctrl_main_regs_tl_req;
  tlul_pkg::tl_d2h_t       sram_ctrl_main_regs_tl_rsp;
  tlul_pkg::tl_h2d_t       sram_ctrl_main_ram_tl_req;
  tlul_pkg::tl_d2h_t       sram_ctrl_main_ram_tl_rsp;
  tlul_pkg::tl_h2d_t       uart0_tl_req;
  tlul_pkg::tl_d2h_t       uart0_tl_rsp;
  tlul_pkg::tl_h2d_t       uart1_tl_req;
  tlul_pkg::tl_d2h_t       uart1_tl_rsp;
  tlul_pkg::tl_h2d_t       gpio_tl_req;
  tlul_pkg::tl_d2h_t       gpio_tl_rsp;
  tlul_pkg::tl_h2d_t       spi_device_tl_req;
  tlul_pkg::tl_d2h_t       spi_device_tl_rsp;
  tlul_pkg::tl_h2d_t       spi_host0_tl_req;
  tlul_pkg::tl_d2h_t       spi_host0_tl_rsp;
  tlul_pkg::tl_h2d_t       rv_timer_tl_req;
  tlul_pkg::tl_d2h_t       rv_timer_tl_rsp;
  tlul_pkg::tl_h2d_t       usbdev_tl_req;
  tlul_pkg::tl_d2h_t       usbdev_tl_rsp;
  tlul_pkg::tl_h2d_t       pinmux_tl_req;
  tlul_pkg::tl_d2h_t       pinmux_tl_rsp;
  logic       rv_core_ibex_irq_timer;
  logic [31:0] rv_core_ibex_hart_id;
  logic [31:0] rv_core_ibex_boot_addr;
  jtag_pkg::jtag_req_t       pinmux_dft_jtag_req;
  jtag_pkg::jtag_rsp_t       pinmux_dft_jtag_rsp;

  // Create mixed connections to ports



  // Ibex-specific assignments
  // TODO: This should be further automated in the future.
  assign rv_core_ibex_irq_timer = intr_rv_timer_timer_expired_hart0_timer0;
  assign rv_core_ibex_hart_id = '0;

  assign rv_core_ibex_boot_addr = tl_main_pkg::ADDR_SPACE_ROM_CTRL__ROM;

  // Struct breakout module tool-inserted DFT TAP signals
  pinmux_jtag_breakout u_dft_tap_breakout (
    .req_i    (pinmux_dft_jtag_req),
    .rsp_o    (pinmux_dft_jtag_rsp),
    .tck_o    (),
    .trst_no  (),
    .tms_o    (),
    .tdi_o    (),
    .tdo_i    (1'b0),
    .tdo_oe_i (1'b0)
  );

// Tie off unused clock- and reset enables
//VCS coverage off
// pragma coverage off
  prim_mubi_pkg::mubi4_t [20:0] unused_cg_en;
  prim_mubi_pkg::mubi4_t [33:0] unused_rst_en;

  assign unused_cg_en[0] = clkmgr_cg_en_i.aon_peri;
  assign unused_cg_en[1] = clkmgr_cg_en_i.aon_powerup;
  assign unused_cg_en[2] = clkmgr_cg_en_i.aon_secure;
  assign unused_cg_en[3] = clkmgr_cg_en_i.aon_timers;
  assign unused_cg_en[4] = clkmgr_cg_en_i.io_div2_peri;
  assign unused_cg_en[5] = clkmgr_cg_en_i.io_div2_powerup;
  assign unused_cg_en[6] = clkmgr_cg_en_i.io_div4_infra;
  assign unused_cg_en[7] = clkmgr_cg_en_i.io_div4_peri;
  assign unused_cg_en[8] = clkmgr_cg_en_i.io_div4_powerup;
  assign unused_cg_en[9] = clkmgr_cg_en_i.io_div4_secure;
  assign unused_cg_en[10] = clkmgr_cg_en_i.io_div4_timers;
  assign unused_cg_en[11] = clkmgr_cg_en_i.io_infra;
  assign unused_cg_en[12] = clkmgr_cg_en_i.io_peri;
  assign unused_cg_en[13] = clkmgr_cg_en_i.io_powerup;
  assign unused_cg_en[14] = clkmgr_cg_en_i.main_aes;
  assign unused_cg_en[15] = clkmgr_cg_en_i.main_infra;
  assign unused_cg_en[16] = clkmgr_cg_en_i.main_powerup;
  assign unused_cg_en[17] = clkmgr_cg_en_i.main_secure;
  assign unused_cg_en[18] = clkmgr_cg_en_i.usb_infra;
  assign unused_cg_en[19] = clkmgr_cg_en_i.usb_peri;
  assign unused_cg_en[20] = clkmgr_cg_en_i.usb_powerup;

  assign unused_rst_en[0] = rstmgr_rst_en_i.lc[rstmgr_pkg::DomainAonSel];
  assign unused_rst_en[1] = rstmgr_rst_en_i.lc[rstmgr_pkg::DomainMainSel];
  assign unused_rst_en[2] = rstmgr_rst_en_i.lc_io_div4[rstmgr_pkg::DomainAonSel];
  assign unused_rst_en[3] = rstmgr_rst_en_i.lc_io_div4[rstmgr_pkg::DomainMainSel];
  assign unused_rst_en[4] = rstmgr_rst_en_i.lc_shadowed[rstmgr_pkg::DomainAonSel];
  assign unused_rst_en[5] = rstmgr_rst_en_i.lc_shadowed[rstmgr_pkg::DomainMainSel];
  assign unused_rst_en[6] = rstmgr_rst_en_i.por[rstmgr_pkg::DomainAonSel];
  assign unused_rst_en[7] = rstmgr_rst_en_i.por[rstmgr_pkg::DomainMainSel];
  assign unused_rst_en[8] = rstmgr_rst_en_i.por_aon[rstmgr_pkg::DomainAonSel];
  assign unused_rst_en[9] = rstmgr_rst_en_i.por_aon[rstmgr_pkg::DomainMainSel];
  assign unused_rst_en[10] = rstmgr_rst_en_i.por_io[rstmgr_pkg::DomainAonSel];
  assign unused_rst_en[11] = rstmgr_rst_en_i.por_io[rstmgr_pkg::DomainMainSel];
  assign unused_rst_en[12] = rstmgr_rst_en_i.por_io_div2[rstmgr_pkg::DomainAonSel];
  assign unused_rst_en[13] = rstmgr_rst_en_i.por_io_div2[rstmgr_pkg::DomainMainSel];
  assign unused_rst_en[14] = rstmgr_rst_en_i.por_io_div4[rstmgr_pkg::DomainAonSel];
  assign unused_rst_en[15] = rstmgr_rst_en_i.por_io_div4[rstmgr_pkg::DomainMainSel];
  assign unused_rst_en[16] = rstmgr_rst_en_i.por_io_div4_shadowed[rstmgr_pkg::DomainAonSel];
  assign unused_rst_en[17] = rstmgr_rst_en_i.por_io_div4_shadowed[rstmgr_pkg::DomainMainSel];
  assign unused_rst_en[18] = rstmgr_rst_en_i.por_usb[rstmgr_pkg::DomainAonSel];
  assign unused_rst_en[19] = rstmgr_rst_en_i.por_usb[rstmgr_pkg::DomainMainSel];
  assign unused_rst_en[20] = rstmgr_rst_en_i.spi_device[rstmgr_pkg::DomainAonSel];
  assign unused_rst_en[21] = rstmgr_rst_en_i.spi_device[rstmgr_pkg::DomainMainSel];
  assign unused_rst_en[22] = rstmgr_rst_en_i.spi_host0[rstmgr_pkg::DomainAonSel];
  assign unused_rst_en[23] = rstmgr_rst_en_i.spi_host0[rstmgr_pkg::DomainMainSel];
  assign unused_rst_en[24] = rstmgr_rst_en_i.sys[rstmgr_pkg::DomainAonSel];
  assign unused_rst_en[25] = rstmgr_rst_en_i.sys[rstmgr_pkg::DomainMainSel];
  assign unused_rst_en[26] = rstmgr_rst_en_i.sys_aon[rstmgr_pkg::DomainAonSel];
  assign unused_rst_en[27] = rstmgr_rst_en_i.sys_aon[rstmgr_pkg::DomainMainSel];
  assign unused_rst_en[28] = rstmgr_rst_en_i.sys_io_div4[rstmgr_pkg::DomainAonSel];
  assign unused_rst_en[29] = rstmgr_rst_en_i.sys_io_div4[rstmgr_pkg::DomainMainSel];
  assign unused_rst_en[30] = rstmgr_rst_en_i.sys_shadowed[rstmgr_pkg::DomainAonSel];
  assign unused_rst_en[31] = rstmgr_rst_en_i.sys_shadowed[rstmgr_pkg::DomainMainSel];
  assign unused_rst_en[32] = rstmgr_rst_en_i.usb[rstmgr_pkg::DomainAonSel];
  assign unused_rst_en[33] = rstmgr_rst_en_i.usb[rstmgr_pkg::DomainMainSel];
// pragma coverage on
//VCS coverage on

// Tie off unused clocks and resets
//VCS coverage off
// pragma coverage off
  logic [7:0] unused_clocks;
  assign unused_clocks[0] = clkmgr_clocks_i.clk_aon_secure;
  assign unused_clocks[1] = clkmgr_clocks_i.clk_aon_timers;
  assign unused_clocks[2] = clkmgr_clocks_i.clk_io_div2_powerup;
  assign unused_clocks[3] = clkmgr_clocks_i.clk_io_infra;
  assign unused_clocks[4] = clkmgr_clocks_i.clk_io_powerup;
  assign unused_clocks[5] = clkmgr_clocks_i.clk_main_powerup;
  assign unused_clocks[6] = clkmgr_clocks_i.clk_usb_infra;
  assign unused_clocks[7] = clkmgr_clocks_i.clk_usb_powerup;

  logic [20:0] unused_resets;
  assign unused_resets[0] = rstmgr_resets_i.rst_lc_n[rstmgr_pkg::DomainAonSel];
  assign unused_resets[1] = rstmgr_resets_i.rst_lc_shadowed_n[rstmgr_pkg::DomainAonSel];
  assign unused_resets[2] = rstmgr_resets_i.rst_por_aon_n[rstmgr_pkg::DomainAonSel];
  assign unused_resets[3] = rstmgr_resets_i.rst_por_aon_n[rstmgr_pkg::DomainMainSel];
  assign unused_resets[4] = rstmgr_resets_i.rst_por_io_div2_n[rstmgr_pkg::DomainAonSel];
  assign unused_resets[5] = rstmgr_resets_i.rst_por_io_div2_n[rstmgr_pkg::DomainMainSel];
  assign unused_resets[6] = rstmgr_resets_i.rst_por_io_div4_n[rstmgr_pkg::DomainAonSel];
  assign unused_resets[7] = rstmgr_resets_i.rst_por_io_div4_n[rstmgr_pkg::DomainMainSel];
  assign unused_resets[8] = rstmgr_resets_i.rst_por_io_div4_shadowed_n[rstmgr_pkg::DomainAonSel];
  assign unused_resets[9] = rstmgr_resets_i.rst_por_io_div4_shadowed_n[rstmgr_pkg::DomainMainSel];
  assign unused_resets[10] = rstmgr_resets_i.rst_por_io_n[rstmgr_pkg::DomainAonSel];
  assign unused_resets[11] = rstmgr_resets_i.rst_por_io_n[rstmgr_pkg::DomainMainSel];
  assign unused_resets[12] = rstmgr_resets_i.rst_por_n[rstmgr_pkg::DomainAonSel];
  assign unused_resets[13] = rstmgr_resets_i.rst_por_n[rstmgr_pkg::DomainMainSel];
  assign unused_resets[14] = rstmgr_resets_i.rst_por_usb_n[rstmgr_pkg::DomainAonSel];
  assign unused_resets[15] = rstmgr_resets_i.rst_por_usb_n[rstmgr_pkg::DomainMainSel];
  assign unused_resets[16] = rstmgr_resets_i.rst_spi_device_n[rstmgr_pkg::DomainAonSel];
  assign unused_resets[17] = rstmgr_resets_i.rst_spi_host0_n[rstmgr_pkg::DomainAonSel];
  assign unused_resets[18] = rstmgr_resets_i.rst_sys_n[rstmgr_pkg::DomainAonSel];
  assign unused_resets[19] = rstmgr_resets_i.rst_sys_shadowed_n[rstmgr_pkg::DomainAonSel];
  assign unused_resets[20] = rstmgr_resets_i.rst_usb_n[rstmgr_pkg::DomainAonSel];
// pragma coverage on
//VCS coverage on

  // Instantiation of IPs
  uart #(
    .AlertAsyncOn(AsyncOnOutgoingAlertEnglishbreakfast[0]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles)
  ) u_uart0 (
    // Clock and reset connections
    .clk_i(clkmgr_clocks_i.clk_io_div4_peri),
    .rst_ni(rstmgr_resets_i.rst_lc_io_div4_n[rstmgr_pkg::DomainMainSel]),

    // Interrupts
    .intr_tx_watermark_o (intr_uart0_tx_watermark),
    .intr_rx_watermark_o (intr_uart0_rx_watermark),
    .intr_tx_done_o      (intr_uart0_tx_done),
    .intr_rx_overflow_o  (intr_uart0_rx_overflow),
    .intr_rx_frame_err_o (intr_uart0_rx_frame_err),
    .intr_rx_break_err_o (intr_uart0_rx_break_err),
    .intr_rx_timeout_o   (intr_uart0_rx_timeout),
    .intr_rx_parity_err_o(intr_uart0_rx_parity_err),
    .intr_tx_empty_o     (intr_uart0_tx_empty),

    // External alert group "englishbreakfast" [0]: fatal_fault
    .alert_tx_o(outgoing_alert_englishbreakfast_tx_o[0]),
    .alert_rx_i(outgoing_alert_englishbreakfast_rx_i[0]),

    // CIO inputs
    .cio_rx_i   (cio_uart0_rx_p2d),

    // CIO outputs
    .cio_tx_o   (cio_uart0_tx_d2p),
    .cio_tx_en_o(cio_uart0_tx_en_d2p),

    // Inter-module signals
    .lsio_trigger_o(),
    .racl_policies_i(top_racl_pkg::RACL_POLICY_VEC_DEFAULT),
    .racl_error_o(),
    .tl_i(uart0_tl_req),
    .tl_o(uart0_tl_rsp)
  );

  uart #(
    .AlertAsyncOn(AsyncOnOutgoingAlertEnglishbreakfast[1]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles)
  ) u_uart1 (
    // Clock and reset connections
    .clk_i(clkmgr_clocks_i.clk_io_div4_peri),
    .rst_ni(rstmgr_resets_i.rst_lc_io_div4_n[rstmgr_pkg::DomainMainSel]),

    // Interrupts
    .intr_tx_watermark_o (intr_uart1_tx_watermark),
    .intr_rx_watermark_o (intr_uart1_rx_watermark),
    .intr_tx_done_o      (intr_uart1_tx_done),
    .intr_rx_overflow_o  (intr_uart1_rx_overflow),
    .intr_rx_frame_err_o (intr_uart1_rx_frame_err),
    .intr_rx_break_err_o (intr_uart1_rx_break_err),
    .intr_rx_timeout_o   (intr_uart1_rx_timeout),
    .intr_rx_parity_err_o(intr_uart1_rx_parity_err),
    .intr_tx_empty_o     (intr_uart1_tx_empty),

    // External alert group "englishbreakfast" [1]: fatal_fault
    .alert_tx_o(outgoing_alert_englishbreakfast_tx_o[1]),
    .alert_rx_i(outgoing_alert_englishbreakfast_rx_i[1]),

    // CIO inputs
    .cio_rx_i   (cio_uart1_rx_p2d),

    // CIO outputs
    .cio_tx_o   (cio_uart1_tx_d2p),
    .cio_tx_en_o(cio_uart1_tx_en_d2p),

    // Inter-module signals
    .lsio_trigger_o(),
    .racl_policies_i(top_racl_pkg::RACL_POLICY_VEC_DEFAULT),
    .racl_error_o(),
    .tl_i(uart1_tl_req),
    .tl_o(uart1_tl_rsp)
  );

  gpio #(
    .AlertAsyncOn(AsyncOnOutgoingAlertEnglishbreakfast[2]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles),
    .GpioAsyncOn(GpioGpioAsyncOn),
    .GpioAsHwStrapsEn(GpioGpioAsHwStrapsEn)
  ) u_gpio (
    // Clock and reset connections
    .clk_i(clkmgr_clocks_i.clk_io_div4_peri),
    .rst_ni(rstmgr_resets_i.rst_sys_io_div4_n[rstmgr_pkg::DomainMainSel]),

    // Interrupts
    .intr_gpio_o(intr_gpio_gpio),

    // External alert group "englishbreakfast" [2]: fatal_fault
    .alert_tx_o(outgoing_alert_englishbreakfast_tx_o[2]),
    .alert_rx_i(outgoing_alert_englishbreakfast_rx_i[2]),

    // CIO inputs
    .cio_gpio_i   (cio_gpio_gpio_p2d),

    // CIO outputs
    .cio_gpio_o   (cio_gpio_gpio_d2p),
    .cio_gpio_en_o(cio_gpio_gpio_en_d2p),

    // Inter-module signals
    .strap_en_i(1'b0),
    .sampled_straps_o(),
    .racl_policies_i(top_racl_pkg::RACL_POLICY_VEC_DEFAULT),
    .racl_error_o(),
    .tl_i(gpio_tl_req),
    .tl_o(gpio_tl_rsp)
  );

  spi_device #(
    .AlertAsyncOn(AsyncOnOutgoingAlertEnglishbreakfast[3]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles),
    .SramType(SpiDeviceSramType)
  ) u_spi_device (
    // Clock and reset connections
    .clk_i(clkmgr_clocks_i.clk_io_div4_peri),
    .scan_clk_i(clkmgr_clocks_i.clk_io_div2_peri),
    .rst_ni(rstmgr_resets_i.rst_spi_device_n[rstmgr_pkg::DomainMainSel]),

    // DFT/scan connections
    .scanmode_i,
    .scan_rst_ni,

    // Interrupts
    .intr_upload_cmdfifo_not_empty_o(intr_spi_device_upload_cmdfifo_not_empty),
    .intr_upload_payload_not_empty_o(intr_spi_device_upload_payload_not_empty),
    .intr_upload_payload_overflow_o (intr_spi_device_upload_payload_overflow),
    .intr_readbuf_watermark_o       (intr_spi_device_readbuf_watermark),
    .intr_readbuf_flip_o            (intr_spi_device_readbuf_flip),
    .intr_tpm_header_not_empty_o    (intr_spi_device_tpm_header_not_empty),
    .intr_tpm_rdfifo_cmd_end_o      (intr_spi_device_tpm_rdfifo_cmd_end),
    .intr_tpm_rdfifo_drop_o         (intr_spi_device_tpm_rdfifo_drop),

    // External alert group "englishbreakfast" [3]: fatal_fault
    .alert_tx_o(outgoing_alert_englishbreakfast_tx_o[3]),
    .alert_rx_i(outgoing_alert_englishbreakfast_rx_i[3]),

    // CIO inputs
    .cio_sck_i       (cio_spi_device_sck_p2d),
    .cio_csb_i       (cio_spi_device_csb_p2d),
    .cio_tpm_csb_i   (cio_spi_device_tpm_csb_p2d),
    .cio_sd_i        (cio_spi_device_sd_p2d),

    // CIO outputs
    .cio_sd_o        (cio_spi_device_sd_d2p),
    .cio_sd_en_o     (cio_spi_device_sd_en_d2p),

    // Inter-module signals
    .ram_cfg_sys2spi_i(prim_ram_1r1w_pkg::RAM_1R1W_CFG_REQ_DEFAULT),
    .ram_cfg_sys2spi_o(),
    .ram_cfg_spi2sys_i(prim_ram_1r1w_pkg::RAM_1R1W_CFG_REQ_DEFAULT),
    .ram_cfg_spi2sys_o(),
    .passthrough_o(spi_device_passthrough_req),
    .passthrough_i(spi_device_passthrough_rsp),
    .mbist_en_i('0),
    .sck_monitor_o(sck_monitor_o),
    .racl_policies_i(top_racl_pkg::RACL_POLICY_VEC_DEFAULT),
    .racl_error_o(),
    .tl_i(spi_device_tl_req),
    .tl_o(spi_device_tl_rsp)
  );

  spi_host #(
    .AlertAsyncOn(AsyncOnOutgoingAlertEnglishbreakfast[4]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles),
    .NumCS(SpiHost0NumCS)
  ) u_spi_host0 (
    // Clock and reset connections
    .clk_i(clkmgr_clocks_i.clk_io_peri),
    .rst_ni(rstmgr_resets_i.rst_spi_host0_n[rstmgr_pkg::DomainMainSel]),

    // Interrupts
    .intr_error_o    (intr_spi_host0_error),
    .intr_spi_event_o(intr_spi_host0_spi_event),

    // External alert group "englishbreakfast" [4]: fatal_fault
    .alert_tx_o(outgoing_alert_englishbreakfast_tx_o[4]),
    .alert_rx_i(outgoing_alert_englishbreakfast_rx_i[4]),

    // CIO inputs
    .cio_sd_i    (cio_spi_host0_sd_p2d),

    // CIO outputs
    .cio_sck_o   (cio_spi_host0_sck_d2p),
    .cio_sck_en_o(cio_spi_host0_sck_en_d2p),
    .cio_csb_o   (cio_spi_host0_csb_d2p),
    .cio_csb_en_o(cio_spi_host0_csb_en_d2p),
    .cio_sd_o    (cio_spi_host0_sd_d2p),
    .cio_sd_en_o (cio_spi_host0_sd_en_d2p),

    // Inter-module signals
    .passthrough_i(spi_device_passthrough_req),
    .passthrough_o(spi_device_passthrough_rsp),
    .lsio_trigger_o(),
    .racl_policies_i(top_racl_pkg::RACL_POLICY_VEC_DEFAULT),
    .racl_error_o(),
    .tl_i(spi_host0_tl_req),
    .tl_o(spi_host0_tl_rsp)
  );

  rv_timer #(
    .AlertAsyncOn(AsyncOnOutgoingAlertEnglishbreakfast[5]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles)
  ) u_rv_timer (
    // Clock and reset connections
    .clk_i(clkmgr_clocks_i.clk_io_div4_timers),
    .rst_ni(rstmgr_resets_i.rst_sys_io_div4_n[rstmgr_pkg::DomainMainSel]),

    // Interrupts
    .intr_timer_expired_hart0_timer0_o(intr_rv_timer_timer_expired_hart0_timer0),

    // External alert group "englishbreakfast" [5]: fatal_fault
    .alert_tx_o(outgoing_alert_englishbreakfast_tx_o[5]),
    .alert_rx_i(outgoing_alert_englishbreakfast_rx_i[5]),

    // Inter-module signals
    .racl_policies_i(top_racl_pkg::RACL_POLICY_VEC_DEFAULT),
    .racl_error_o(),
    .tl_i(rv_timer_tl_req),
    .tl_o(rv_timer_tl_rsp)
  );

  usbdev #(
    .AlertAsyncOn(AsyncOnOutgoingAlertEnglishbreakfast[6]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles),
    .Stub(UsbdevStub),
    .RcvrWakeTimeUs(UsbdevRcvrWakeTimeUs)
  ) u_usbdev (
    // Clock and reset connections
    .clk_i(clkmgr_clocks_i.clk_usb_peri),
    .clk_aon_i(clkmgr_clocks_i.clk_aon_peri),
    .rst_ni(rstmgr_resets_i.rst_usb_n[rstmgr_pkg::DomainMainSel]),
    .rst_aon_ni(rstmgr_resets_i.rst_sys_aon_n[rstmgr_pkg::DomainMainSel]),

    // Interrupts
    .intr_pkt_received_o   (intr_usbdev_pkt_received),
    .intr_pkt_sent_o       (intr_usbdev_pkt_sent),
    .intr_disconnected_o   (intr_usbdev_disconnected),
    .intr_host_lost_o      (intr_usbdev_host_lost),
    .intr_link_reset_o     (intr_usbdev_link_reset),
    .intr_link_suspend_o   (intr_usbdev_link_suspend),
    .intr_link_resume_o    (intr_usbdev_link_resume),
    .intr_av_out_empty_o   (intr_usbdev_av_out_empty),
    .intr_rx_full_o        (intr_usbdev_rx_full),
    .intr_av_overflow_o    (intr_usbdev_av_overflow),
    .intr_link_in_err_o    (intr_usbdev_link_in_err),
    .intr_rx_crc_err_o     (intr_usbdev_rx_crc_err),
    .intr_rx_pid_err_o     (intr_usbdev_rx_pid_err),
    .intr_rx_bitstuff_err_o(intr_usbdev_rx_bitstuff_err),
    .intr_frame_o          (intr_usbdev_frame),
    .intr_powered_o        (intr_usbdev_powered),
    .intr_link_out_err_o   (intr_usbdev_link_out_err),
    .intr_av_setup_empty_o (intr_usbdev_av_setup_empty),

    // External alert group "englishbreakfast" [6]: fatal_fault
    .alert_tx_o(outgoing_alert_englishbreakfast_tx_o[6]),
    .alert_rx_i(outgoing_alert_englishbreakfast_rx_i[6]),

    // CIO inputs
    .cio_sense_i    (cio_usbdev_sense_p2d),
    .cio_usb_dp_i   (cio_usbdev_usb_dp_p2d),
    .cio_usb_dn_i   (cio_usbdev_usb_dn_p2d),

    // CIO outputs
    .cio_usb_dp_o   (cio_usbdev_usb_dp_d2p),
    .cio_usb_dp_en_o(cio_usbdev_usb_dp_en_d2p),
    .cio_usb_dn_o   (cio_usbdev_usb_dn_d2p),
    .cio_usb_dn_en_o(cio_usbdev_usb_dn_en_d2p),

    // Inter-module signals
    .usb_rx_d_i(usbdev_usb_rx_d_i),
    .usb_tx_d_o(usbdev_usb_tx_d_o),
    .usb_tx_se0_o(usbdev_usb_tx_se0_o),
    .usb_tx_use_d_se0_o(usbdev_usb_tx_use_d_se0_o),
    .usb_dp_pullup_o(usbdev_usb_dp_pullup),
    .usb_dn_pullup_o(usbdev_usb_dn_pullup),
    .usb_rx_enable_o(usbdev_usb_rx_enable_o),
    .usb_ref_val_o(usbdev_usb_ref_val_o),
    .usb_ref_pulse_o(usbdev_usb_ref_pulse_o),
    .usb_aon_suspend_req_o(usbdev_usb_aon_suspend_req),
    .usb_aon_wake_ack_o(usbdev_usb_aon_wake_ack),
    .usb_aon_bus_reset_i(usbdev_usb_aon_bus_reset),
    .usb_aon_sense_lost_i(usbdev_usb_aon_sense_lost),
    .usb_aon_bus_not_idle_i('0),
    .usb_aon_wake_detect_active_i(pinmux_usbdev_wake_detect_active),
    .ram_cfg_i(prim_ram_1p_pkg::RAM_1P_CFG_REQ_DEFAULT),
    .ram_cfg_o(),
    .tl_i(usbdev_tl_req),
    .tl_o(usbdev_tl_rsp)
  );

  pinmux #(
    .AlertAsyncOn(AsyncOnOutgoingAlertEnglishbreakfast[12]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles),
    .SecVolatileRawUnlockEn(SecPinmuxVolatileRawUnlockEn),
    .TargetCfg(PinmuxTargetCfg)
  ) u_pinmux (
    // Clock and reset connections
    .clk_i(clkmgr_clocks_i.clk_io_div4_powerup),
    .clk_aon_i(clkmgr_clocks_i.clk_aon_powerup),
    .rst_ni(rstmgr_resets_i.rst_lc_io_div4_n[rstmgr_pkg::DomainAonSel]),
    .rst_aon_ni(rstmgr_resets_i.rst_sys_aon_n[rstmgr_pkg::DomainAonSel]),
    .rst_sys_ni(rstmgr_resets_i.rst_sys_io_div4_n[rstmgr_pkg::DomainAonSel]),

    // DFT/scan connections
    .scanmode_i,

    // External alert group "englishbreakfast" [12]: fatal_fault
    .alert_tx_o(outgoing_alert_englishbreakfast_tx_o[7]),
    .alert_rx_i(outgoing_alert_englishbreakfast_rx_i[7]),

    // Inter-module signals
    .lc_hw_debug_clr_i(lc_ctrl_pkg::Off),
    .lc_hw_debug_en_i(lc_ctrl_pkg::Off),
    .lc_dft_en_i(lc_ctrl_pkg::Off),
    .lc_escalate_en_i(lc_ctrl_pkg::Off),
    .lc_check_byp_en_i(lc_ctrl_pkg::Off),
    .pinmux_hw_debug_en_o(),
    .lc_jtag_o(),
    .lc_jtag_i(jtag_pkg::JTAG_RSP_DEFAULT),
    .rv_jtag_o(),
    .rv_jtag_i(jtag_pkg::JTAG_RSP_DEFAULT),
    .dft_jtag_o(pinmux_dft_jtag_req),
    .dft_jtag_i(pinmux_dft_jtag_rsp),
    .dft_strap_test_o(dft_strap_test_o),
    .dft_hold_tap_sel_i(dft_hold_tap_sel_i),
    .sleep_en_i(pwrmgr_low_power_i),
    .strap_en_i(pwrmgr_strap_i),
    .strap_en_override_i(1'b0),
    .pin_wkup_req_o(pwrmgr_wakeups_o[0]),
    .usbdev_dppullup_en_i(usbdev_usb_dp_pullup),
    .usbdev_dnpullup_en_i(usbdev_usb_dn_pullup),
    .usb_dppullup_en_o(usb_dp_pullup_en_o),
    .usb_dnpullup_en_o(usb_dn_pullup_en_o),
    .usb_wkup_req_o(pwrmgr_wakeups_o[1]),
    .usbdev_suspend_req_i(usbdev_usb_aon_suspend_req),
    .usbdev_wake_ack_i(usbdev_usb_aon_wake_ack),
    .usbdev_bus_not_idle_o(),
    .usbdev_bus_reset_o(usbdev_usb_aon_bus_reset),
    .usbdev_sense_lost_o(usbdev_usb_aon_sense_lost),
    .usbdev_wake_detect_active_o(pinmux_usbdev_wake_detect_active),
    .tl_i(pinmux_tl_req),
    .tl_o(pinmux_tl_rsp),

    .periph_to_mio_i   (mio_d2p   ),
    .periph_to_mio_oe_i(mio_en_d2p),
    .mio_to_periph_o   (mio_p2d   ),

    .mio_attr_o,
    .mio_out_o,
    .mio_oe_o,
    .mio_in_i,

    .periph_to_dio_i   (dio_d2p   ),
    .periph_to_dio_oe_i(dio_en_d2p),
    .dio_to_periph_o   (dio_p2d   ),

    .dio_attr_o,
    .dio_out_o,
    .dio_oe_o,
    .dio_in_i
  );

  flash_ctrl #(
    .AlertAsyncOn(AsyncOnOutgoingAlertEnglishbreakfast[18:14]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles),
    .RndCnstAddrKey(RndCnstFlashCtrlAddrKey),
    .RndCnstDataKey(RndCnstFlashCtrlDataKey),
    .RndCnstAllSeeds(RndCnstFlashCtrlAllSeeds),
    .RndCnstLfsrSeed(RndCnstFlashCtrlLfsrSeed),
    .RndCnstLfsrPerm(RndCnstFlashCtrlLfsrPerm),
    .SecScrambleEn(SecFlashCtrlScrambleEn),
    .ProgFifoDepth(FlashCtrlProgFifoDepth),
    .RdFifoDepth(FlashCtrlRdFifoDepth)
  ) u_flash_ctrl (
    // Clock and reset connections
    .clk_i(clkmgr_clocks_i.clk_main_infra),
    .clk_otp_i(clkmgr_clocks_i.clk_io_div4_infra),
    .rst_shadowed_ni(rstmgr_resets_i.rst_lc_shadowed_n[rstmgr_pkg::DomainMainSel]),
    .rst_ni(rstmgr_resets_i.rst_lc_n[rstmgr_pkg::DomainMainSel]),
    .rst_otp_ni(rstmgr_resets_i.rst_lc_io_div4_n[rstmgr_pkg::DomainMainSel]),

    // DFT/scan connections
    .scanmode_i,
    .scan_rst_ni,
    .scan_en_i,

    // Interrupts
    .intr_prog_empty_o(intr_flash_ctrl_prog_empty),
    .intr_prog_lvl_o  (intr_flash_ctrl_prog_lvl),
    .intr_rd_full_o   (intr_flash_ctrl_rd_full),
    .intr_rd_lvl_o    (intr_flash_ctrl_rd_lvl),
    .intr_op_done_o   (intr_flash_ctrl_op_done),
    .intr_corr_err_o  (intr_flash_ctrl_corr_err),

    // External alert group "englishbreakfast" [14]: recov_err
    // External alert group "englishbreakfast" [15]: fatal_std_err
    // External alert group "englishbreakfast" [16]: fatal_err
    // External alert group "englishbreakfast" [17]: fatal_prim_flash_alert
    // External alert group "englishbreakfast" [18]: recov_prim_flash_alert
    .alert_tx_o(outgoing_alert_englishbreakfast_tx_o[12:8]),
    .alert_rx_i(outgoing_alert_englishbreakfast_rx_i[12:8]),

    // CIO inputs
    .cio_tck_i   (cio_flash_ctrl_tck_p2d),
    .cio_tms_i   (cio_flash_ctrl_tms_p2d),
    .cio_tdi_i   (cio_flash_ctrl_tdi_p2d),

    // CIO outputs
    .cio_tdo_o   (cio_flash_ctrl_tdo_d2p),
    .cio_tdo_en_o(cio_flash_ctrl_tdo_en_d2p),

    // Inter-module signals
    .otp_o(),
    .otp_i(otp_ctrl_pkg::NVM_OTP_KEY_RSP_DEFAULT),
    .lc_nvm_debug_en_i(lc_ctrl_pkg::LC_TX_DEFAULT),
    .flash_bist_enable_i(flash_bist_enable_i),
    .flash_power_down_h_i(flash_power_down_h_i),
    .flash_power_ready_h_i(flash_power_ready_h_i),
    .flash_test_mode_a_io(),
    .flash_test_voltage_h_io(),
    .lc_creator_seed_sw_rw_en_i(lc_ctrl_pkg::LC_TX_DEFAULT),
    .lc_owner_seed_sw_rw_en_i(lc_ctrl_pkg::LC_TX_DEFAULT),
    .lc_iso_part_sw_rd_en_i(lc_ctrl_pkg::LC_TX_DEFAULT),
    .lc_iso_part_sw_wr_en_i(lc_ctrl_pkg::LC_TX_DEFAULT),
    .lc_seed_hw_rd_en_i(lc_ctrl_pkg::LC_TX_DEFAULT),
    .lc_escalate_en_i(lc_ctrl_pkg::LC_TX_DEFAULT),
    .rma_req_i(lc_ctrl_pkg::LC_TX_DEFAULT),
    .rma_ack_o(),
    .rma_seed_i(lc_ctrl_pkg::LC_NVM_RMA_SEED_DEFAULT),
    .pwrmgr_o(pwrmgr_pwr_nvm_o),
    .keymgr_o(),
    .obs_ctrl_i(obs_ctrl_i),
    .fla_obs_o(flash_obs_o),
    .core_tl_i(flash_ctrl_core_tl_req),
    .core_tl_o(flash_ctrl_core_tl_rsp),
    .prim_tl_i(flash_ctrl_prim_tl_req),
    .prim_tl_o(flash_ctrl_prim_tl_rsp),
    .mem_tl_i(flash_ctrl_mem_tl_req),
    .mem_tl_o(flash_ctrl_mem_tl_rsp)
  );

  rv_plic #(
    .AlertAsyncOn(AsyncOnOutgoingAlertEnglishbreakfast[19]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles)
  ) u_rv_plic (
    // Clock and reset connections
    .clk_i(clkmgr_clocks_i.clk_main_secure),
    .rst_ni(rstmgr_resets_i.rst_sys_n[rstmgr_pkg::DomainMainSel]),

    // External alert group "englishbreakfast" [19]: fatal_fault
    .alert_tx_o(outgoing_alert_englishbreakfast_tx_o[13]),
    .alert_rx_i(outgoing_alert_englishbreakfast_rx_i[13]),

    // Inter-module signals
    .irq_o(rv_plic_irq),
    .irq_id_o(),
    .msip_o(rv_plic_msip),
    .tl_i(rv_plic_tl_req),
    .tl_o(rv_plic_tl_rsp),


    // Interrupt source vector
    .intr_src_i(intr_vector)
  );

  aes #(
    .AlertAsyncOn(AsyncOnOutgoingAlertEnglishbreakfast[21:20]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles),
    .AES192Enable(1'b1),
    .AESGCMEnable(AesAESGCMEnable),
    .SecMasking(SecAesMasking),
    .SecSBoxImpl(SecAesSBoxImpl),
    .SecStartTriggerDelay(SecAesStartTriggerDelay),
    .SecAllowForcingMasks(SecAesAllowForcingMasks),
    .SecSkipPRNGReseeding(SecAesSkipPRNGReseeding),
    .RndCnstClearingLfsrSeed(RndCnstAesClearingLfsrSeed),
    .RndCnstClearingLfsrPerm(RndCnstAesClearingLfsrPerm),
    .RndCnstClearingSharePerm(RndCnstAesClearingSharePerm),
    .RndCnstMaskingLfsrSeed(RndCnstAesMaskingLfsrSeed),
    .RndCnstMaskingLfsrPerm(RndCnstAesMaskingLfsrPerm)
  ) u_aes (
    // Clock and reset connections
    .clk_i(clkmgr_clocks_i.clk_main_aes),
    .clk_edn_i(clkmgr_clocks_i.clk_main_aes),
    .rst_shadowed_ni(rstmgr_resets_i.rst_sys_shadowed_n[rstmgr_pkg::DomainMainSel]),
    .rst_ni(rstmgr_resets_i.rst_sys_n[rstmgr_pkg::DomainMainSel]),
    .rst_edn_ni(rstmgr_resets_i.rst_sys_n[rstmgr_pkg::DomainMainSel]),

    // External alert group "englishbreakfast" [20]: recov_ctrl_update_err
    // External alert group "englishbreakfast" [21]: fatal_fault
    .alert_tx_o(outgoing_alert_englishbreakfast_tx_o[15:14]),
    .alert_rx_i(outgoing_alert_englishbreakfast_rx_i[15:14]),

    // Inter-module signals
    .idle_o(clkmgr_idle_o),
    .output_valid_o(),
    .input_ready_o(),
    .lc_escalate_en_i(lc_ctrl_pkg::Off),
    .edn_o(),
    .edn_i(edn_pkg::EDN_RSP_DEFAULT),
    .keymgr_key_i(keymgr_pkg::HW_KEY_REQ_DEFAULT),
    .tl_i(aes_tl_req),
    .tl_o(aes_tl_rsp)
  );

  sram_ctrl #(
    .AlertAsyncOn(AsyncOnOutgoingAlertEnglishbreakfast[22]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles),
    .RndCnstSramKey(RndCnstSramCtrlMainSramKey),
    .RndCnstSramNonce(RndCnstSramCtrlMainSramNonce),
    .RndCnstLfsrSeed(RndCnstSramCtrlMainLfsrSeed),
    .RndCnstLfsrPerm(RndCnstSramCtrlMainLfsrPerm),
    .MemSizeRam(131072),
    .InstSize(SramCtrlMainInstSize),
    .NumRamInst(SramCtrlMainNumRamInst),
    .InstrExec(SramCtrlMainInstrExec),
    .NumPrinceRoundsHalf(SramCtrlMainNumPrinceRoundsHalf),
    .Outstanding(SramCtrlMainOutstanding),
    .EccCorrection(SramCtrlMainEccCorrection)
  ) u_sram_ctrl_main (
    // Clock and reset connections
    .clk_i(clkmgr_clocks_i.clk_main_secure),
    .clk_otp_i(clkmgr_clocks_i.clk_io_div4_secure),
    .rst_ni(rstmgr_resets_i.rst_sys_n[rstmgr_pkg::DomainMainSel]),
    .rst_otp_ni(rstmgr_resets_i.rst_lc_io_div4_n[rstmgr_pkg::DomainMainSel]),

    // External alert group "englishbreakfast" [22]: fatal_error
    .alert_tx_o(outgoing_alert_englishbreakfast_tx_o[16]),
    .alert_rx_i(outgoing_alert_englishbreakfast_rx_i[16]),

    // RACL policies
    .racl_policy_sel_ranges_ram_i('{top_racl_pkg::RACL_RANGE_T_DEFAULT}),

    // Inter-module signals
    .sram_otp_key_o(),
    .sram_otp_key_i(otp_ctrl_pkg::SRAM_OTP_KEY_RSP_DEFAULT),
    .ram_cfg_i('{default: prim_ram_1p_pkg::RAM_1P_CFG_REQ_DEFAULT}),
    .ram_cfg_o(),
    .lc_escalate_en_i(lc_ctrl_pkg::Off),
    .lc_hw_debug_en_i(lc_ctrl_pkg::Off),
    .otp_en_sram_ifetch_i(prim_mubi_pkg::MuBi8False),
    .racl_policies_i(top_racl_pkg::RACL_POLICY_VEC_DEFAULT),
    .racl_error_o(),
    .sram_rerror_o(),
    .regs_tl_i(sram_ctrl_main_regs_tl_req),
    .regs_tl_o(sram_ctrl_main_regs_tl_rsp),
    .ram_tl_i(sram_ctrl_main_ram_tl_req),
    .ram_tl_o(sram_ctrl_main_ram_tl_rsp)
  );

  rom_ctrl #(
    .AlertAsyncOn(AsyncOnOutgoingAlertEnglishbreakfast[23]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles),
    .BootRomInitFile(RomCtrlBootRomInitFile),
    .FlopToKmac(RomCtrlFlopToKmac),
    .RndCnstScrNonce(RndCnstRomCtrlScrNonce),
    .RndCnstScrKey(RndCnstRomCtrlScrKey),
    .SecDisableScrambling(SecRomCtrlDisableScrambling),
    .MemSizeRom(32768)
  ) u_rom_ctrl (
    // Clock and reset connections
    .clk_i(clkmgr_clocks_i.clk_main_infra),
    .rst_ni(rstmgr_resets_i.rst_sys_n[rstmgr_pkg::DomainMainSel]),

    // External alert group "englishbreakfast" [23]: fatal
    .alert_tx_o(outgoing_alert_englishbreakfast_tx_o[17]),
    .alert_rx_i(outgoing_alert_englishbreakfast_rx_i[17]),

    // Inter-module signals
    .rom_cfg_i(prim_rom_pkg::ROM_CFG_REQ_DEFAULT),
    .rom_cfg_o(),
    .pwrmgr_data_o(),
    .keymgr_data_o(),
    .kmac_data_o(),
    .kmac_data_i(kmac_pkg::APP_RSP_DEFAULT),
    .regs_tl_i(rom_ctrl_regs_tl_req),
    .regs_tl_o(rom_ctrl_regs_tl_rsp),
    .rom_tl_i(rom_ctrl_rom_tl_req),
    .rom_tl_o(rom_ctrl_rom_tl_rsp)
  );

  rv_core_ibex #(
    .AlertAsyncOn(AsyncOnOutgoingAlertEnglishbreakfast[27:24]),
    .AlertSkewCycles(top_pkg::AlertSkewCycles),
    .RndCnstLfsrSeed(RndCnstRvCoreIbexLfsrSeed),
    .RndCnstLfsrPerm(RndCnstRvCoreIbexLfsrPerm),
    .RndCnstIbexKeyDefault(RndCnstRvCoreIbexIbexKeyDefault),
    .RndCnstIbexNonceDefault(RndCnstRvCoreIbexIbexNonceDefault),
    .NEscalationSeverities(4),
    .WidthPingCounter(16),
    .PMPEnable(RvCoreIbexPMPEnable),
    .PMPGranularity(RvCoreIbexPMPGranularity),
    .PMPNumRegions(RvCoreIbexPMPNumRegions),
    .MHPMCounterNum(RvCoreIbexMHPMCounterNum),
    .MHPMCounterWidth(RvCoreIbexMHPMCounterWidth),
    .PMPRstCfg(RvCoreIbexPMPRstCfg),
    .PMPRstAddr(RvCoreIbexPMPRstAddr),
    .PMPRstMsecCfg(RvCoreIbexPMPRstMsecCfg),
    .RV32E(RvCoreIbexRV32E),
    .RV32M(RvCoreIbexRV32M),
    .RV32B(RvCoreIbexRV32B),
    .RV32ZC(RvCoreIbexRV32ZC),
    .RegFile(RvCoreIbexRegFile),
    .BranchTargetALU(RvCoreIbexBranchTargetALU),
    .WritebackStage(RvCoreIbexWritebackStage),
    .ICache(RvCoreIbexICache),
    .ICacheECC(RvCoreIbexICacheECC),
    .ICacheScramble(RvCoreIbexICacheScramble),
    .ICacheNWays(RvCoreIbexICacheNWays),
    .BranchPredictor(RvCoreIbexBranchPredictor),
    .DbgTriggerEn(RvCoreIbexDbgTriggerEn),
    .DbgHwBreakNum(RvCoreIbexDbgHwBreakNum),
    .SecureIbex(RvCoreIbexSecureIbex),
    .DmBaseAddr(RvCoreIbexDmBaseAddr),
    .DmAddrMask(RvCoreIbexDmAddrMask),
    .DmHaltAddr(RvCoreIbexDmHaltAddr),
    .DmExceptionAddr(RvCoreIbexDmExceptionAddr),
    .PipeLine(RvCoreIbexPipeLine),
    .TlulHostUserRsvdBits(RvCoreIbexTlulHostUserRsvdBits),
    .CsrMvendorId(RvCoreIbexCsrMvendorId),
    .CsrMimpId(RvCoreIbexCsrMimpId),
    .InstructionPipeline(RvCoreIbexInstructionPipeline)
  ) u_rv_core_ibex (
    // Clock and reset connections
    .clk_i(clkmgr_clocks_i.clk_main_infra),
    .clk_edn_i(clkmgr_clocks_i.clk_main_infra),
    .clk_esc_i(clkmgr_clocks_i.clk_io_div4_infra),
    .clk_otp_i(clkmgr_clocks_i.clk_io_div4_infra),
    .rst_ni(rstmgr_resets_i.rst_sys_n[rstmgr_pkg::DomainMainSel]),
    .rst_edn_ni(rstmgr_resets_i.rst_sys_n[rstmgr_pkg::DomainMainSel]),
    .rst_esc_ni(rstmgr_resets_i.rst_lc_io_div4_n[rstmgr_pkg::DomainMainSel]),
    .rst_otp_ni(rstmgr_resets_i.rst_lc_io_div4_n[rstmgr_pkg::DomainMainSel]),

    // DFT/scan connections
    .scanmode_i,
    .scan_rst_ni,

    // External alert group "englishbreakfast" [24]: fatal_sw_err
    // External alert group "englishbreakfast" [25]: recov_sw_err
    // External alert group "englishbreakfast" [26]: fatal_hw_err
    // External alert group "englishbreakfast" [27]: recov_hw_err
    .alert_tx_o(outgoing_alert_englishbreakfast_tx_o[21:18]),
    .alert_rx_i(outgoing_alert_englishbreakfast_rx_i[21:18]),

    // Inter-module signals
    .rst_cpu_n_o(),
    .ram_cfg_icache_tag_i('{default: prim_ram_1p_pkg::RAM_1P_CFG_REQ_DEFAULT}),
    .ram_cfg_icache_tag_o(),
    .ram_cfg_icache_data_i('{default: prim_ram_1p_pkg::RAM_1P_CFG_REQ_DEFAULT}),
    .ram_cfg_icache_data_o(),
    .hart_id_i(rv_core_ibex_hart_id),
    .boot_addr_i(rv_core_ibex_boot_addr),
    .irq_software_i(rv_plic_msip),
    .irq_timer_i(rv_core_ibex_irq_timer),
    .irq_external_i(rv_plic_irq),
    .esc_tx_i(prim_esc_pkg::ESC_TX_DEFAULT),
    .esc_rx_o(),
    .debug_req_i('0),
    .crash_dump_o(rv_core_ibex_crash_dump_o),
    .lc_cpu_en_i(lc_ctrl_pkg::On),
    .pwrmgr_cpu_en_i(pwrmgr_fetch_en_i),
    .pwrmgr_o(rv_core_ibex_pwrmgr_o),
    .nmi_wdog_i('0),
    .edn_o(),
    .edn_i(edn_pkg::EDN_RSP_DEFAULT),
    .icache_otp_key_o(),
    .icache_otp_key_i(otp_ctrl_pkg::SRAM_OTP_KEY_RSP_DEFAULT),
    .fpga_info_i(fpga_info_i),
    .corei_tl_h_o(main_tl_rv_core_ibex__corei_req),
    .corei_tl_h_i(main_tl_rv_core_ibex__corei_rsp),
    .cored_tl_h_o(main_tl_rv_core_ibex__cored_req),
    .cored_tl_h_i(main_tl_rv_core_ibex__cored_rsp),
    .cfg_tl_d_i(rv_core_ibex_cfg_tl_d_req),
    .cfg_tl_d_o(rv_core_ibex_cfg_tl_d_rsp)
  );


  // Interrupt assignments
  assign intr_vector = {
    intr_flash_ctrl_corr_err,                 // ID 87
    intr_flash_ctrl_op_done,                  // ID 86
    intr_flash_ctrl_rd_lvl,                   // ID 85
    intr_flash_ctrl_rd_full,                  // ID 84
    intr_flash_ctrl_prog_lvl,                 // ID 83
    intr_flash_ctrl_prog_empty,               // ID 82
    intr_vector_pd_aon_i[2],                  // ID 81 (aon_timer_wdog_timer_bark)
    intr_vector_pd_aon_i[1],                  // ID 80 (aon_timer_wkup_timer_expired)
    intr_vector_pd_aon_i[0],                  // ID 79 (pwrmgr_wakeup)
    intr_usbdev_av_setup_empty,               // ID 78
    intr_usbdev_link_out_err,                 // ID 77
    intr_usbdev_powered,                      // ID 76
    intr_usbdev_frame,                        // ID 75
    intr_usbdev_rx_bitstuff_err,              // ID 74
    intr_usbdev_rx_pid_err,                   // ID 73
    intr_usbdev_rx_crc_err,                   // ID 72
    intr_usbdev_link_in_err,                  // ID 71
    intr_usbdev_av_overflow,                  // ID 70
    intr_usbdev_rx_full,                      // ID 69
    intr_usbdev_av_out_empty,                 // ID 68
    intr_usbdev_link_resume,                  // ID 67
    intr_usbdev_link_suspend,                 // ID 66
    intr_usbdev_link_reset,                   // ID 65
    intr_usbdev_host_lost,                    // ID 64
    intr_usbdev_disconnected,                 // ID 63
    intr_usbdev_pkt_sent,                     // ID 62
    intr_usbdev_pkt_received,                 // ID 61
    intr_spi_host0_spi_event,                 // ID 60
    intr_spi_host0_error,                     // ID 59
    intr_spi_device_tpm_rdfifo_drop,          // ID 58
    intr_spi_device_tpm_rdfifo_cmd_end,       // ID 57
    intr_spi_device_tpm_header_not_empty,     // ID 56
    intr_spi_device_readbuf_flip,             // ID 55
    intr_spi_device_readbuf_watermark,        // ID 54
    intr_spi_device_upload_payload_overflow,  // ID 53
    intr_spi_device_upload_payload_not_empty, // ID 52
    intr_spi_device_upload_cmdfifo_not_empty, // ID 51
    intr_gpio_gpio,                           // IDs [19 +: 32]
    intr_uart1_tx_empty,                      // ID 18
    intr_uart1_rx_parity_err,                 // ID 17
    intr_uart1_rx_timeout,                    // ID 16
    intr_uart1_rx_break_err,                  // ID 15
    intr_uart1_rx_frame_err,                  // ID 14
    intr_uart1_rx_overflow,                   // ID 13
    intr_uart1_tx_done,                       // ID 12
    intr_uart1_rx_watermark,                  // ID 11
    intr_uart1_tx_watermark,                  // ID 10
    intr_uart0_tx_empty,                      // ID 9
    intr_uart0_rx_parity_err,                 // ID 8
    intr_uart0_rx_timeout,                    // ID 7
    intr_uart0_rx_break_err,                  // ID 6
    intr_uart0_rx_frame_err,                  // ID 5
    intr_uart0_rx_overflow,                   // ID 4
    intr_uart0_tx_done,                       // ID 3
    intr_uart0_rx_watermark,                  // ID 2
    intr_uart0_tx_watermark,                  // ID 1
    1'b0 // ID 0 is a special case and tied to zero.
  };

  // Instantiation of TL-UL crossbars
  xbar_main u_xbar_main (
    .clk_main_i(clkmgr_clocks_i.clk_main_infra),
    .clk_fixed_i(clkmgr_clocks_i.clk_io_div4_infra),
    .rst_main_ni(rstmgr_resets_i.rst_sys_n[rstmgr_pkg::DomainMainSel]),
    .rst_fixed_ni(rstmgr_resets_i.rst_sys_io_div4_n[rstmgr_pkg::DomainMainSel]),

    // port: tl_rv_core_ibex__corei
    .tl_rv_core_ibex__corei_i(main_tl_rv_core_ibex__corei_req),
    .tl_rv_core_ibex__corei_o(main_tl_rv_core_ibex__corei_rsp),

    // port: tl_rv_core_ibex__cored
    .tl_rv_core_ibex__cored_i(main_tl_rv_core_ibex__cored_req),
    .tl_rv_core_ibex__cored_o(main_tl_rv_core_ibex__cored_rsp),

    // port: tl_rom_ctrl__rom
    .tl_rom_ctrl__rom_o(rom_ctrl_rom_tl_req),
    .tl_rom_ctrl__rom_i(rom_ctrl_rom_tl_rsp),

    // port: tl_rom_ctrl__regs
    .tl_rom_ctrl__regs_o(rom_ctrl_regs_tl_req),
    .tl_rom_ctrl__regs_i(rom_ctrl_regs_tl_rsp),

    // port: tl_peri
    .tl_peri_o(main_tl_peri_req),
    .tl_peri_i(main_tl_peri_rsp),

    // port: tl_flash_ctrl__core
    .tl_flash_ctrl__core_o(flash_ctrl_core_tl_req),
    .tl_flash_ctrl__core_i(flash_ctrl_core_tl_rsp),

    // port: tl_flash_ctrl__prim
    .tl_flash_ctrl__prim_o(flash_ctrl_prim_tl_req),
    .tl_flash_ctrl__prim_i(flash_ctrl_prim_tl_rsp),

    // port: tl_flash_ctrl__mem
    .tl_flash_ctrl__mem_o(flash_ctrl_mem_tl_req),
    .tl_flash_ctrl__mem_i(flash_ctrl_mem_tl_rsp),

    // port: tl_aes
    .tl_aes_o(aes_tl_req),
    .tl_aes_i(aes_tl_rsp),

    // port: tl_rv_plic
    .tl_rv_plic_o(rv_plic_tl_req),
    .tl_rv_plic_i(rv_plic_tl_rsp),

    // port: tl_rv_core_ibex__cfg
    .tl_rv_core_ibex__cfg_o(rv_core_ibex_cfg_tl_d_req),
    .tl_rv_core_ibex__cfg_i(rv_core_ibex_cfg_tl_d_rsp),

    // port: tl_sram_ctrl_main__regs
    .tl_sram_ctrl_main__regs_o(sram_ctrl_main_regs_tl_req),
    .tl_sram_ctrl_main__regs_i(sram_ctrl_main_regs_tl_rsp),

    // port: tl_sram_ctrl_main__ram
    .tl_sram_ctrl_main__ram_o(sram_ctrl_main_ram_tl_req),
    .tl_sram_ctrl_main__ram_i(sram_ctrl_main_ram_tl_rsp),

    .scanmode_i
  );

  xbar_peri u_xbar_peri (
    .clk_peri_i(clkmgr_clocks_i.clk_io_div4_infra),
    .clk_spi_host0_i(clkmgr_clocks_i.clk_io_infra),
    .clk_usb_i(clkmgr_clocks_i.clk_usb_infra),
    .rst_peri_ni(rstmgr_resets_i.rst_sys_io_div4_n[rstmgr_pkg::DomainMainSel]),
    .rst_spi_host0_ni(rstmgr_resets_i.rst_spi_host0_n[rstmgr_pkg::DomainMainSel]),
    .rst_usb_ni(rstmgr_resets_i.rst_usb_n[rstmgr_pkg::DomainMainSel]),

    // port: tl_main
    .tl_main_i(main_tl_peri_req),
    .tl_main_o(main_tl_peri_rsp),

    // port: tl_uart0
    .tl_uart0_o(uart0_tl_req),
    .tl_uart0_i(uart0_tl_rsp),

    // port: tl_uart1
    .tl_uart1_o(uart1_tl_req),
    .tl_uart1_i(uart1_tl_rsp),

    // port: tl_gpio
    .tl_gpio_o(gpio_tl_req),
    .tl_gpio_i(gpio_tl_rsp),

    // port: tl_spi_device
    .tl_spi_device_o(spi_device_tl_req),
    .tl_spi_device_i(spi_device_tl_rsp),

    // port: tl_spi_host0
    .tl_spi_host0_o(spi_host0_tl_req),
    .tl_spi_host0_i(spi_host0_tl_rsp),

    // port: tl_rv_timer
    .tl_rv_timer_o(rv_timer_tl_req),
    .tl_rv_timer_i(rv_timer_tl_rsp),

    // port: tl_usbdev
    .tl_usbdev_o(usbdev_tl_req),
    .tl_usbdev_i(usbdev_tl_rsp),

    // port: tl_pwrmgr
    .tl_pwrmgr_o(pwrmgr_tl_req_o),
    .tl_pwrmgr_i(pwrmgr_tl_rsp_i),

    // port: tl_rstmgr
    .tl_rstmgr_o(rstmgr_tl_req_o),
    .tl_rstmgr_i(rstmgr_tl_rsp_i),

    // port: tl_clkmgr
    .tl_clkmgr_o(clkmgr_tl_req_o),
    .tl_clkmgr_i(clkmgr_tl_rsp_i),

    // port: tl_pinmux
    .tl_pinmux_o(pinmux_tl_req),
    .tl_pinmux_i(pinmux_tl_rsp),

    // port: tl_ast
    .tl_ast_o(ast_tl_req_o),
    .tl_ast_i(ast_tl_rsp_i),

    .scanmode_i
  );


  // Pinmux connections
  // All muxed inputs
  assign cio_gpio_gpio_p2d[0] = mio_p2d[MioInGpioGpio0];
  assign cio_gpio_gpio_p2d[1] = mio_p2d[MioInGpioGpio1];
  assign cio_gpio_gpio_p2d[2] = mio_p2d[MioInGpioGpio2];
  assign cio_gpio_gpio_p2d[3] = mio_p2d[MioInGpioGpio3];
  assign cio_gpio_gpio_p2d[4] = mio_p2d[MioInGpioGpio4];
  assign cio_gpio_gpio_p2d[5] = mio_p2d[MioInGpioGpio5];
  assign cio_gpio_gpio_p2d[6] = mio_p2d[MioInGpioGpio6];
  assign cio_gpio_gpio_p2d[7] = mio_p2d[MioInGpioGpio7];
  assign cio_gpio_gpio_p2d[8] = mio_p2d[MioInGpioGpio8];
  assign cio_gpio_gpio_p2d[9] = mio_p2d[MioInGpioGpio9];
  assign cio_gpio_gpio_p2d[10] = mio_p2d[MioInGpioGpio10];
  assign cio_gpio_gpio_p2d[11] = mio_p2d[MioInGpioGpio11];
  assign cio_gpio_gpio_p2d[12] = mio_p2d[MioInGpioGpio12];
  assign cio_gpio_gpio_p2d[13] = mio_p2d[MioInGpioGpio13];
  assign cio_gpio_gpio_p2d[14] = mio_p2d[MioInGpioGpio14];
  assign cio_gpio_gpio_p2d[15] = mio_p2d[MioInGpioGpio15];
  assign cio_gpio_gpio_p2d[16] = mio_p2d[MioInGpioGpio16];
  assign cio_gpio_gpio_p2d[17] = mio_p2d[MioInGpioGpio17];
  assign cio_gpio_gpio_p2d[18] = mio_p2d[MioInGpioGpio18];
  assign cio_gpio_gpio_p2d[19] = mio_p2d[MioInGpioGpio19];
  assign cio_gpio_gpio_p2d[20] = mio_p2d[MioInGpioGpio20];
  assign cio_gpio_gpio_p2d[21] = mio_p2d[MioInGpioGpio21];
  assign cio_gpio_gpio_p2d[22] = mio_p2d[MioInGpioGpio22];
  assign cio_gpio_gpio_p2d[23] = mio_p2d[MioInGpioGpio23];
  assign cio_gpio_gpio_p2d[24] = mio_p2d[MioInGpioGpio24];
  assign cio_gpio_gpio_p2d[25] = mio_p2d[MioInGpioGpio25];
  assign cio_gpio_gpio_p2d[26] = mio_p2d[MioInGpioGpio26];
  assign cio_gpio_gpio_p2d[27] = mio_p2d[MioInGpioGpio27];
  assign cio_gpio_gpio_p2d[28] = mio_p2d[MioInGpioGpio28];
  assign cio_gpio_gpio_p2d[29] = mio_p2d[MioInGpioGpio29];
  assign cio_gpio_gpio_p2d[30] = mio_p2d[MioInGpioGpio30];
  assign cio_gpio_gpio_p2d[31] = mio_p2d[MioInGpioGpio31];
  assign cio_uart0_rx_p2d = mio_p2d[MioInUart0Rx];
  assign cio_uart1_rx_p2d = mio_p2d[MioInUart1Rx];
  assign cio_flash_ctrl_tck_p2d = mio_p2d[MioInFlashCtrlTck];
  assign cio_flash_ctrl_tms_p2d = mio_p2d[MioInFlashCtrlTms];
  assign cio_flash_ctrl_tdi_p2d = mio_p2d[MioInFlashCtrlTdi];
  assign cio_usbdev_sense_p2d = mio_p2d[MioInUsbdevSense];

  // All muxed outputs
  assign mio_d2p[MioOutGpioGpio0] = cio_gpio_gpio_d2p[0];
  assign mio_d2p[MioOutGpioGpio1] = cio_gpio_gpio_d2p[1];
  assign mio_d2p[MioOutGpioGpio2] = cio_gpio_gpio_d2p[2];
  assign mio_d2p[MioOutGpioGpio3] = cio_gpio_gpio_d2p[3];
  assign mio_d2p[MioOutGpioGpio4] = cio_gpio_gpio_d2p[4];
  assign mio_d2p[MioOutGpioGpio5] = cio_gpio_gpio_d2p[5];
  assign mio_d2p[MioOutGpioGpio6] = cio_gpio_gpio_d2p[6];
  assign mio_d2p[MioOutGpioGpio7] = cio_gpio_gpio_d2p[7];
  assign mio_d2p[MioOutGpioGpio8] = cio_gpio_gpio_d2p[8];
  assign mio_d2p[MioOutGpioGpio9] = cio_gpio_gpio_d2p[9];
  assign mio_d2p[MioOutGpioGpio10] = cio_gpio_gpio_d2p[10];
  assign mio_d2p[MioOutGpioGpio11] = cio_gpio_gpio_d2p[11];
  assign mio_d2p[MioOutGpioGpio12] = cio_gpio_gpio_d2p[12];
  assign mio_d2p[MioOutGpioGpio13] = cio_gpio_gpio_d2p[13];
  assign mio_d2p[MioOutGpioGpio14] = cio_gpio_gpio_d2p[14];
  assign mio_d2p[MioOutGpioGpio15] = cio_gpio_gpio_d2p[15];
  assign mio_d2p[MioOutGpioGpio16] = cio_gpio_gpio_d2p[16];
  assign mio_d2p[MioOutGpioGpio17] = cio_gpio_gpio_d2p[17];
  assign mio_d2p[MioOutGpioGpio18] = cio_gpio_gpio_d2p[18];
  assign mio_d2p[MioOutGpioGpio19] = cio_gpio_gpio_d2p[19];
  assign mio_d2p[MioOutGpioGpio20] = cio_gpio_gpio_d2p[20];
  assign mio_d2p[MioOutGpioGpio21] = cio_gpio_gpio_d2p[21];
  assign mio_d2p[MioOutGpioGpio22] = cio_gpio_gpio_d2p[22];
  assign mio_d2p[MioOutGpioGpio23] = cio_gpio_gpio_d2p[23];
  assign mio_d2p[MioOutGpioGpio24] = cio_gpio_gpio_d2p[24];
  assign mio_d2p[MioOutGpioGpio25] = cio_gpio_gpio_d2p[25];
  assign mio_d2p[MioOutGpioGpio26] = cio_gpio_gpio_d2p[26];
  assign mio_d2p[MioOutGpioGpio27] = cio_gpio_gpio_d2p[27];
  assign mio_d2p[MioOutGpioGpio28] = cio_gpio_gpio_d2p[28];
  assign mio_d2p[MioOutGpioGpio29] = cio_gpio_gpio_d2p[29];
  assign mio_d2p[MioOutGpioGpio30] = cio_gpio_gpio_d2p[30];
  assign mio_d2p[MioOutGpioGpio31] = cio_gpio_gpio_d2p[31];
  assign mio_d2p[MioOutUart0Tx] = cio_uart0_tx_d2p;
  assign mio_d2p[MioOutUart1Tx] = cio_uart1_tx_d2p;
  assign mio_d2p[MioOutFlashCtrlTdo] = cio_flash_ctrl_tdo_d2p;

  // All muxed output enables
  assign mio_en_d2p[MioOutGpioGpio0] = cio_gpio_gpio_en_d2p[0];
  assign mio_en_d2p[MioOutGpioGpio1] = cio_gpio_gpio_en_d2p[1];
  assign mio_en_d2p[MioOutGpioGpio2] = cio_gpio_gpio_en_d2p[2];
  assign mio_en_d2p[MioOutGpioGpio3] = cio_gpio_gpio_en_d2p[3];
  assign mio_en_d2p[MioOutGpioGpio4] = cio_gpio_gpio_en_d2p[4];
  assign mio_en_d2p[MioOutGpioGpio5] = cio_gpio_gpio_en_d2p[5];
  assign mio_en_d2p[MioOutGpioGpio6] = cio_gpio_gpio_en_d2p[6];
  assign mio_en_d2p[MioOutGpioGpio7] = cio_gpio_gpio_en_d2p[7];
  assign mio_en_d2p[MioOutGpioGpio8] = cio_gpio_gpio_en_d2p[8];
  assign mio_en_d2p[MioOutGpioGpio9] = cio_gpio_gpio_en_d2p[9];
  assign mio_en_d2p[MioOutGpioGpio10] = cio_gpio_gpio_en_d2p[10];
  assign mio_en_d2p[MioOutGpioGpio11] = cio_gpio_gpio_en_d2p[11];
  assign mio_en_d2p[MioOutGpioGpio12] = cio_gpio_gpio_en_d2p[12];
  assign mio_en_d2p[MioOutGpioGpio13] = cio_gpio_gpio_en_d2p[13];
  assign mio_en_d2p[MioOutGpioGpio14] = cio_gpio_gpio_en_d2p[14];
  assign mio_en_d2p[MioOutGpioGpio15] = cio_gpio_gpio_en_d2p[15];
  assign mio_en_d2p[MioOutGpioGpio16] = cio_gpio_gpio_en_d2p[16];
  assign mio_en_d2p[MioOutGpioGpio17] = cio_gpio_gpio_en_d2p[17];
  assign mio_en_d2p[MioOutGpioGpio18] = cio_gpio_gpio_en_d2p[18];
  assign mio_en_d2p[MioOutGpioGpio19] = cio_gpio_gpio_en_d2p[19];
  assign mio_en_d2p[MioOutGpioGpio20] = cio_gpio_gpio_en_d2p[20];
  assign mio_en_d2p[MioOutGpioGpio21] = cio_gpio_gpio_en_d2p[21];
  assign mio_en_d2p[MioOutGpioGpio22] = cio_gpio_gpio_en_d2p[22];
  assign mio_en_d2p[MioOutGpioGpio23] = cio_gpio_gpio_en_d2p[23];
  assign mio_en_d2p[MioOutGpioGpio24] = cio_gpio_gpio_en_d2p[24];
  assign mio_en_d2p[MioOutGpioGpio25] = cio_gpio_gpio_en_d2p[25];
  assign mio_en_d2p[MioOutGpioGpio26] = cio_gpio_gpio_en_d2p[26];
  assign mio_en_d2p[MioOutGpioGpio27] = cio_gpio_gpio_en_d2p[27];
  assign mio_en_d2p[MioOutGpioGpio28] = cio_gpio_gpio_en_d2p[28];
  assign mio_en_d2p[MioOutGpioGpio29] = cio_gpio_gpio_en_d2p[29];
  assign mio_en_d2p[MioOutGpioGpio30] = cio_gpio_gpio_en_d2p[30];
  assign mio_en_d2p[MioOutGpioGpio31] = cio_gpio_gpio_en_d2p[31];
  assign mio_en_d2p[MioOutUart0Tx] = cio_uart0_tx_en_d2p;
  assign mio_en_d2p[MioOutUart1Tx] = cio_uart1_tx_en_d2p;
  assign mio_en_d2p[MioOutFlashCtrlTdo] = cio_flash_ctrl_tdo_en_d2p;

  // All dedicated inputs
  logic [13:0] unused_dio_p2d;
  assign unused_dio_p2d = dio_p2d;
  assign cio_spi_host0_sd_p2d[0] = dio_p2d[DioSpiHost0Sd0];
  assign cio_spi_host0_sd_p2d[1] = dio_p2d[DioSpiHost0Sd1];
  assign cio_spi_host0_sd_p2d[2] = dio_p2d[DioSpiHost0Sd2];
  assign cio_spi_host0_sd_p2d[3] = dio_p2d[DioSpiHost0Sd3];
  assign cio_spi_device_sd_p2d[0] = dio_p2d[DioSpiDeviceSd0];
  assign cio_spi_device_sd_p2d[1] = dio_p2d[DioSpiDeviceSd1];
  assign cio_spi_device_sd_p2d[2] = dio_p2d[DioSpiDeviceSd2];
  assign cio_spi_device_sd_p2d[3] = dio_p2d[DioSpiDeviceSd3];
  assign cio_usbdev_usb_dp_p2d = dio_p2d[DioUsbdevUsbDp];
  assign cio_usbdev_usb_dn_p2d = dio_p2d[DioUsbdevUsbDn];
  assign cio_spi_device_sck_p2d = dio_p2d[DioSpiDeviceSck];
  assign cio_spi_device_csb_p2d = dio_p2d[DioSpiDeviceCsb];

  // All dedicated outputs
  assign dio_d2p[DioSpiHost0Sd0] = cio_spi_host0_sd_d2p[0];
  assign dio_d2p[DioSpiHost0Sd1] = cio_spi_host0_sd_d2p[1];
  assign dio_d2p[DioSpiHost0Sd2] = cio_spi_host0_sd_d2p[2];
  assign dio_d2p[DioSpiHost0Sd3] = cio_spi_host0_sd_d2p[3];
  assign dio_d2p[DioSpiDeviceSd0] = cio_spi_device_sd_d2p[0];
  assign dio_d2p[DioSpiDeviceSd1] = cio_spi_device_sd_d2p[1];
  assign dio_d2p[DioSpiDeviceSd2] = cio_spi_device_sd_d2p[2];
  assign dio_d2p[DioSpiDeviceSd3] = cio_spi_device_sd_d2p[3];
  assign dio_d2p[DioUsbdevUsbDp] = cio_usbdev_usb_dp_d2p;
  assign dio_d2p[DioUsbdevUsbDn] = cio_usbdev_usb_dn_d2p;
  assign dio_d2p[DioSpiDeviceSck] = 1'b0;
  assign dio_d2p[DioSpiDeviceCsb] = 1'b0;
  assign dio_d2p[DioSpiHost0Sck] = cio_spi_host0_sck_d2p;
  assign dio_d2p[DioSpiHost0Csb] = cio_spi_host0_csb_d2p;

  // All dedicated output enables
  assign dio_en_d2p[DioSpiHost0Sd0] = cio_spi_host0_sd_en_d2p[0];
  assign dio_en_d2p[DioSpiHost0Sd1] = cio_spi_host0_sd_en_d2p[1];
  assign dio_en_d2p[DioSpiHost0Sd2] = cio_spi_host0_sd_en_d2p[2];
  assign dio_en_d2p[DioSpiHost0Sd3] = cio_spi_host0_sd_en_d2p[3];
  assign dio_en_d2p[DioSpiDeviceSd0] = cio_spi_device_sd_en_d2p[0];
  assign dio_en_d2p[DioSpiDeviceSd1] = cio_spi_device_sd_en_d2p[1];
  assign dio_en_d2p[DioSpiDeviceSd2] = cio_spi_device_sd_en_d2p[2];
  assign dio_en_d2p[DioSpiDeviceSd3] = cio_spi_device_sd_en_d2p[3];
  assign dio_en_d2p[DioUsbdevUsbDp] = cio_usbdev_usb_dp_en_d2p;
  assign dio_en_d2p[DioUsbdevUsbDn] = cio_usbdev_usb_dn_en_d2p;
  assign dio_en_d2p[DioSpiDeviceSck] = 1'b0;
  assign dio_en_d2p[DioSpiDeviceCsb] = 1'b0;
  assign dio_en_d2p[DioSpiHost0Sck] = cio_spi_host0_sck_en_d2p;
  assign dio_en_d2p[DioSpiHost0Csb] = cio_spi_host0_csb_en_d2p;

endmodule
