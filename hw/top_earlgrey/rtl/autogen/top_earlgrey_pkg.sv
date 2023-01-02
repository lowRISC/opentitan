// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_earlgrey/data/top_earlgrey.hjson \
//                -o hw/top_earlgrey/ \
//                --rnd_cnst_seed 4881560218908238235

package top_earlgrey_pkg;
  /**
   * Peripheral base address for gpio in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_GPIO_BASE_ADDR = 32'hC0040000;

  /**
   * Peripheral size in bytes for gpio in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_GPIO_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for pattgen in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_PATTGEN_BASE_ADDR = 32'hC00E0000;

  /**
   * Peripheral size in bytes for pattgen in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_PATTGEN_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for rv_timer in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_TIMER_BASE_ADDR = 32'hC0100000;

  /**
   * Peripheral size in bytes for rv_timer in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_TIMER_SIZE_BYTES = 32'h200;

  /**
   * Peripheral base address for core device on otp_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR = 32'hC0130000;

  /**
   * Peripheral size in bytes for core device on otp_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_OTP_CTRL_CORE_SIZE_BYTES = 32'h2000;

  /**
   * Peripheral base address for prim device on otp_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_OTP_CTRL_PRIM_BASE_ADDR = 32'hC0132000;

  /**
   * Peripheral size in bytes for prim device on otp_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_OTP_CTRL_PRIM_SIZE_BYTES = 32'h20;

  /**
   * Peripheral base address for lc_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_LC_CTRL_BASE_ADDR = 32'hC0140000;

  /**
   * Peripheral size in bytes for lc_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_LC_CTRL_SIZE_BYTES = 32'h100;

  /**
   * Peripheral base address for alert_handler in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR = 32'hC0150000;

  /**
   * Peripheral size in bytes for alert_handler in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ALERT_HANDLER_SIZE_BYTES = 32'h800;

  /**
   * Peripheral base address for spi_host0 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SPI_HOST0_BASE_ADDR = 32'hC0300000;

  /**
   * Peripheral size in bytes for spi_host0 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SPI_HOST0_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for spi_host1 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SPI_HOST1_BASE_ADDR = 32'hC0310000;

  /**
   * Peripheral size in bytes for spi_host1 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SPI_HOST1_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for spi_device in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SPI_DEVICE_BASE_ADDR = 32'hC0050000;

  /**
   * Peripheral size in bytes for spi_device in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SPI_DEVICE_SIZE_BYTES = 32'h2000;

  /**
   * Peripheral base address for pwrmgr_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_PWRMGR_AON_BASE_ADDR = 32'hC0400000;

  /**
   * Peripheral size in bytes for pwrmgr_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_PWRMGR_AON_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for rstmgr_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RSTMGR_AON_BASE_ADDR = 32'hC0410000;

  /**
   * Peripheral size in bytes for rstmgr_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RSTMGR_AON_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for clkmgr_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_CLKMGR_AON_BASE_ADDR = 32'hC0420000;

  /**
   * Peripheral size in bytes for clkmgr_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_CLKMGR_AON_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for sysrst_ctrl_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SYSRST_CTRL_AON_BASE_ADDR = 32'hC0430000;

  /**
   * Peripheral size in bytes for sysrst_ctrl_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SYSRST_CTRL_AON_SIZE_BYTES = 32'h100;

  /**
   * Peripheral base address for pinmux_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_PINMUX_AON_BASE_ADDR = 32'hC0460000;

  /**
   * Peripheral size in bytes for pinmux_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_PINMUX_AON_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for aon_timer_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR = 32'hC0470000;

  /**
   * Peripheral size in bytes for aon_timer_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_AON_TIMER_AON_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for ast in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_AST_BASE_ADDR = 32'hC0480000;

  /**
   * Peripheral size in bytes for ast in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_AST_SIZE_BYTES = 32'h400;

  /**
   * Peripheral base address for regs device on sram_ctrl_ret_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_BASE_ADDR = 32'hC0500000;

  /**
   * Peripheral size in bytes for regs device on sram_ctrl_ret_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_SIZE_BYTES = 32'h20;

  /**
   * Peripheral base address for ram device on sram_ctrl_ret_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR = 32'hC0600000;

  /**
   * Peripheral size in bytes for ram device on sram_ctrl_ret_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for core device on flash_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR = 32'hC1000000;

  /**
   * Peripheral size in bytes for core device on flash_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_FLASH_CTRL_CORE_SIZE_BYTES = 32'h200;

  /**
   * Peripheral base address for prim device on flash_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_FLASH_CTRL_PRIM_BASE_ADDR = 32'hC1008000;

  /**
   * Peripheral size in bytes for prim device on flash_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_FLASH_CTRL_PRIM_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for mem device on flash_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR = 32'hF0000000;

  /**
   * Peripheral size in bytes for mem device on flash_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_FLASH_CTRL_MEM_SIZE_BYTES = 32'h100000;

  /**
   * Peripheral base address for regs device on rv_dm in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_DM_REGS_BASE_ADDR = 32'hC1200000;

  /**
   * Peripheral size in bytes for regs device on rv_dm in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_DM_REGS_SIZE_BYTES = 32'h4;

  /**
   * Peripheral base address for mem device on rv_dm in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_DM_MEM_BASE_ADDR = 32'h0;

  /**
   * Peripheral size in bytes for mem device on rv_dm in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_DM_MEM_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for tlul2axi in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_TLUL2AXI_BASE_ADDR = 32'h10000;

  /**
   * Peripheral size in bytes for tlul2axi in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_TLUL2AXI_SIZE_BYTES = 32'h10;

  /**
   * Peripheral base address for rv_plic in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_PLIC_BASE_ADDR = 32'hC8000000;

  /**
   * Peripheral size in bytes for rv_plic in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_PLIC_SIZE_BYTES = 32'h8000000;

  /**
   * Peripheral base address for aes in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_AES_BASE_ADDR = 32'hC1100000;

  /**
   * Peripheral size in bytes for aes in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_AES_SIZE_BYTES = 32'h100;

  /**
   * Peripheral base address for hmac in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_HMAC_BASE_ADDR = 32'hC1110000;

  /**
   * Peripheral size in bytes for hmac in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_HMAC_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for kmac in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_KMAC_BASE_ADDR = 32'hC1120000;

  /**
   * Peripheral size in bytes for kmac in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_KMAC_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for otbn in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_OTBN_BASE_ADDR = 32'hC1130000;

  /**
   * Peripheral size in bytes for otbn in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_OTBN_SIZE_BYTES = 32'h10000;

  /**
   * Peripheral base address for keymgr in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_KEYMGR_BASE_ADDR = 32'hC1140000;

  /**
   * Peripheral size in bytes for keymgr in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_KEYMGR_SIZE_BYTES = 32'h100;

  /**
   * Peripheral base address for csrng in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_CSRNG_BASE_ADDR = 32'hC1150000;

  /**
   * Peripheral size in bytes for csrng in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_CSRNG_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for entropy_src in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR = 32'hC1160000;

  /**
   * Peripheral size in bytes for entropy_src in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ENTROPY_SRC_SIZE_BYTES = 32'h100;

  /**
   * Peripheral base address for edn0 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_EDN0_BASE_ADDR = 32'hC1170000;

  /**
   * Peripheral size in bytes for edn0 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_EDN0_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for edn1 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_EDN1_BASE_ADDR = 32'hC1180000;

  /**
   * Peripheral size in bytes for edn1 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_EDN1_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for regs device on sram_ctrl_main in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR = 32'hC11C0000;

  /**
   * Peripheral size in bytes for regs device on sram_ctrl_main in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_SIZE_BYTES = 32'h20;

  /**
   * Peripheral base address for ram device on sram_ctrl_main in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_BASE_ADDR = 32'hE0000000;

  /**
   * Peripheral size in bytes for ram device on sram_ctrl_main in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_SIZE_BYTES = 32'h20000;

  /**
   * Peripheral base address for regs device on rom_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ROM_CTRL_REGS_BASE_ADDR = 32'hC11E0000;

  /**
   * Peripheral size in bytes for regs device on rom_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ROM_CTRL_REGS_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for rom device on rom_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ROM_CTRL_ROM_BASE_ADDR = 32'hD0008000;

  /**
   * Peripheral size in bytes for rom device on rom_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ROM_CTRL_ROM_SIZE_BYTES = 32'h8000;

  /**
   * Peripheral base address for cfg device on rv_core_ibex in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR = 32'hC11F0000;

  /**
   * Peripheral size in bytes for cfg device on rv_core_ibex in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_CORE_IBEX_CFG_SIZE_BYTES = 32'h100;

  /**
   * Memory base address for ram_ret_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RAM_RET_AON_BASE_ADDR = 32'hc0600000;

  /**
   * Memory size for ram_ret_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RAM_RET_AON_SIZE_BYTES = 32'h1000;

  /**
   * Memory base address for eflash in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_EFLASH_BASE_ADDR = 32'hf0000000;

  /**
   * Memory size for eflash in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_EFLASH_SIZE_BYTES = 32'h100000;

  /**
   * Memory base address for ram_main in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RAM_MAIN_BASE_ADDR = 32'he0000000;

  /**
   * Memory size for ram_main in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RAM_MAIN_SIZE_BYTES = 32'h20000;

  /**
   * Memory base address for rom in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ROM_BASE_ADDR = 32'hd0008000;

  /**
   * Memory size for rom in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ROM_SIZE_BYTES = 32'h8000;


  // Enumeration of alert modules
  typedef enum int unsigned {
    TopEarlgreyAlertPeripheralGpio = 0,
    TopEarlgreyAlertPeripheralPattgen = 1,
    TopEarlgreyAlertPeripheralRvTimer = 2,
    TopEarlgreyAlertPeripheralOtpCtrl = 3,
    TopEarlgreyAlertPeripheralLcCtrl = 4,
    TopEarlgreyAlertPeripheralSpiHost0 = 5,
    TopEarlgreyAlertPeripheralSpiHost1 = 6,
    TopEarlgreyAlertPeripheralSpiDevice = 7,
    TopEarlgreyAlertPeripheralPwrmgrAon = 8,
    TopEarlgreyAlertPeripheralRstmgrAon = 9,
    TopEarlgreyAlertPeripheralClkmgrAon = 10,
    TopEarlgreyAlertPeripheralSysrstCtrlAon = 11,
    TopEarlgreyAlertPeripheralPinmuxAon = 12,
    TopEarlgreyAlertPeripheralAonTimerAon = 13,
    TopEarlgreyAlertPeripheralSramCtrlRetAon = 14,
    TopEarlgreyAlertPeripheralFlashCtrl = 15,
    TopEarlgreyAlertPeripheralRvDm = 16,
    TopEarlgreyAlertPeripheralRvPlic = 17,
    TopEarlgreyAlertPeripheralAes = 18,
    TopEarlgreyAlertPeripheralHmac = 19,
    TopEarlgreyAlertPeripheralKmac = 20,
    TopEarlgreyAlertPeripheralOtbn = 21,
    TopEarlgreyAlertPeripheralKeymgr = 22,
    TopEarlgreyAlertPeripheralCsrng = 23,
    TopEarlgreyAlertPeripheralEntropySrc = 24,
    TopEarlgreyAlertPeripheralEdn0 = 25,
    TopEarlgreyAlertPeripheralEdn1 = 26,
    TopEarlgreyAlertPeripheralSramCtrlMain = 27,
    TopEarlgreyAlertPeripheralRomCtrl = 28,
    TopEarlgreyAlertPeripheralRvCoreIbex = 29,
    TopEarlgreyAlertPeripheralCount
  } alert_peripheral_e;

  // Enumeration of alerts
  typedef enum int unsigned {
    TopEarlgreyAlertIdGpioFatalFault = 0,
    TopEarlgreyAlertIdPattgenFatalFault = 1,
    TopEarlgreyAlertIdRvTimerFatalFault = 2,
    TopEarlgreyAlertIdOtpCtrlFatalMacroError = 3,
    TopEarlgreyAlertIdOtpCtrlFatalCheckError = 4,
    TopEarlgreyAlertIdOtpCtrlFatalBusIntegError = 5,
    TopEarlgreyAlertIdOtpCtrlFatalPrimOtpAlert = 6,
    TopEarlgreyAlertIdOtpCtrlRecovPrimOtpAlert = 7,
    TopEarlgreyAlertIdLcCtrlFatalProgError = 8,
    TopEarlgreyAlertIdLcCtrlFatalStateError = 9,
    TopEarlgreyAlertIdLcCtrlFatalBusIntegError = 10,
    TopEarlgreyAlertIdSpiHost0FatalFault = 11,
    TopEarlgreyAlertIdSpiHost1FatalFault = 12,
    TopEarlgreyAlertIdSpiDeviceFatalFault = 13,
    TopEarlgreyAlertIdPwrmgrAonFatalFault = 14,
    TopEarlgreyAlertIdRstmgrAonFatalFault = 15,
    TopEarlgreyAlertIdRstmgrAonFatalCnstyFault = 16,
    TopEarlgreyAlertIdClkmgrAonRecovFault = 17,
    TopEarlgreyAlertIdClkmgrAonFatalFault = 18,
    TopEarlgreyAlertIdSysrstCtrlAonFatalFault = 19,
    TopEarlgreyAlertIdPinmuxAonFatalFault = 20,
    TopEarlgreyAlertIdAonTimerAonFatalFault = 21,
    TopEarlgreyAlertIdSramCtrlRetAonFatalError = 22,
    TopEarlgreyAlertIdFlashCtrlRecovErr = 23,
    TopEarlgreyAlertIdFlashCtrlFatalStdErr = 24,
    TopEarlgreyAlertIdFlashCtrlFatalErr = 25,
    TopEarlgreyAlertIdFlashCtrlFatalPrimFlashAlert = 26,
    TopEarlgreyAlertIdFlashCtrlRecovPrimFlashAlert = 27,
    TopEarlgreyAlertIdRvDmFatalFault = 28,
    TopEarlgreyAlertIdRvPlicFatalFault = 29,
    TopEarlgreyAlertIdAesRecovCtrlUpdateErr = 30,
    TopEarlgreyAlertIdAesFatalFault = 31,
    TopEarlgreyAlertIdHmacFatalFault = 32,
    TopEarlgreyAlertIdKmacRecovOperationErr = 33,
    TopEarlgreyAlertIdKmacFatalFaultErr = 34,
    TopEarlgreyAlertIdOtbnFatal = 35,
    TopEarlgreyAlertIdOtbnRecov = 36,
    TopEarlgreyAlertIdKeymgrRecovOperationErr = 37,
    TopEarlgreyAlertIdKeymgrFatalFaultErr = 38,
    TopEarlgreyAlertIdCsrngRecovAlert = 39,
    TopEarlgreyAlertIdCsrngFatalAlert = 40,
    TopEarlgreyAlertIdEntropySrcRecovAlert = 41,
    TopEarlgreyAlertIdEntropySrcFatalAlert = 42,
    TopEarlgreyAlertIdEdn0RecovAlert = 43,
    TopEarlgreyAlertIdEdn0FatalAlert = 44,
    TopEarlgreyAlertIdEdn1RecovAlert = 45,
    TopEarlgreyAlertIdEdn1FatalAlert = 46,
    TopEarlgreyAlertIdSramCtrlMainFatalError = 47,
    TopEarlgreyAlertIdRomCtrlFatal = 48,
    TopEarlgreyAlertIdRvCoreIbexFatalSwErr = 49,
    TopEarlgreyAlertIdRvCoreIbexRecovSwErr = 50,
    TopEarlgreyAlertIdRvCoreIbexFatalHwErr = 51,
    TopEarlgreyAlertIdRvCoreIbexRecovHwErr = 52,
    TopEarlgreyAlertIdCount
  } alert_id_e;

  // Enumeration of IO power domains.
  // Only used in ASIC target.
  typedef enum logic [2:0] {
    IoBankVcc = 0,
    IoBankAvcc = 1,
    IoBankVioa = 2,
    IoBankViob = 3,
    IoBankCount = 4
  } pwr_dom_e;

  // Enumeration for MIO signals on the top-level.
  typedef enum int unsigned {
    MioInGpioGpio0 = 0,
    MioInGpioGpio1 = 1,
    MioInGpioGpio2 = 2,
    MioInGpioGpio3 = 3,
    MioInGpioGpio4 = 4,
    MioInGpioGpio5 = 5,
    MioInGpioGpio6 = 6,
    MioInGpioGpio7 = 7,
    MioInGpioGpio8 = 8,
    MioInGpioGpio9 = 9,
    MioInGpioGpio10 = 10,
    MioInGpioGpio11 = 11,
    MioInGpioGpio12 = 12,
    MioInGpioGpio13 = 13,
    MioInGpioGpio14 = 14,
    MioInGpioGpio15 = 15,
    MioInGpioGpio16 = 16,
    MioInGpioGpio17 = 17,
    MioInGpioGpio18 = 18,
    MioInGpioGpio19 = 19,
    MioInGpioGpio20 = 20,
    MioInGpioGpio21 = 21,
    MioInGpioGpio22 = 22,
    MioInGpioGpio23 = 23,
    MioInGpioGpio24 = 24,
    MioInGpioGpio25 = 25,
    MioInGpioGpio26 = 26,
    MioInGpioGpio27 = 27,
    MioInGpioGpio28 = 28,
    MioInGpioGpio29 = 29,
    MioInGpioGpio30 = 30,
    MioInGpioGpio31 = 31,
    MioInSpiHost1Sd0 = 32,
    MioInSpiHost1Sd1 = 33,
    MioInSpiHost1Sd2 = 34,
    MioInSpiHost1Sd3 = 35,
    MioInSpiDeviceTpmCsb = 36,
    MioInFlashCtrlTck = 37,
    MioInFlashCtrlTms = 38,
    MioInFlashCtrlTdi = 39,
    MioInSysrstCtrlAonAcPresent = 40,
    MioInSysrstCtrlAonKey0In = 41,
    MioInSysrstCtrlAonKey1In = 42,
    MioInSysrstCtrlAonKey2In = 43,
    MioInSysrstCtrlAonPwrbIn = 44,
    MioInSysrstCtrlAonLidOpen = 45,
    MioInCount = 46
  } mio_in_e;

  typedef enum {
    MioOutGpioGpio0 = 0,
    MioOutGpioGpio1 = 1,
    MioOutGpioGpio2 = 2,
    MioOutGpioGpio3 = 3,
    MioOutGpioGpio4 = 4,
    MioOutGpioGpio5 = 5,
    MioOutGpioGpio6 = 6,
    MioOutGpioGpio7 = 7,
    MioOutGpioGpio8 = 8,
    MioOutGpioGpio9 = 9,
    MioOutGpioGpio10 = 10,
    MioOutGpioGpio11 = 11,
    MioOutGpioGpio12 = 12,
    MioOutGpioGpio13 = 13,
    MioOutGpioGpio14 = 14,
    MioOutGpioGpio15 = 15,
    MioOutGpioGpio16 = 16,
    MioOutGpioGpio17 = 17,
    MioOutGpioGpio18 = 18,
    MioOutGpioGpio19 = 19,
    MioOutGpioGpio20 = 20,
    MioOutGpioGpio21 = 21,
    MioOutGpioGpio22 = 22,
    MioOutGpioGpio23 = 23,
    MioOutGpioGpio24 = 24,
    MioOutGpioGpio25 = 25,
    MioOutGpioGpio26 = 26,
    MioOutGpioGpio27 = 27,
    MioOutGpioGpio28 = 28,
    MioOutGpioGpio29 = 29,
    MioOutGpioGpio30 = 30,
    MioOutGpioGpio31 = 31,
    MioOutSpiHost1Sd0 = 32,
    MioOutSpiHost1Sd1 = 33,
    MioOutSpiHost1Sd2 = 34,
    MioOutSpiHost1Sd3 = 35,
    MioOutPattgenPda0Tx = 36,
    MioOutPattgenPcl0Tx = 37,
    MioOutPattgenPda1Tx = 38,
    MioOutPattgenPcl1Tx = 39,
    MioOutSpiHost1Sck = 40,
    MioOutSpiHost1Csb = 41,
    MioOutFlashCtrlTdo = 42,
    MioOutOtpCtrlTest0 = 43,
    MioOutSysrstCtrlAonBatDisable = 44,
    MioOutSysrstCtrlAonKey0Out = 45,
    MioOutSysrstCtrlAonKey1Out = 46,
    MioOutSysrstCtrlAonKey2Out = 47,
    MioOutSysrstCtrlAonPwrbOut = 48,
    MioOutSysrstCtrlAonZ3Wakeup = 49,
    MioOutCount = 50
  } mio_out_e;

  // Enumeration for DIO signals, used on both the top and chip-levels.
  typedef enum int unsigned {
    DioSpiHost0Sd0 = 0,
    DioSpiHost0Sd1 = 1,
    DioSpiHost0Sd2 = 2,
    DioSpiHost0Sd3 = 3,
    DioSpiDeviceSd0 = 4,
    DioSpiDeviceSd1 = 5,
    DioSpiDeviceSd2 = 6,
    DioSpiDeviceSd3 = 7,
    DioSysrstCtrlAonEcRstL = 8,
    DioSysrstCtrlAonFlashWpL = 9,
    DioSpiDeviceSck = 10,
    DioSpiDeviceCsb = 11,
    DioSpiHost0Sck = 12,
    DioSpiHost0Csb = 13,
    DioCount = 14
  } dio_e;

  // Enumeration for the types of pads.
  typedef enum {
    MioPad,
    DioPad
  } pad_type_e;

  // Raw MIO/DIO input array indices on chip-level.
  // TODO: Does not account for target specific stubbed/added pads.
  // Need to make a target-specific package for those.
  typedef enum int unsigned {
    MioPadIoa0 = 0,
    MioPadIoa1 = 1,
    MioPadIoa2 = 2,
    MioPadIoa3 = 3,
    MioPadIoa4 = 4,
    MioPadIoa5 = 5,
    MioPadIoa6 = 6,
    MioPadIoa7 = 7,
    MioPadIoa8 = 8,
    MioPadIob0 = 9,
    MioPadIob1 = 10,
    MioPadIob2 = 11,
    MioPadIob3 = 12,
    MioPadIob4 = 13,
    MioPadIob5 = 14,
    MioPadIob6 = 15,
    MioPadIob7 = 16,
    MioPadIob8 = 17,
    MioPadIob9 = 18,
    MioPadIob10 = 19,
    MioPadIob11 = 20,
    MioPadIob12 = 21,
    MioPadIoc0 = 22,
    MioPadIoc1 = 23,
    MioPadIoc2 = 24,
    MioPadIoc3 = 25,
    MioPadIoc4 = 26,
    MioPadIoc5 = 27,
    MioPadIoc6 = 28,
    MioPadIoc7 = 29,
    MioPadIoc8 = 30,
    MioPadIoc9 = 31,
    MioPadIoc10 = 32,
    MioPadIoc11 = 33,
    MioPadIoc12 = 34,
    MioPadIor0 = 35,
    MioPadIor1 = 36,
    MioPadIor2 = 37,
    MioPadIor3 = 38,
    MioPadIor4 = 39,
    MioPadIor5 = 40,
    MioPadIor6 = 41,
    MioPadIor7 = 42,
    MioPadIor10 = 43,
    MioPadIor11 = 44,
    MioPadIor12 = 45,
    MioPadIor13 = 46,
    MioPadCount
  } mio_pad_e;

  typedef enum int unsigned {
    DioPadPorN = 0,
    DioPadCc1 = 1,
    DioPadCc2 = 2,
    DioPadFlashTestVolt = 3,
    DioPadFlashTestMode0 = 4,
    DioPadFlashTestMode1 = 5,
    DioPadOtpExtVolt = 6,
    DioPadSpiDevD0 = 7,
    DioPadSpiDevD1 = 8,
    DioPadSpiDevD2 = 9,
    DioPadSpiDevD3 = 10,
    DioPadSpiDevClk = 11,
    DioPadSpiDevCsL = 12,
    DioPadSpiHostD0 = 13,
    DioPadSpiHostD1 = 14,
    DioPadSpiHostD2 = 15,
    DioPadSpiHostD3 = 16,
    DioPadSpiHostClk = 17,
    DioPadSpiHostCsL = 18,
    DioPadIor8 = 19,
    DioPadIor9 = 20,
    DioPadCount
  } dio_pad_e;

  // List of peripheral instantiated in this chip.
  typedef enum {
    PeripheralAes,
    PeripheralAlertHandler,
    PeripheralAonTimerAon,
    PeripheralAst,
    PeripheralClkmgrAon,
    PeripheralCsrng,
    PeripheralEdn0,
    PeripheralEdn1,
    PeripheralEntropySrc,
    PeripheralFlashCtrl,
    PeripheralGpio,
    PeripheralHmac,
    PeripheralKeymgr,
    PeripheralKmac,
    PeripheralLcCtrl,
    PeripheralOtbn,
    PeripheralOtpCtrl,
    PeripheralPattgen,
    PeripheralPinmuxAon,
    PeripheralPwrmgrAon,
    PeripheralRomCtrl,
    PeripheralRstmgrAon,
    PeripheralRvCoreIbex,
    PeripheralRvDm,
    PeripheralRvPlic,
    PeripheralRvTimer,
    PeripheralSpiDevice,
    PeripheralSpiHost0,
    PeripheralSpiHost1,
    PeripheralSramCtrlMain,
    PeripheralSramCtrlRetAon,
    PeripheralSysrstCtrlAon,
    PeripheralTlul2axi,
    PeripheralCount
  } peripheral_e;

  // TODO: Enumeration for PLIC Interrupt source peripheral.
  // TODO: Enumeration for PLIC Interrupt Ids.

endpackage
