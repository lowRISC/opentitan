// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_englishbreakfast/data/top_englishbreakfast.hjson
//                -o hw/top_englishbreakfast/

package top_englishbreakfast_pkg;
  /**
   * Peripheral base address for uart0 in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_UART0_BASE_ADDR = 32'h40000000;

  /**
   * Peripheral size in bytes for uart0 in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_UART0_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for uart1 in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_UART1_BASE_ADDR = 32'h40010000;

  /**
   * Peripheral size in bytes for uart1 in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_UART1_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for gpio0 in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_GPIO0_BASE_ADDR = 32'h40040000;

  /**
   * Peripheral size in bytes for gpio0 in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_GPIO0_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for spi_device in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_SPI_DEVICE_BASE_ADDR = 32'h40050000;

  /**
   * Peripheral size in bytes for spi_device in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_SPI_DEVICE_SIZE_BYTES = 32'h2000;

  /**
   * Peripheral base address for spi_host0 in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_SPI_HOST0_BASE_ADDR = 32'h40060000;

  /**
   * Peripheral size in bytes for spi_host0 in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_SPI_HOST0_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for rv_timer in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_RV_TIMER_BASE_ADDR = 32'h40100000;

  /**
   * Peripheral size in bytes for rv_timer in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_RV_TIMER_SIZE_BYTES = 32'h200;

  /**
   * Peripheral base address for usbdev in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_USBDEV_BASE_ADDR = 32'h40320000;

  /**
   * Peripheral size in bytes for usbdev in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_USBDEV_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for pwrmgr in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_PWRMGR_BASE_ADDR = 32'h40400000;

  /**
   * Peripheral size in bytes for pwrmgr in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_PWRMGR_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for rstmgr in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_RSTMGR_BASE_ADDR = 32'h40410000;

  /**
   * Peripheral size in bytes for rstmgr in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_RSTMGR_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for clkmgr in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_CLKMGR_BASE_ADDR = 32'h40420000;

  /**
   * Peripheral size in bytes for clkmgr in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_CLKMGR_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for pinmux in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_PINMUX_BASE_ADDR = 32'h40460000;

  /**
   * Peripheral size in bytes for pinmux in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_PINMUX_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for aon_timer in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_AON_TIMER_BASE_ADDR = 32'h40470000;

  /**
   * Peripheral size in bytes for aon_timer in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_AON_TIMER_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for ast in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_AST_BASE_ADDR = 32'h40480000;

  /**
   * Peripheral size in bytes for ast in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_AST_SIZE_BYTES = 32'h400;

  /**
   * Peripheral base address for core device on flash_ctrl in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_FLASH_CTRL_CORE_BASE_ADDR = 32'h41000000;

  /**
   * Peripheral size in bytes for core device on flash_ctrl in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_FLASH_CTRL_CORE_SIZE_BYTES = 32'h200;

  /**
   * Peripheral base address for prim device on flash_ctrl in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_FLASH_CTRL_PRIM_BASE_ADDR = 32'h41008000;

  /**
   * Peripheral size in bytes for prim device on flash_ctrl in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_FLASH_CTRL_PRIM_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for rv_plic in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_RV_PLIC_BASE_ADDR = 32'h48000000;

  /**
   * Peripheral size in bytes for rv_plic in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_RV_PLIC_SIZE_BYTES = 32'h8000000;

  /**
   * Peripheral base address for aes in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_AES_BASE_ADDR = 32'h41100000;

  /**
   * Peripheral size in bytes for aes in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_AES_SIZE_BYTES = 32'h100;

  /**
   * Peripheral base address for regs device on sram_ctrl_main in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_SRAM_CTRL_MAIN_REGS_BASE_ADDR = 32'h411C0000;

  /**
   * Peripheral size in bytes for regs device on sram_ctrl_main in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_SRAM_CTRL_MAIN_REGS_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for regs device on rom_ctrl in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_ROM_CTRL_REGS_BASE_ADDR = 32'h411E0000;

  /**
   * Peripheral size in bytes for regs device on rom_ctrl in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_ROM_CTRL_REGS_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for cfg device on rv_core_ibex in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_RV_CORE_IBEX_CFG_BASE_ADDR = 32'h411F0000;

  /**
   * Peripheral size in bytes for cfg device on rv_core_ibex in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_RV_CORE_IBEX_CFG_SIZE_BYTES = 32'h100;

  /**
   * Memory base address for mem memory on flash_ctrl in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_FLASH_CTRL_MEM_BASE_ADDR = 32'h20000000;

  /**
   * Memory size for mem memory on flash_ctrl in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_FLASH_CTRL_MEM_SIZE_BYTES = 32'h10000;

  /**
   * Memory base address for ram memory on sram_ctrl_main in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_SRAM_CTRL_MAIN_RAM_BASE_ADDR = 32'h10000000;

  /**
   * Memory size for ram memory on sram_ctrl_main in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_SRAM_CTRL_MAIN_RAM_SIZE_BYTES = 32'h20000;

  /**
   * Memory base address for rom memory on rom_ctrl in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_ROM_CTRL_ROM_BASE_ADDR = 32'h8000;

  /**
   * Memory size for rom memory on rom_ctrl in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_ROM_CTRL_ROM_SIZE_BYTES = 32'h8000;


  // Number of englishbreakfast outgoing alerts
  parameter int unsigned NOutgoingAlertsEnglishbreakfast = 28;
  parameter int unsigned NOutgoingAlertsEnglishbreakfastPdAon = 6;
  parameter int unsigned NOutgoingAlertsEnglishbreakfastPdMain = 22;

  // Number of LPGs for outgoing alert group englishbreakfast
  parameter int unsigned NOutgoingLpgsEnglishbreakfast = 13;

  // Enumeration of englishbreakfast outgoing alert modules
  typedef enum int unsigned {
    TopEnglishbreakfastAlertPeripheralUart0 = 0,
    TopEnglishbreakfastAlertPeripheralUart1 = 1,
    TopEnglishbreakfastAlertPeripheralGpio0 = 2,
    TopEnglishbreakfastAlertPeripheralSpiDevice = 3,
    TopEnglishbreakfastAlertPeripheralSpiHost0 = 4,
    TopEnglishbreakfastAlertPeripheralRvTimer = 5,
    TopEnglishbreakfastAlertPeripheralUsbdev = 6,
    TopEnglishbreakfastAlertPeripheralPwrmgr = 7,
    TopEnglishbreakfastAlertPeripheralRstmgr = 8,
    TopEnglishbreakfastAlertPeripheralClkmgr = 9,
    TopEnglishbreakfastAlertPeripheralPinmux = 10,
    TopEnglishbreakfastAlertPeripheralAonTimer = 11,
    TopEnglishbreakfastAlertPeripheralFlashCtrl = 12,
    TopEnglishbreakfastAlertPeripheralRvPlic = 13,
    TopEnglishbreakfastAlertPeripheralAes = 14,
    TopEnglishbreakfastAlertPeripheralSramCtrlMain = 15,
    TopEnglishbreakfastAlertPeripheralRomCtrl = 16,
    TopEnglishbreakfastAlertPeripheralRvCoreIbex = 17,
    TopEnglishbreakfastOutgoingAlertEnglishbreakfastPeripheralCount
  } outgoing_alert_englishbreakfast_peripheral_e;

  // Enumeration of englishbreakfast outgoing alerts
  typedef enum int unsigned {
    TopEnglishbreakfastAlertIdUart0FatalFault = 0,
    TopEnglishbreakfastAlertIdUart1FatalFault = 1,
    TopEnglishbreakfastAlertIdGpio0FatalFault = 2,
    TopEnglishbreakfastAlertIdSpiDeviceFatalFault = 3,
    TopEnglishbreakfastAlertIdSpiHost0FatalFault = 4,
    TopEnglishbreakfastAlertIdRvTimerFatalFault = 5,
    TopEnglishbreakfastAlertIdUsbdevFatalFault = 6,
    TopEnglishbreakfastAlertIdPwrmgrFatalFault = 7,
    TopEnglishbreakfastAlertIdRstmgrFatalFault = 8,
    TopEnglishbreakfastAlertIdRstmgrFatalCnstyFault = 9,
    TopEnglishbreakfastAlertIdClkmgrRecovFault = 10,
    TopEnglishbreakfastAlertIdClkmgrFatalFault = 11,
    TopEnglishbreakfastAlertIdPinmuxFatalFault = 12,
    TopEnglishbreakfastAlertIdAonTimerFatalFault = 13,
    TopEnglishbreakfastAlertIdFlashCtrlRecovErr = 14,
    TopEnglishbreakfastAlertIdFlashCtrlFatalStdErr = 15,
    TopEnglishbreakfastAlertIdFlashCtrlFatalErr = 16,
    TopEnglishbreakfastAlertIdFlashCtrlFatalPrimFlashAlert = 17,
    TopEnglishbreakfastAlertIdFlashCtrlRecovPrimFlashAlert = 18,
    TopEnglishbreakfastAlertIdRvPlicFatalFault = 19,
    TopEnglishbreakfastAlertIdAesRecovCtrlUpdateErr = 20,
    TopEnglishbreakfastAlertIdAesFatalFault = 21,
    TopEnglishbreakfastAlertIdSramCtrlMainFatalError = 22,
    TopEnglishbreakfastAlertIdRomCtrlFatal = 23,
    TopEnglishbreakfastAlertIdRvCoreIbexFatalSwErr = 24,
    TopEnglishbreakfastAlertIdRvCoreIbexRecovSwErr = 25,
    TopEnglishbreakfastAlertIdRvCoreIbexFatalHwErr = 26,
    TopEnglishbreakfastAlertIdRvCoreIbexRecovHwErr = 27,
    TopEnglishbreakfastOutgoingAlertEnglishbreakfastIdCount
  } outgoing_alert_englishbreakfast_id_e;

  // Enumeration of englishbreakfast outgoing alerts AsyncOn configuration
  parameter logic [NOutgoingAlertsEnglishbreakfast-1:0] AsyncOnOutgoingAlertEnglishbreakfast = {
    1'b1,
    1'b1,
    1'b1,
    1'b1,
    1'b1,
    1'b1,
    1'b1,
    1'b1,
    1'b1,
    1'b1,
    1'b1,
    1'b1,
    1'b1,
    1'b1,
    1'b1,
    1'b1,
    1'b1,
    1'b1,
    1'b1,
    1'b1,
    1'b1,
    1'b1,
    1'b1,
    1'b1,
    1'b1,
    1'b1,
    1'b1,
    1'b1
  };

  // Enumeration of interrupts
  typedef enum int unsigned {
    TopEnglishbreakfastPlicIrqIdNone = 0,
    TopEnglishbreakfastPlicIrqIdUart0TxWatermark = 1,
    TopEnglishbreakfastPlicIrqIdUart0RxWatermark = 2,
    TopEnglishbreakfastPlicIrqIdUart0TxDone = 3,
    TopEnglishbreakfastPlicIrqIdUart0RxOverflow = 4,
    TopEnglishbreakfastPlicIrqIdUart0RxFrameErr = 5,
    TopEnglishbreakfastPlicIrqIdUart0RxBreakErr = 6,
    TopEnglishbreakfastPlicIrqIdUart0RxTimeout = 7,
    TopEnglishbreakfastPlicIrqIdUart0RxParityErr = 8,
    TopEnglishbreakfastPlicIrqIdUart0TxEmpty = 9,
    TopEnglishbreakfastPlicIrqIdUart1TxWatermark = 10,
    TopEnglishbreakfastPlicIrqIdUart1RxWatermark = 11,
    TopEnglishbreakfastPlicIrqIdUart1TxDone = 12,
    TopEnglishbreakfastPlicIrqIdUart1RxOverflow = 13,
    TopEnglishbreakfastPlicIrqIdUart1RxFrameErr = 14,
    TopEnglishbreakfastPlicIrqIdUart1RxBreakErr = 15,
    TopEnglishbreakfastPlicIrqIdUart1RxTimeout = 16,
    TopEnglishbreakfastPlicIrqIdUart1RxParityErr = 17,
    TopEnglishbreakfastPlicIrqIdUart1TxEmpty = 18,
    TopEnglishbreakfastPlicIrqIdGpio0Gpio0 = 19,
    TopEnglishbreakfastPlicIrqIdGpio0Gpio1 = 20,
    TopEnglishbreakfastPlicIrqIdGpio0Gpio2 = 21,
    TopEnglishbreakfastPlicIrqIdGpio0Gpio3 = 22,
    TopEnglishbreakfastPlicIrqIdGpio0Gpio4 = 23,
    TopEnglishbreakfastPlicIrqIdGpio0Gpio5 = 24,
    TopEnglishbreakfastPlicIrqIdGpio0Gpio6 = 25,
    TopEnglishbreakfastPlicIrqIdGpio0Gpio7 = 26,
    TopEnglishbreakfastPlicIrqIdGpio0Gpio8 = 27,
    TopEnglishbreakfastPlicIrqIdGpio0Gpio9 = 28,
    TopEnglishbreakfastPlicIrqIdGpio0Gpio10 = 29,
    TopEnglishbreakfastPlicIrqIdGpio0Gpio11 = 30,
    TopEnglishbreakfastPlicIrqIdGpio0Gpio12 = 31,
    TopEnglishbreakfastPlicIrqIdGpio0Gpio13 = 32,
    TopEnglishbreakfastPlicIrqIdGpio0Gpio14 = 33,
    TopEnglishbreakfastPlicIrqIdGpio0Gpio15 = 34,
    TopEnglishbreakfastPlicIrqIdGpio0Gpio16 = 35,
    TopEnglishbreakfastPlicIrqIdGpio0Gpio17 = 36,
    TopEnglishbreakfastPlicIrqIdGpio0Gpio18 = 37,
    TopEnglishbreakfastPlicIrqIdGpio0Gpio19 = 38,
    TopEnglishbreakfastPlicIrqIdGpio0Gpio20 = 39,
    TopEnglishbreakfastPlicIrqIdGpio0Gpio21 = 40,
    TopEnglishbreakfastPlicIrqIdGpio0Gpio22 = 41,
    TopEnglishbreakfastPlicIrqIdGpio0Gpio23 = 42,
    TopEnglishbreakfastPlicIrqIdGpio0Gpio24 = 43,
    TopEnglishbreakfastPlicIrqIdGpio0Gpio25 = 44,
    TopEnglishbreakfastPlicIrqIdGpio0Gpio26 = 45,
    TopEnglishbreakfastPlicIrqIdGpio0Gpio27 = 46,
    TopEnglishbreakfastPlicIrqIdGpio0Gpio28 = 47,
    TopEnglishbreakfastPlicIrqIdGpio0Gpio29 = 48,
    TopEnglishbreakfastPlicIrqIdGpio0Gpio30 = 49,
    TopEnglishbreakfastPlicIrqIdGpio0Gpio31 = 50,
    TopEnglishbreakfastPlicIrqIdSpiDeviceUploadCmdfifoNotEmpty = 51,
    TopEnglishbreakfastPlicIrqIdSpiDeviceUploadPayloadNotEmpty = 52,
    TopEnglishbreakfastPlicIrqIdSpiDeviceUploadPayloadOverflow = 53,
    TopEnglishbreakfastPlicIrqIdSpiDeviceReadbufWatermark = 54,
    TopEnglishbreakfastPlicIrqIdSpiDeviceReadbufFlip = 55,
    TopEnglishbreakfastPlicIrqIdSpiDeviceTpmHeaderNotEmpty = 56,
    TopEnglishbreakfastPlicIrqIdSpiDeviceTpmRdfifoCmdEnd = 57,
    TopEnglishbreakfastPlicIrqIdSpiDeviceTpmRdfifoDrop = 58,
    TopEnglishbreakfastPlicIrqIdSpiHost0Error = 59,
    TopEnglishbreakfastPlicIrqIdSpiHost0SpiEvent = 60,
    TopEnglishbreakfastPlicIrqIdUsbdevPktReceived = 61,
    TopEnglishbreakfastPlicIrqIdUsbdevPktSent = 62,
    TopEnglishbreakfastPlicIrqIdUsbdevDisconnected = 63,
    TopEnglishbreakfastPlicIrqIdUsbdevHostLost = 64,
    TopEnglishbreakfastPlicIrqIdUsbdevLinkReset = 65,
    TopEnglishbreakfastPlicIrqIdUsbdevLinkSuspend = 66,
    TopEnglishbreakfastPlicIrqIdUsbdevLinkResume = 67,
    TopEnglishbreakfastPlicIrqIdUsbdevAvOutEmpty = 68,
    TopEnglishbreakfastPlicIrqIdUsbdevRxFull = 69,
    TopEnglishbreakfastPlicIrqIdUsbdevAvOverflow = 70,
    TopEnglishbreakfastPlicIrqIdUsbdevLinkInErr = 71,
    TopEnglishbreakfastPlicIrqIdUsbdevRxCrcErr = 72,
    TopEnglishbreakfastPlicIrqIdUsbdevRxPidErr = 73,
    TopEnglishbreakfastPlicIrqIdUsbdevRxBitstuffErr = 74,
    TopEnglishbreakfastPlicIrqIdUsbdevFrame = 75,
    TopEnglishbreakfastPlicIrqIdUsbdevPowered = 76,
    TopEnglishbreakfastPlicIrqIdUsbdevLinkOutErr = 77,
    TopEnglishbreakfastPlicIrqIdUsbdevAvSetupEmpty = 78,
    TopEnglishbreakfastPlicIrqIdPwrmgrWakeup = 79,
    TopEnglishbreakfastPlicIrqIdAonTimerWkupTimerExpired = 80,
    TopEnglishbreakfastPlicIrqIdAonTimerWdogTimerBark = 81,
    TopEnglishbreakfastPlicIrqIdFlashCtrlProgEmpty = 82,
    TopEnglishbreakfastPlicIrqIdFlashCtrlProgLvl = 83,
    TopEnglishbreakfastPlicIrqIdFlashCtrlRdFull = 84,
    TopEnglishbreakfastPlicIrqIdFlashCtrlRdLvl = 85,
    TopEnglishbreakfastPlicIrqIdFlashCtrlOpDone = 86,
    TopEnglishbreakfastPlicIrqIdFlashCtrlCorrErr = 87,
    TopEnglishbreakfastPlicIrqIdCount
  } interrupt_rv_plic_id_e;


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
    MioInGpio0Gpio0 = 0,
    MioInGpio0Gpio1 = 1,
    MioInGpio0Gpio2 = 2,
    MioInGpio0Gpio3 = 3,
    MioInGpio0Gpio4 = 4,
    MioInGpio0Gpio5 = 5,
    MioInGpio0Gpio6 = 6,
    MioInGpio0Gpio7 = 7,
    MioInGpio0Gpio8 = 8,
    MioInGpio0Gpio9 = 9,
    MioInGpio0Gpio10 = 10,
    MioInGpio0Gpio11 = 11,
    MioInGpio0Gpio12 = 12,
    MioInGpio0Gpio13 = 13,
    MioInGpio0Gpio14 = 14,
    MioInGpio0Gpio15 = 15,
    MioInGpio0Gpio16 = 16,
    MioInGpio0Gpio17 = 17,
    MioInGpio0Gpio18 = 18,
    MioInGpio0Gpio19 = 19,
    MioInGpio0Gpio20 = 20,
    MioInGpio0Gpio21 = 21,
    MioInGpio0Gpio22 = 22,
    MioInGpio0Gpio23 = 23,
    MioInGpio0Gpio24 = 24,
    MioInGpio0Gpio25 = 25,
    MioInGpio0Gpio26 = 26,
    MioInGpio0Gpio27 = 27,
    MioInGpio0Gpio28 = 28,
    MioInGpio0Gpio29 = 29,
    MioInGpio0Gpio30 = 30,
    MioInGpio0Gpio31 = 31,
    MioInUart0Rx = 32,
    MioInUart1Rx = 33,
    MioInFlashCtrlTck = 34,
    MioInFlashCtrlTms = 35,
    MioInFlashCtrlTdi = 36,
    MioInUsbdevSense = 37,
    MioInCount = 38
  } mio_in_e;

  typedef enum {
    MioOutGpio0Gpio0 = 0,
    MioOutGpio0Gpio1 = 1,
    MioOutGpio0Gpio2 = 2,
    MioOutGpio0Gpio3 = 3,
    MioOutGpio0Gpio4 = 4,
    MioOutGpio0Gpio5 = 5,
    MioOutGpio0Gpio6 = 6,
    MioOutGpio0Gpio7 = 7,
    MioOutGpio0Gpio8 = 8,
    MioOutGpio0Gpio9 = 9,
    MioOutGpio0Gpio10 = 10,
    MioOutGpio0Gpio11 = 11,
    MioOutGpio0Gpio12 = 12,
    MioOutGpio0Gpio13 = 13,
    MioOutGpio0Gpio14 = 14,
    MioOutGpio0Gpio15 = 15,
    MioOutGpio0Gpio16 = 16,
    MioOutGpio0Gpio17 = 17,
    MioOutGpio0Gpio18 = 18,
    MioOutGpio0Gpio19 = 19,
    MioOutGpio0Gpio20 = 20,
    MioOutGpio0Gpio21 = 21,
    MioOutGpio0Gpio22 = 22,
    MioOutGpio0Gpio23 = 23,
    MioOutGpio0Gpio24 = 24,
    MioOutGpio0Gpio25 = 25,
    MioOutGpio0Gpio26 = 26,
    MioOutGpio0Gpio27 = 27,
    MioOutGpio0Gpio28 = 28,
    MioOutGpio0Gpio29 = 29,
    MioOutGpio0Gpio30 = 30,
    MioOutGpio0Gpio31 = 31,
    MioOutUart0Tx = 32,
    MioOutUart1Tx = 33,
    MioOutFlashCtrlTdo = 34,
    MioOutCount = 35
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
    DioUsbdevUsbDp = 8,
    DioUsbdevUsbDn = 9,
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
    DioPadUsbP = 1,
    DioPadUsbN = 2,
    DioPadCc1 = 3,
    DioPadCc2 = 4,
    DioPadFlashTestVolt = 5,
    DioPadFlashTestMode0 = 6,
    DioPadFlashTestMode1 = 7,
    DioPadSpiHostD0 = 8,
    DioPadSpiHostD1 = 9,
    DioPadSpiHostD2 = 10,
    DioPadSpiHostD3 = 11,
    DioPadSpiHostClk = 12,
    DioPadSpiHostCsL = 13,
    DioPadSpiDevD0 = 14,
    DioPadSpiDevD1 = 15,
    DioPadSpiDevD2 = 16,
    DioPadSpiDevD3 = 17,
    DioPadSpiDevClk = 18,
    DioPadSpiDevCsL = 19,
    DioPadCount
  } dio_pad_e;

  // List of peripheral instantiated in this chip.
  typedef enum {
    PeripheralAes,
    PeripheralAonTimer,
    PeripheralAst,
    PeripheralClkmgr,
    PeripheralFlashCtrl,
    PeripheralGpio0,
    PeripheralPinmux,
    PeripheralPwrmgr,
    PeripheralRomCtrl,
    PeripheralRstmgr,
    PeripheralRvCoreIbex,
    PeripheralRvPlic,
    PeripheralRvTimer,
    PeripheralSpiDevice,
    PeripheralSpiHost0,
    PeripheralSramCtrlMain,
    PeripheralUart0,
    PeripheralUart1,
    PeripheralUsbdev,
    PeripheralCount
  } peripheral_e;

  // MMIO Region
  //
  parameter int unsigned TOP_ENGLISHBREAKFAST_MMIO_BASE_ADDR = 32'h40000000;
  parameter int unsigned TOP_ENGLISHBREAKFAST_MMIO_SIZE_BYTES = 32'h10000000;

  // TODO: Enumeration for PLIC Interrupt source peripheral.

// MACROs for AST analog simulation support
`ifdef ANALOGSIM
  `define INOUT_AI input ast_pkg::awire_t
  `define INOUT_AO output ast_pkg::awire_t
`else
  `define INOUT_AI inout
  `define INOUT_AO inout
`endif

endpackage
