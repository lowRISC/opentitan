// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_englishbreakfast/data/top_englishbreakfast.hjson \
//                -o hw/top_englishbreakfast/ \
//                --rnd_cnst_seed \
//                47496257290787239787852990649372780135330843464066774986444696694703339830170

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
   * Peripheral base address for gpio in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_GPIO_BASE_ADDR = 32'h40040000;

  /**
   * Peripheral size in bytes for gpio in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_GPIO_SIZE_BYTES = 32'h80;

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
   * Peripheral base address for pwrmgr_aon in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_PWRMGR_AON_BASE_ADDR = 32'h40400000;

  /**
   * Peripheral size in bytes for pwrmgr_aon in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_PWRMGR_AON_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for rstmgr_aon in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_RSTMGR_AON_BASE_ADDR = 32'h40410000;

  /**
   * Peripheral size in bytes for rstmgr_aon in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_RSTMGR_AON_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for clkmgr_aon in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_CLKMGR_AON_BASE_ADDR = 32'h40420000;

  /**
   * Peripheral size in bytes for clkmgr_aon in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_CLKMGR_AON_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for pinmux_aon in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_PINMUX_AON_BASE_ADDR = 32'h40460000;

  /**
   * Peripheral size in bytes for pinmux_aon in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_PINMUX_AON_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for aon_timer_aon in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_AON_TIMER_AON_BASE_ADDR = 32'h40470000;

  /**
   * Peripheral size in bytes for aon_timer_aon in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_AON_TIMER_AON_SIZE_BYTES = 32'h40;

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
   * Peripheral base address for mem device on flash_ctrl in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_FLASH_CTRL_MEM_BASE_ADDR = 32'h20000000;

  /**
   * Peripheral size in bytes for mem device on flash_ctrl in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_FLASH_CTRL_MEM_SIZE_BYTES = 32'h10000;

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
   * Peripheral base address for ram device on sram_ctrl_main in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_SRAM_CTRL_MAIN_RAM_BASE_ADDR = 32'h10000000;

  /**
   * Peripheral size in bytes for ram device on sram_ctrl_main in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_SRAM_CTRL_MAIN_RAM_SIZE_BYTES = 32'h20000;

  /**
   * Peripheral base address for regs device on rom_ctrl in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_ROM_CTRL_REGS_BASE_ADDR = 32'h411E0000;

  /**
   * Peripheral size in bytes for regs device on rom_ctrl in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_ROM_CTRL_REGS_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for rom device on rom_ctrl in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_ROM_CTRL_ROM_BASE_ADDR = 32'h8000;

  /**
   * Peripheral size in bytes for rom device on rom_ctrl in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_ROM_CTRL_ROM_SIZE_BYTES = 32'h8000;

  /**
   * Peripheral base address for cfg device on rv_core_ibex in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_RV_CORE_IBEX_CFG_BASE_ADDR = 32'h411F0000;

  /**
   * Peripheral size in bytes for cfg device on rv_core_ibex in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_RV_CORE_IBEX_CFG_SIZE_BYTES = 32'h100;

  /**
   * Memory base address for eflash in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_EFLASH_BASE_ADDR = 32'h20000000;

  /**
   * Memory size for eflash in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_EFLASH_SIZE_BYTES = 32'h10000;

  /**
   * Memory base address for ram_main in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_RAM_MAIN_BASE_ADDR = 32'h10000000;

  /**
   * Memory size for ram_main in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_RAM_MAIN_SIZE_BYTES = 32'h20000;

  /**
   * Memory base address for rom in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_ROM_BASE_ADDR = 32'h8000;

  /**
   * Memory size for rom in top englishbreakfast.
   */
  parameter int unsigned TOP_ENGLISHBREAKFAST_ROM_SIZE_BYTES = 32'h8000;


  // Enumeration of interrupts
  typedef enum int unsigned {
    TopEnglishbreakfastIrqIdUart0TxWatermark = 1,
    TopEnglishbreakfastIrqIdUart0RxWatermark = 2,
    TopEnglishbreakfastIrqIdUart0TxDone = 3,
    TopEnglishbreakfastIrqIdUart0RxOverflow = 4,
    TopEnglishbreakfastIrqIdUart0RxFrameErr = 5,
    TopEnglishbreakfastIrqIdUart0RxBreakErr = 6,
    TopEnglishbreakfastIrqIdUart0RxTimeout = 7,
    TopEnglishbreakfastIrqIdUart0RxParityErr = 8,
    TopEnglishbreakfastIrqIdUart0TxEmpty = 9,
    TopEnglishbreakfastIrqIdUart1TxWatermark = 10,
    TopEnglishbreakfastIrqIdUart1RxWatermark = 11,
    TopEnglishbreakfastIrqIdUart1TxDone = 12,
    TopEnglishbreakfastIrqIdUart1RxOverflow = 13,
    TopEnglishbreakfastIrqIdUart1RxFrameErr = 14,
    TopEnglishbreakfastIrqIdUart1RxBreakErr = 15,
    TopEnglishbreakfastIrqIdUart1RxTimeout = 16,
    TopEnglishbreakfastIrqIdUart1RxParityErr = 17,
    TopEnglishbreakfastIrqIdUart1TxEmpty = 18,
    TopEnglishbreakfastIrqIdGpioGpio0 = 19,
    TopEnglishbreakfastIrqIdGpioGpio1 = 20,
    TopEnglishbreakfastIrqIdGpioGpio2 = 21,
    TopEnglishbreakfastIrqIdGpioGpio3 = 22,
    TopEnglishbreakfastIrqIdGpioGpio4 = 23,
    TopEnglishbreakfastIrqIdGpioGpio5 = 24,
    TopEnglishbreakfastIrqIdGpioGpio6 = 25,
    TopEnglishbreakfastIrqIdGpioGpio7 = 26,
    TopEnglishbreakfastIrqIdGpioGpio8 = 27,
    TopEnglishbreakfastIrqIdGpioGpio9 = 28,
    TopEnglishbreakfastIrqIdGpioGpio10 = 29,
    TopEnglishbreakfastIrqIdGpioGpio11 = 30,
    TopEnglishbreakfastIrqIdGpioGpio12 = 31,
    TopEnglishbreakfastIrqIdGpioGpio13 = 32,
    TopEnglishbreakfastIrqIdGpioGpio14 = 33,
    TopEnglishbreakfastIrqIdGpioGpio15 = 34,
    TopEnglishbreakfastIrqIdGpioGpio16 = 35,
    TopEnglishbreakfastIrqIdGpioGpio17 = 36,
    TopEnglishbreakfastIrqIdGpioGpio18 = 37,
    TopEnglishbreakfastIrqIdGpioGpio19 = 38,
    TopEnglishbreakfastIrqIdGpioGpio20 = 39,
    TopEnglishbreakfastIrqIdGpioGpio21 = 40,
    TopEnglishbreakfastIrqIdGpioGpio22 = 41,
    TopEnglishbreakfastIrqIdGpioGpio23 = 42,
    TopEnglishbreakfastIrqIdGpioGpio24 = 43,
    TopEnglishbreakfastIrqIdGpioGpio25 = 44,
    TopEnglishbreakfastIrqIdGpioGpio26 = 45,
    TopEnglishbreakfastIrqIdGpioGpio27 = 46,
    TopEnglishbreakfastIrqIdGpioGpio28 = 47,
    TopEnglishbreakfastIrqIdGpioGpio29 = 48,
    TopEnglishbreakfastIrqIdGpioGpio30 = 49,
    TopEnglishbreakfastIrqIdGpioGpio31 = 50,
    TopEnglishbreakfastIrqIdSpiDeviceUploadCmdfifoNotEmpty = 51,
    TopEnglishbreakfastIrqIdSpiDeviceUploadPayloadNotEmpty = 52,
    TopEnglishbreakfastIrqIdSpiDeviceUploadPayloadOverflow = 53,
    TopEnglishbreakfastIrqIdSpiDeviceReadbufWatermark = 54,
    TopEnglishbreakfastIrqIdSpiDeviceReadbufFlip = 55,
    TopEnglishbreakfastIrqIdSpiDeviceTpmHeaderNotEmpty = 56,
    TopEnglishbreakfastIrqIdSpiDeviceTpmRdfifoCmdEnd = 57,
    TopEnglishbreakfastIrqIdSpiDeviceTpmRdfifoDrop = 58,
    TopEnglishbreakfastIrqIdSpiHost0Error = 59,
    TopEnglishbreakfastIrqIdSpiHost0SpiEvent = 60,
    TopEnglishbreakfastIrqIdUsbdevPktReceived = 61,
    TopEnglishbreakfastIrqIdUsbdevPktSent = 62,
    TopEnglishbreakfastIrqIdUsbdevDisconnected = 63,
    TopEnglishbreakfastIrqIdUsbdevHostLost = 64,
    TopEnglishbreakfastIrqIdUsbdevLinkReset = 65,
    TopEnglishbreakfastIrqIdUsbdevLinkSuspend = 66,
    TopEnglishbreakfastIrqIdUsbdevLinkResume = 67,
    TopEnglishbreakfastIrqIdUsbdevAvOutEmpty = 68,
    TopEnglishbreakfastIrqIdUsbdevRxFull = 69,
    TopEnglishbreakfastIrqIdUsbdevAvOverflow = 70,
    TopEnglishbreakfastIrqIdUsbdevLinkInErr = 71,
    TopEnglishbreakfastIrqIdUsbdevRxCrcErr = 72,
    TopEnglishbreakfastIrqIdUsbdevRxPidErr = 73,
    TopEnglishbreakfastIrqIdUsbdevRxBitstuffErr = 74,
    TopEnglishbreakfastIrqIdUsbdevFrame = 75,
    TopEnglishbreakfastIrqIdUsbdevPowered = 76,
    TopEnglishbreakfastIrqIdUsbdevLinkOutErr = 77,
    TopEnglishbreakfastIrqIdUsbdevAvSetupEmpty = 78,
    TopEnglishbreakfastIrqIdPwrmgrAonWakeup = 79,
    TopEnglishbreakfastIrqIdAonTimerAonWkupTimerExpired = 80,
    TopEnglishbreakfastIrqIdAonTimerAonWdogTimerBark = 81,
    TopEnglishbreakfastIrqIdFlashCtrlProgEmpty = 82,
    TopEnglishbreakfastIrqIdFlashCtrlProgLvl = 83,
    TopEnglishbreakfastIrqIdFlashCtrlRdFull = 84,
    TopEnglishbreakfastIrqIdFlashCtrlRdLvl = 85,
    TopEnglishbreakfastIrqIdFlashCtrlOpDone = 86,
    TopEnglishbreakfastIrqIdFlashCtrlCorrErr = 87,
    TopEnglishbreakfastIrqIdCount
  } interrupt_id_e;

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
    MioInUart0Rx = 32,
    MioInUart1Rx = 33,
    MioInFlashCtrlTck = 34,
    MioInFlashCtrlTms = 35,
    MioInFlashCtrlTdi = 36,
    MioInUsbdevSense = 37,
    MioInCount = 38
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
    PeripheralAonTimerAon,
    PeripheralAst,
    PeripheralClkmgrAon,
    PeripheralFlashCtrl,
    PeripheralGpio,
    PeripheralPinmuxAon,
    PeripheralPwrmgrAon,
    PeripheralRomCtrl,
    PeripheralRstmgrAon,
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
