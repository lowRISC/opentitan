// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_verbano/data/top_verbano.hjson \
//                -o hw/top_verbano/

package top_verbano_pkg;
  /**
   * Peripheral base address for uart0 in top verbano.
   */
  parameter int unsigned TOP_VERBANO_UART0_BASE_ADDR = 32'h40000000;

  /**
   * Peripheral size in bytes for uart0 in top verbano.
   */
  parameter int unsigned TOP_VERBANO_UART0_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for uart1 in top verbano.
   */
  parameter int unsigned TOP_VERBANO_UART1_BASE_ADDR = 32'h40010000;

  /**
   * Peripheral size in bytes for uart1 in top verbano.
   */
  parameter int unsigned TOP_VERBANO_UART1_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for uart2 in top verbano.
   */
  parameter int unsigned TOP_VERBANO_UART2_BASE_ADDR = 32'h40020000;

  /**
   * Peripheral size in bytes for uart2 in top verbano.
   */
  parameter int unsigned TOP_VERBANO_UART2_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for uart3 in top verbano.
   */
  parameter int unsigned TOP_VERBANO_UART3_BASE_ADDR = 32'h40030000;

  /**
   * Peripheral size in bytes for uart3 in top verbano.
   */
  parameter int unsigned TOP_VERBANO_UART3_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for gpio in top verbano.
   */
  parameter int unsigned TOP_VERBANO_GPIO_BASE_ADDR = 32'h40040000;

  /**
   * Peripheral size in bytes for gpio in top verbano.
   */
  parameter int unsigned TOP_VERBANO_GPIO_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for spi_device in top verbano.
   */
  parameter int unsigned TOP_VERBANO_SPI_DEVICE_BASE_ADDR = 32'h40050000;

  /**
   * Peripheral size in bytes for spi_device in top verbano.
   */
  parameter int unsigned TOP_VERBANO_SPI_DEVICE_SIZE_BYTES = 32'h2000;

  /**
   * Peripheral base address for i2c0 in top verbano.
   */
  parameter int unsigned TOP_VERBANO_I2C0_BASE_ADDR = 32'h40080000;

  /**
   * Peripheral size in bytes for i2c0 in top verbano.
   */
  parameter int unsigned TOP_VERBANO_I2C0_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for i2c1 in top verbano.
   */
  parameter int unsigned TOP_VERBANO_I2C1_BASE_ADDR = 32'h40090000;

  /**
   * Peripheral size in bytes for i2c1 in top verbano.
   */
  parameter int unsigned TOP_VERBANO_I2C1_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for i2c2 in top verbano.
   */
  parameter int unsigned TOP_VERBANO_I2C2_BASE_ADDR = 32'h400A0000;

  /**
   * Peripheral size in bytes for i2c2 in top verbano.
   */
  parameter int unsigned TOP_VERBANO_I2C2_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for pattgen in top verbano.
   */
  parameter int unsigned TOP_VERBANO_PATTGEN_BASE_ADDR = 32'h400E0000;

  /**
   * Peripheral size in bytes for pattgen in top verbano.
   */
  parameter int unsigned TOP_VERBANO_PATTGEN_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for rv_timer in top verbano.
   */
  parameter int unsigned TOP_VERBANO_RV_TIMER_BASE_ADDR = 32'h40100000;

  /**
   * Peripheral size in bytes for rv_timer in top verbano.
   */
  parameter int unsigned TOP_VERBANO_RV_TIMER_SIZE_BYTES = 32'h200;

  /**
   * Peripheral base address for core device on otp_ctrl in top verbano.
   */
  parameter int unsigned TOP_VERBANO_OTP_CTRL_CORE_BASE_ADDR = 32'h40130000;

  /**
   * Peripheral size in bytes for core device on otp_ctrl in top verbano.
   */
  parameter int unsigned TOP_VERBANO_OTP_CTRL_CORE_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for prim device on otp_macro in top verbano.
   */
  parameter int unsigned TOP_VERBANO_OTP_MACRO_PRIM_BASE_ADDR = 32'h40138000;

  /**
   * Peripheral size in bytes for prim device on otp_macro in top verbano.
   */
  parameter int unsigned TOP_VERBANO_OTP_MACRO_PRIM_SIZE_BYTES = 32'h20;

  /**
   * Peripheral base address for regs device on lc_ctrl in top verbano.
   */
  parameter int unsigned TOP_VERBANO_LC_CTRL_REGS_BASE_ADDR = 32'h40140000;

  /**
   * Peripheral size in bytes for regs device on lc_ctrl in top verbano.
   */
  parameter int unsigned TOP_VERBANO_LC_CTRL_REGS_SIZE_BYTES = 32'h100;

  /**
   * Peripheral base address for dmi device on lc_ctrl in top verbano.
   */
  parameter int unsigned TOP_VERBANO_LC_CTRL_DMI_BASE_ADDR = 32'h0;

  /**
   * Peripheral size in bytes for dmi device on lc_ctrl in top verbano.
   */
  parameter int unsigned TOP_VERBANO_LC_CTRL_DMI_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for alert_handler in top verbano.
   */
  parameter int unsigned TOP_VERBANO_ALERT_HANDLER_BASE_ADDR = 32'h40150000;

  /**
   * Peripheral size in bytes for alert_handler in top verbano.
   */
  parameter int unsigned TOP_VERBANO_ALERT_HANDLER_SIZE_BYTES = 32'h800;

  /**
   * Peripheral base address for spi_host0 in top verbano.
   */
  parameter int unsigned TOP_VERBANO_SPI_HOST0_BASE_ADDR = 32'h40300000;

  /**
   * Peripheral size in bytes for spi_host0 in top verbano.
   */
  parameter int unsigned TOP_VERBANO_SPI_HOST0_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for spi_host1 in top verbano.
   */
  parameter int unsigned TOP_VERBANO_SPI_HOST1_BASE_ADDR = 32'h40310000;

  /**
   * Peripheral size in bytes for spi_host1 in top verbano.
   */
  parameter int unsigned TOP_VERBANO_SPI_HOST1_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for usbdev in top verbano.
   */
  parameter int unsigned TOP_VERBANO_USBDEV_BASE_ADDR = 32'h40320000;

  /**
   * Peripheral size in bytes for usbdev in top verbano.
   */
  parameter int unsigned TOP_VERBANO_USBDEV_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for pwrmgr_aon in top verbano.
   */
  parameter int unsigned TOP_VERBANO_PWRMGR_AON_BASE_ADDR = 32'h40400000;

  /**
   * Peripheral size in bytes for pwrmgr_aon in top verbano.
   */
  parameter int unsigned TOP_VERBANO_PWRMGR_AON_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for rstmgr_aon in top verbano.
   */
  parameter int unsigned TOP_VERBANO_RSTMGR_AON_BASE_ADDR = 32'h40410000;

  /**
   * Peripheral size in bytes for rstmgr_aon in top verbano.
   */
  parameter int unsigned TOP_VERBANO_RSTMGR_AON_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for clkmgr_aon in top verbano.
   */
  parameter int unsigned TOP_VERBANO_CLKMGR_AON_BASE_ADDR = 32'h40420000;

  /**
   * Peripheral size in bytes for clkmgr_aon in top verbano.
   */
  parameter int unsigned TOP_VERBANO_CLKMGR_AON_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for sysrst_ctrl_aon in top verbano.
   */
  parameter int unsigned TOP_VERBANO_SYSRST_CTRL_AON_BASE_ADDR = 32'h40430000;

  /**
   * Peripheral size in bytes for sysrst_ctrl_aon in top verbano.
   */
  parameter int unsigned TOP_VERBANO_SYSRST_CTRL_AON_SIZE_BYTES = 32'h100;

  /**
   * Peripheral base address for adc_ctrl_aon in top verbano.
   */
  parameter int unsigned TOP_VERBANO_ADC_CTRL_AON_BASE_ADDR = 32'h40440000;

  /**
   * Peripheral size in bytes for adc_ctrl_aon in top verbano.
   */
  parameter int unsigned TOP_VERBANO_ADC_CTRL_AON_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for pwm_aon in top verbano.
   */
  parameter int unsigned TOP_VERBANO_PWM_AON_BASE_ADDR = 32'h40450000;

  /**
   * Peripheral size in bytes for pwm_aon in top verbano.
   */
  parameter int unsigned TOP_VERBANO_PWM_AON_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for pinmux_aon in top verbano.
   */
  parameter int unsigned TOP_VERBANO_PINMUX_AON_BASE_ADDR = 32'h40460000;

  /**
   * Peripheral size in bytes for pinmux_aon in top verbano.
   */
  parameter int unsigned TOP_VERBANO_PINMUX_AON_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for aon_timer_aon in top verbano.
   */
  parameter int unsigned TOP_VERBANO_AON_TIMER_AON_BASE_ADDR = 32'h40470000;

  /**
   * Peripheral size in bytes for aon_timer_aon in top verbano.
   */
  parameter int unsigned TOP_VERBANO_AON_TIMER_AON_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for ast in top verbano.
   */
  parameter int unsigned TOP_VERBANO_AST_BASE_ADDR = 32'h40480000;

  /**
   * Peripheral size in bytes for ast in top verbano.
   */
  parameter int unsigned TOP_VERBANO_AST_SIZE_BYTES = 32'h400;

  /**
   * Peripheral base address for sensor_ctrl_aon in top verbano.
   */
  parameter int unsigned TOP_VERBANO_SENSOR_CTRL_AON_BASE_ADDR = 32'h40490000;

  /**
   * Peripheral size in bytes for sensor_ctrl_aon in top verbano.
   */
  parameter int unsigned TOP_VERBANO_SENSOR_CTRL_AON_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for regs device on sram_ctrl_ret_aon in top verbano.
   */
  parameter int unsigned TOP_VERBANO_SRAM_CTRL_RET_AON_REGS_BASE_ADDR = 32'h40500000;

  /**
   * Peripheral size in bytes for regs device on sram_ctrl_ret_aon in top verbano.
   */
  parameter int unsigned TOP_VERBANO_SRAM_CTRL_RET_AON_REGS_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for ram device on sram_ctrl_ret_aon in top verbano.
   */
  parameter int unsigned TOP_VERBANO_SRAM_CTRL_RET_AON_RAM_BASE_ADDR = 32'h40600000;

  /**
   * Peripheral size in bytes for ram device on sram_ctrl_ret_aon in top verbano.
   */
  parameter int unsigned TOP_VERBANO_SRAM_CTRL_RET_AON_RAM_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for core device on flash_ctrl in top verbano.
   */
  parameter int unsigned TOP_VERBANO_FLASH_CTRL_CORE_BASE_ADDR = 32'h41000000;

  /**
   * Peripheral size in bytes for core device on flash_ctrl in top verbano.
   */
  parameter int unsigned TOP_VERBANO_FLASH_CTRL_CORE_SIZE_BYTES = 32'h200;

  /**
   * Peripheral base address for prim device on flash_ctrl in top verbano.
   */
  parameter int unsigned TOP_VERBANO_FLASH_CTRL_PRIM_BASE_ADDR = 32'h41008000;

  /**
   * Peripheral size in bytes for prim device on flash_ctrl in top verbano.
   */
  parameter int unsigned TOP_VERBANO_FLASH_CTRL_PRIM_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for mem device on flash_ctrl in top verbano.
   */
  parameter int unsigned TOP_VERBANO_FLASH_CTRL_MEM_BASE_ADDR = 32'h20000000;

  /**
   * Peripheral size in bytes for mem device on flash_ctrl in top verbano.
   */
  parameter int unsigned TOP_VERBANO_FLASH_CTRL_MEM_SIZE_BYTES = 32'h100000;

  /**
   * Peripheral base address for regs device on rv_dm in top verbano.
   */
  parameter int unsigned TOP_VERBANO_RV_DM_REGS_BASE_ADDR = 32'h41200000;

  /**
   * Peripheral size in bytes for regs device on rv_dm in top verbano.
   */
  parameter int unsigned TOP_VERBANO_RV_DM_REGS_SIZE_BYTES = 32'h10;

  /**
   * Peripheral base address for mem device on rv_dm in top verbano.
   */
  parameter int unsigned TOP_VERBANO_RV_DM_MEM_BASE_ADDR = 32'h10000;

  /**
   * Peripheral size in bytes for mem device on rv_dm in top verbano.
   */
  parameter int unsigned TOP_VERBANO_RV_DM_MEM_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for dbg device on rv_dm in top verbano.
   */
  parameter int unsigned TOP_VERBANO_RV_DM_DBG_BASE_ADDR = 32'h1000;

  /**
   * Peripheral size in bytes for dbg device on rv_dm in top verbano.
   */
  parameter int unsigned TOP_VERBANO_RV_DM_DBG_SIZE_BYTES = 32'h200;

  /**
   * Peripheral base address for rv_plic in top verbano.
   */
  parameter int unsigned TOP_VERBANO_RV_PLIC_BASE_ADDR = 32'h48000000;

  /**
   * Peripheral size in bytes for rv_plic in top verbano.
   */
  parameter int unsigned TOP_VERBANO_RV_PLIC_SIZE_BYTES = 32'h8000000;

  /**
   * Peripheral base address for aes in top verbano.
   */
  parameter int unsigned TOP_VERBANO_AES_BASE_ADDR = 32'h41100000;

  /**
   * Peripheral size in bytes for aes in top verbano.
   */
  parameter int unsigned TOP_VERBANO_AES_SIZE_BYTES = 32'h100;

  /**
   * Peripheral base address for hmac in top verbano.
   */
  parameter int unsigned TOP_VERBANO_HMAC_BASE_ADDR = 32'h41110000;

  /**
   * Peripheral size in bytes for hmac in top verbano.
   */
  parameter int unsigned TOP_VERBANO_HMAC_SIZE_BYTES = 32'h2000;

  /**
   * Peripheral base address for kmac in top verbano.
   */
  parameter int unsigned TOP_VERBANO_KMAC_BASE_ADDR = 32'h41120000;

  /**
   * Peripheral size in bytes for kmac in top verbano.
   */
  parameter int unsigned TOP_VERBANO_KMAC_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for otbn in top verbano.
   */
  parameter int unsigned TOP_VERBANO_OTBN_BASE_ADDR = 32'h41130000;

  /**
   * Peripheral size in bytes for otbn in top verbano.
   */
  parameter int unsigned TOP_VERBANO_OTBN_SIZE_BYTES = 32'h10000;

  /**
   * Peripheral base address for keymgr in top verbano.
   */
  parameter int unsigned TOP_VERBANO_KEYMGR_BASE_ADDR = 32'h41140000;

  /**
   * Peripheral size in bytes for keymgr in top verbano.
   */
  parameter int unsigned TOP_VERBANO_KEYMGR_SIZE_BYTES = 32'h100;

  /**
   * Peripheral base address for csrng in top verbano.
   */
  parameter int unsigned TOP_VERBANO_CSRNG_BASE_ADDR = 32'h41150000;

  /**
   * Peripheral size in bytes for csrng in top verbano.
   */
  parameter int unsigned TOP_VERBANO_CSRNG_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for entropy_src in top verbano.
   */
  parameter int unsigned TOP_VERBANO_ENTROPY_SRC_BASE_ADDR = 32'h41160000;

  /**
   * Peripheral size in bytes for entropy_src in top verbano.
   */
  parameter int unsigned TOP_VERBANO_ENTROPY_SRC_SIZE_BYTES = 32'h100;

  /**
   * Peripheral base address for edn0 in top verbano.
   */
  parameter int unsigned TOP_VERBANO_EDN0_BASE_ADDR = 32'h41170000;

  /**
   * Peripheral size in bytes for edn0 in top verbano.
   */
  parameter int unsigned TOP_VERBANO_EDN0_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for edn1 in top verbano.
   */
  parameter int unsigned TOP_VERBANO_EDN1_BASE_ADDR = 32'h41180000;

  /**
   * Peripheral size in bytes for edn1 in top verbano.
   */
  parameter int unsigned TOP_VERBANO_EDN1_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for regs device on sram_ctrl_main in top verbano.
   */
  parameter int unsigned TOP_VERBANO_SRAM_CTRL_MAIN_REGS_BASE_ADDR = 32'h411C0000;

  /**
   * Peripheral size in bytes for regs device on sram_ctrl_main in top verbano.
   */
  parameter int unsigned TOP_VERBANO_SRAM_CTRL_MAIN_REGS_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for ram device on sram_ctrl_main in top verbano.
   */
  parameter int unsigned TOP_VERBANO_SRAM_CTRL_MAIN_RAM_BASE_ADDR = 32'h10000000;

  /**
   * Peripheral size in bytes for ram device on sram_ctrl_main in top verbano.
   */
  parameter int unsigned TOP_VERBANO_SRAM_CTRL_MAIN_RAM_SIZE_BYTES = 32'h20000;

  /**
   * Peripheral base address for regs device on rom_ctrl in top verbano.
   */
  parameter int unsigned TOP_VERBANO_ROM_CTRL_REGS_BASE_ADDR = 32'h411E0000;

  /**
   * Peripheral size in bytes for regs device on rom_ctrl in top verbano.
   */
  parameter int unsigned TOP_VERBANO_ROM_CTRL_REGS_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for rom device on rom_ctrl in top verbano.
   */
  parameter int unsigned TOP_VERBANO_ROM_CTRL_ROM_BASE_ADDR = 32'h8000;

  /**
   * Peripheral size in bytes for rom device on rom_ctrl in top verbano.
   */
  parameter int unsigned TOP_VERBANO_ROM_CTRL_ROM_SIZE_BYTES = 32'h8000;

  /**
   * Peripheral base address for cfg device on rv_core_ibex in top verbano.
   */
  parameter int unsigned TOP_VERBANO_RV_CORE_IBEX_CFG_BASE_ADDR = 32'h411F0000;

  /**
   * Peripheral size in bytes for cfg device on rv_core_ibex in top verbano.
   */
  parameter int unsigned TOP_VERBANO_RV_CORE_IBEX_CFG_SIZE_BYTES = 32'h100;

  /**
   * Memory base address for ram_ret_aon in top verbano.
   */
  parameter int unsigned TOP_VERBANO_RAM_RET_AON_BASE_ADDR = 32'h40600000;

  /**
   * Memory size for ram_ret_aon in top verbano.
   */
  parameter int unsigned TOP_VERBANO_RAM_RET_AON_SIZE_BYTES = 32'h1000;

  /**
   * Memory base address for eflash in top verbano.
   */
  parameter int unsigned TOP_VERBANO_EFLASH_BASE_ADDR = 32'h20000000;

  /**
   * Memory size for eflash in top verbano.
   */
  parameter int unsigned TOP_VERBANO_EFLASH_SIZE_BYTES = 32'h100000;

  /**
   * Memory base address for ram_main in top verbano.
   */
  parameter int unsigned TOP_VERBANO_RAM_MAIN_BASE_ADDR = 32'h10000000;

  /**
   * Memory size for ram_main in top verbano.
   */
  parameter int unsigned TOP_VERBANO_RAM_MAIN_SIZE_BYTES = 32'h20000;

  /**
   * Memory base address for rom in top verbano.
   */
  parameter int unsigned TOP_VERBANO_ROM_BASE_ADDR = 32'h8000;

  /**
   * Memory size for rom in top verbano.
   */
  parameter int unsigned TOP_VERBANO_ROM_SIZE_BYTES = 32'h8000;


  // Enumeration of alert modules
  typedef enum int unsigned {
    TopVerbanoAlertPeripheralUart0 = 0,
    TopVerbanoAlertPeripheralUart1 = 1,
    TopVerbanoAlertPeripheralUart2 = 2,
    TopVerbanoAlertPeripheralUart3 = 3,
    TopVerbanoAlertPeripheralGpio = 4,
    TopVerbanoAlertPeripheralSpiDevice = 5,
    TopVerbanoAlertPeripheralI2c0 = 6,
    TopVerbanoAlertPeripheralI2c1 = 7,
    TopVerbanoAlertPeripheralI2c2 = 8,
    TopVerbanoAlertPeripheralPattgen = 9,
    TopVerbanoAlertPeripheralRvTimer = 10,
    TopVerbanoAlertPeripheralOtpCtrl = 11,
    TopVerbanoAlertPeripheralLcCtrl = 12,
    TopVerbanoAlertPeripheralSpiHost0 = 13,
    TopVerbanoAlertPeripheralSpiHost1 = 14,
    TopVerbanoAlertPeripheralUsbdev = 15,
    TopVerbanoAlertPeripheralPwrmgrAon = 16,
    TopVerbanoAlertPeripheralRstmgrAon = 17,
    TopVerbanoAlertPeripheralClkmgrAon = 18,
    TopVerbanoAlertPeripheralSysrstCtrlAon = 19,
    TopVerbanoAlertPeripheralAdcCtrlAon = 20,
    TopVerbanoAlertPeripheralPwmAon = 21,
    TopVerbanoAlertPeripheralPinmuxAon = 22,
    TopVerbanoAlertPeripheralAonTimerAon = 23,
    TopVerbanoAlertPeripheralSensorCtrlAon = 24,
    TopVerbanoAlertPeripheralSramCtrlRetAon = 25,
    TopVerbanoAlertPeripheralFlashCtrl = 26,
    TopVerbanoAlertPeripheralRvDm = 27,
    TopVerbanoAlertPeripheralRvPlic = 28,
    TopVerbanoAlertPeripheralAes = 29,
    TopVerbanoAlertPeripheralHmac = 30,
    TopVerbanoAlertPeripheralKmac = 31,
    TopVerbanoAlertPeripheralOtbn = 32,
    TopVerbanoAlertPeripheralKeymgr = 33,
    TopVerbanoAlertPeripheralCsrng = 34,
    TopVerbanoAlertPeripheralEntropySrc = 35,
    TopVerbanoAlertPeripheralEdn0 = 36,
    TopVerbanoAlertPeripheralEdn1 = 37,
    TopVerbanoAlertPeripheralSramCtrlMain = 38,
    TopVerbanoAlertPeripheralRomCtrl = 39,
    TopVerbanoAlertPeripheralRvCoreIbex = 40,
    TopVerbanoAlertPeripheralCount
  } alert_peripheral_e;

  // Enumeration of alerts
  typedef enum int unsigned {
    TopVerbanoAlertIdUart0FatalFault = 0,
    TopVerbanoAlertIdUart1FatalFault = 1,
    TopVerbanoAlertIdUart2FatalFault = 2,
    TopVerbanoAlertIdUart3FatalFault = 3,
    TopVerbanoAlertIdGpioFatalFault = 4,
    TopVerbanoAlertIdSpiDeviceFatalFault = 5,
    TopVerbanoAlertIdI2c0FatalFault = 6,
    TopVerbanoAlertIdI2c1FatalFault = 7,
    TopVerbanoAlertIdI2c2FatalFault = 8,
    TopVerbanoAlertIdPattgenFatalFault = 9,
    TopVerbanoAlertIdRvTimerFatalFault = 10,
    TopVerbanoAlertIdOtpCtrlFatalMacroError = 11,
    TopVerbanoAlertIdOtpCtrlFatalCheckError = 12,
    TopVerbanoAlertIdOtpCtrlFatalBusIntegError = 13,
    TopVerbanoAlertIdOtpCtrlFatalPrimOtpAlert = 14,
    TopVerbanoAlertIdOtpCtrlRecovPrimOtpAlert = 15,
    TopVerbanoAlertIdLcCtrlFatalProgError = 16,
    TopVerbanoAlertIdLcCtrlFatalStateError = 17,
    TopVerbanoAlertIdLcCtrlFatalBusIntegError = 18,
    TopVerbanoAlertIdSpiHost0FatalFault = 19,
    TopVerbanoAlertIdSpiHost1FatalFault = 20,
    TopVerbanoAlertIdUsbdevFatalFault = 21,
    TopVerbanoAlertIdPwrmgrAonFatalFault = 22,
    TopVerbanoAlertIdRstmgrAonFatalFault = 23,
    TopVerbanoAlertIdRstmgrAonFatalCnstyFault = 24,
    TopVerbanoAlertIdClkmgrAonRecovFault = 25,
    TopVerbanoAlertIdClkmgrAonFatalFault = 26,
    TopVerbanoAlertIdSysrstCtrlAonFatalFault = 27,
    TopVerbanoAlertIdAdcCtrlAonFatalFault = 28,
    TopVerbanoAlertIdPwmAonFatalFault = 29,
    TopVerbanoAlertIdPinmuxAonFatalFault = 30,
    TopVerbanoAlertIdAonTimerAonFatalFault = 31,
    TopVerbanoAlertIdSensorCtrlAonRecovAlert = 32,
    TopVerbanoAlertIdSensorCtrlAonFatalAlert = 33,
    TopVerbanoAlertIdSramCtrlRetAonFatalError = 34,
    TopVerbanoAlertIdFlashCtrlRecovErr = 35,
    TopVerbanoAlertIdFlashCtrlFatalStdErr = 36,
    TopVerbanoAlertIdFlashCtrlFatalErr = 37,
    TopVerbanoAlertIdFlashCtrlFatalPrimFlashAlert = 38,
    TopVerbanoAlertIdFlashCtrlRecovPrimFlashAlert = 39,
    TopVerbanoAlertIdRvDmFatalFault = 40,
    TopVerbanoAlertIdRvPlicFatalFault = 41,
    TopVerbanoAlertIdAesRecovCtrlUpdateErr = 42,
    TopVerbanoAlertIdAesFatalFault = 43,
    TopVerbanoAlertIdHmacFatalFault = 44,
    TopVerbanoAlertIdKmacRecovOperationErr = 45,
    TopVerbanoAlertIdKmacFatalFaultErr = 46,
    TopVerbanoAlertIdOtbnFatal = 47,
    TopVerbanoAlertIdOtbnRecov = 48,
    TopVerbanoAlertIdKeymgrRecovOperationErr = 49,
    TopVerbanoAlertIdKeymgrFatalFaultErr = 50,
    TopVerbanoAlertIdCsrngRecovAlert = 51,
    TopVerbanoAlertIdCsrngFatalAlert = 52,
    TopVerbanoAlertIdEntropySrcRecovAlert = 53,
    TopVerbanoAlertIdEntropySrcFatalAlert = 54,
    TopVerbanoAlertIdEdn0RecovAlert = 55,
    TopVerbanoAlertIdEdn0FatalAlert = 56,
    TopVerbanoAlertIdEdn1RecovAlert = 57,
    TopVerbanoAlertIdEdn1FatalAlert = 58,
    TopVerbanoAlertIdSramCtrlMainFatalError = 59,
    TopVerbanoAlertIdRomCtrlFatal = 60,
    TopVerbanoAlertIdRvCoreIbexFatalSwErr = 61,
    TopVerbanoAlertIdRvCoreIbexRecovSwErr = 62,
    TopVerbanoAlertIdRvCoreIbexFatalHwErr = 63,
    TopVerbanoAlertIdRvCoreIbexRecovHwErr = 64,
    TopVerbanoAlertIdCount
  } alert_id_e;

  // Enumeration of interrupts
  typedef enum int unsigned {
    TopVerbanoPlicIrqIdNone = 0,
    TopVerbanoPlicIrqIdUart0TxWatermark = 1,
    TopVerbanoPlicIrqIdUart0RxWatermark = 2,
    TopVerbanoPlicIrqIdUart0TxDone = 3,
    TopVerbanoPlicIrqIdUart0RxOverflow = 4,
    TopVerbanoPlicIrqIdUart0RxFrameErr = 5,
    TopVerbanoPlicIrqIdUart0RxBreakErr = 6,
    TopVerbanoPlicIrqIdUart0RxTimeout = 7,
    TopVerbanoPlicIrqIdUart0RxParityErr = 8,
    TopVerbanoPlicIrqIdUart0TxEmpty = 9,
    TopVerbanoPlicIrqIdUart1TxWatermark = 10,
    TopVerbanoPlicIrqIdUart1RxWatermark = 11,
    TopVerbanoPlicIrqIdUart1TxDone = 12,
    TopVerbanoPlicIrqIdUart1RxOverflow = 13,
    TopVerbanoPlicIrqIdUart1RxFrameErr = 14,
    TopVerbanoPlicIrqIdUart1RxBreakErr = 15,
    TopVerbanoPlicIrqIdUart1RxTimeout = 16,
    TopVerbanoPlicIrqIdUart1RxParityErr = 17,
    TopVerbanoPlicIrqIdUart1TxEmpty = 18,
    TopVerbanoPlicIrqIdUart2TxWatermark = 19,
    TopVerbanoPlicIrqIdUart2RxWatermark = 20,
    TopVerbanoPlicIrqIdUart2TxDone = 21,
    TopVerbanoPlicIrqIdUart2RxOverflow = 22,
    TopVerbanoPlicIrqIdUart2RxFrameErr = 23,
    TopVerbanoPlicIrqIdUart2RxBreakErr = 24,
    TopVerbanoPlicIrqIdUart2RxTimeout = 25,
    TopVerbanoPlicIrqIdUart2RxParityErr = 26,
    TopVerbanoPlicIrqIdUart2TxEmpty = 27,
    TopVerbanoPlicIrqIdUart3TxWatermark = 28,
    TopVerbanoPlicIrqIdUart3RxWatermark = 29,
    TopVerbanoPlicIrqIdUart3TxDone = 30,
    TopVerbanoPlicIrqIdUart3RxOverflow = 31,
    TopVerbanoPlicIrqIdUart3RxFrameErr = 32,
    TopVerbanoPlicIrqIdUart3RxBreakErr = 33,
    TopVerbanoPlicIrqIdUart3RxTimeout = 34,
    TopVerbanoPlicIrqIdUart3RxParityErr = 35,
    TopVerbanoPlicIrqIdUart3TxEmpty = 36,
    TopVerbanoPlicIrqIdGpioGpio0 = 37,
    TopVerbanoPlicIrqIdGpioGpio1 = 38,
    TopVerbanoPlicIrqIdGpioGpio2 = 39,
    TopVerbanoPlicIrqIdGpioGpio3 = 40,
    TopVerbanoPlicIrqIdGpioGpio4 = 41,
    TopVerbanoPlicIrqIdGpioGpio5 = 42,
    TopVerbanoPlicIrqIdGpioGpio6 = 43,
    TopVerbanoPlicIrqIdGpioGpio7 = 44,
    TopVerbanoPlicIrqIdGpioGpio8 = 45,
    TopVerbanoPlicIrqIdGpioGpio9 = 46,
    TopVerbanoPlicIrqIdGpioGpio10 = 47,
    TopVerbanoPlicIrqIdGpioGpio11 = 48,
    TopVerbanoPlicIrqIdGpioGpio12 = 49,
    TopVerbanoPlicIrqIdGpioGpio13 = 50,
    TopVerbanoPlicIrqIdGpioGpio14 = 51,
    TopVerbanoPlicIrqIdGpioGpio15 = 52,
    TopVerbanoPlicIrqIdGpioGpio16 = 53,
    TopVerbanoPlicIrqIdGpioGpio17 = 54,
    TopVerbanoPlicIrqIdGpioGpio18 = 55,
    TopVerbanoPlicIrqIdGpioGpio19 = 56,
    TopVerbanoPlicIrqIdGpioGpio20 = 57,
    TopVerbanoPlicIrqIdGpioGpio21 = 58,
    TopVerbanoPlicIrqIdGpioGpio22 = 59,
    TopVerbanoPlicIrqIdGpioGpio23 = 60,
    TopVerbanoPlicIrqIdGpioGpio24 = 61,
    TopVerbanoPlicIrqIdGpioGpio25 = 62,
    TopVerbanoPlicIrqIdGpioGpio26 = 63,
    TopVerbanoPlicIrqIdGpioGpio27 = 64,
    TopVerbanoPlicIrqIdGpioGpio28 = 65,
    TopVerbanoPlicIrqIdGpioGpio29 = 66,
    TopVerbanoPlicIrqIdGpioGpio30 = 67,
    TopVerbanoPlicIrqIdGpioGpio31 = 68,
    TopVerbanoPlicIrqIdSpiDeviceUploadCmdfifoNotEmpty = 69,
    TopVerbanoPlicIrqIdSpiDeviceUploadPayloadNotEmpty = 70,
    TopVerbanoPlicIrqIdSpiDeviceUploadPayloadOverflow = 71,
    TopVerbanoPlicIrqIdSpiDeviceReadbufWatermark = 72,
    TopVerbanoPlicIrqIdSpiDeviceReadbufFlip = 73,
    TopVerbanoPlicIrqIdSpiDeviceTpmHeaderNotEmpty = 74,
    TopVerbanoPlicIrqIdSpiDeviceTpmRdfifoCmdEnd = 75,
    TopVerbanoPlicIrqIdSpiDeviceTpmRdfifoDrop = 76,
    TopVerbanoPlicIrqIdI2c0FmtThreshold = 77,
    TopVerbanoPlicIrqIdI2c0RxThreshold = 78,
    TopVerbanoPlicIrqIdI2c0AcqThreshold = 79,
    TopVerbanoPlicIrqIdI2c0RxOverflow = 80,
    TopVerbanoPlicIrqIdI2c0ControllerHalt = 81,
    TopVerbanoPlicIrqIdI2c0SclInterference = 82,
    TopVerbanoPlicIrqIdI2c0SdaInterference = 83,
    TopVerbanoPlicIrqIdI2c0StretchTimeout = 84,
    TopVerbanoPlicIrqIdI2c0SdaUnstable = 85,
    TopVerbanoPlicIrqIdI2c0CmdComplete = 86,
    TopVerbanoPlicIrqIdI2c0TxStretch = 87,
    TopVerbanoPlicIrqIdI2c0TxThreshold = 88,
    TopVerbanoPlicIrqIdI2c0AcqStretch = 89,
    TopVerbanoPlicIrqIdI2c0UnexpStop = 90,
    TopVerbanoPlicIrqIdI2c0HostTimeout = 91,
    TopVerbanoPlicIrqIdI2c1FmtThreshold = 92,
    TopVerbanoPlicIrqIdI2c1RxThreshold = 93,
    TopVerbanoPlicIrqIdI2c1AcqThreshold = 94,
    TopVerbanoPlicIrqIdI2c1RxOverflow = 95,
    TopVerbanoPlicIrqIdI2c1ControllerHalt = 96,
    TopVerbanoPlicIrqIdI2c1SclInterference = 97,
    TopVerbanoPlicIrqIdI2c1SdaInterference = 98,
    TopVerbanoPlicIrqIdI2c1StretchTimeout = 99,
    TopVerbanoPlicIrqIdI2c1SdaUnstable = 100,
    TopVerbanoPlicIrqIdI2c1CmdComplete = 101,
    TopVerbanoPlicIrqIdI2c1TxStretch = 102,
    TopVerbanoPlicIrqIdI2c1TxThreshold = 103,
    TopVerbanoPlicIrqIdI2c1AcqStretch = 104,
    TopVerbanoPlicIrqIdI2c1UnexpStop = 105,
    TopVerbanoPlicIrqIdI2c1HostTimeout = 106,
    TopVerbanoPlicIrqIdI2c2FmtThreshold = 107,
    TopVerbanoPlicIrqIdI2c2RxThreshold = 108,
    TopVerbanoPlicIrqIdI2c2AcqThreshold = 109,
    TopVerbanoPlicIrqIdI2c2RxOverflow = 110,
    TopVerbanoPlicIrqIdI2c2ControllerHalt = 111,
    TopVerbanoPlicIrqIdI2c2SclInterference = 112,
    TopVerbanoPlicIrqIdI2c2SdaInterference = 113,
    TopVerbanoPlicIrqIdI2c2StretchTimeout = 114,
    TopVerbanoPlicIrqIdI2c2SdaUnstable = 115,
    TopVerbanoPlicIrqIdI2c2CmdComplete = 116,
    TopVerbanoPlicIrqIdI2c2TxStretch = 117,
    TopVerbanoPlicIrqIdI2c2TxThreshold = 118,
    TopVerbanoPlicIrqIdI2c2AcqStretch = 119,
    TopVerbanoPlicIrqIdI2c2UnexpStop = 120,
    TopVerbanoPlicIrqIdI2c2HostTimeout = 121,
    TopVerbanoPlicIrqIdPattgenDoneCh0 = 122,
    TopVerbanoPlicIrqIdPattgenDoneCh1 = 123,
    TopVerbanoPlicIrqIdRvTimerTimerExpiredHart0Timer0 = 124,
    TopVerbanoPlicIrqIdOtpCtrlOtpOperationDone = 125,
    TopVerbanoPlicIrqIdOtpCtrlOtpError = 126,
    TopVerbanoPlicIrqIdAlertHandlerClassa = 127,
    TopVerbanoPlicIrqIdAlertHandlerClassb = 128,
    TopVerbanoPlicIrqIdAlertHandlerClassc = 129,
    TopVerbanoPlicIrqIdAlertHandlerClassd = 130,
    TopVerbanoPlicIrqIdSpiHost0Error = 131,
    TopVerbanoPlicIrqIdSpiHost0SpiEvent = 132,
    TopVerbanoPlicIrqIdSpiHost1Error = 133,
    TopVerbanoPlicIrqIdSpiHost1SpiEvent = 134,
    TopVerbanoPlicIrqIdUsbdevPktReceived = 135,
    TopVerbanoPlicIrqIdUsbdevPktSent = 136,
    TopVerbanoPlicIrqIdUsbdevDisconnected = 137,
    TopVerbanoPlicIrqIdUsbdevHostLost = 138,
    TopVerbanoPlicIrqIdUsbdevLinkReset = 139,
    TopVerbanoPlicIrqIdUsbdevLinkSuspend = 140,
    TopVerbanoPlicIrqIdUsbdevLinkResume = 141,
    TopVerbanoPlicIrqIdUsbdevAvOutEmpty = 142,
    TopVerbanoPlicIrqIdUsbdevRxFull = 143,
    TopVerbanoPlicIrqIdUsbdevAvOverflow = 144,
    TopVerbanoPlicIrqIdUsbdevLinkInErr = 145,
    TopVerbanoPlicIrqIdUsbdevRxCrcErr = 146,
    TopVerbanoPlicIrqIdUsbdevRxPidErr = 147,
    TopVerbanoPlicIrqIdUsbdevRxBitstuffErr = 148,
    TopVerbanoPlicIrqIdUsbdevFrame = 149,
    TopVerbanoPlicIrqIdUsbdevPowered = 150,
    TopVerbanoPlicIrqIdUsbdevLinkOutErr = 151,
    TopVerbanoPlicIrqIdUsbdevAvSetupEmpty = 152,
    TopVerbanoPlicIrqIdPwrmgrAonWakeup = 153,
    TopVerbanoPlicIrqIdSysrstCtrlAonEventDetected = 154,
    TopVerbanoPlicIrqIdAdcCtrlAonMatchPending = 155,
    TopVerbanoPlicIrqIdAonTimerAonWkupTimerExpired = 156,
    TopVerbanoPlicIrqIdAonTimerAonWdogTimerBark = 157,
    TopVerbanoPlicIrqIdSensorCtrlAonIoStatusChange = 158,
    TopVerbanoPlicIrqIdSensorCtrlAonInitStatusChange = 159,
    TopVerbanoPlicIrqIdFlashCtrlProgEmpty = 160,
    TopVerbanoPlicIrqIdFlashCtrlProgLvl = 161,
    TopVerbanoPlicIrqIdFlashCtrlRdFull = 162,
    TopVerbanoPlicIrqIdFlashCtrlRdLvl = 163,
    TopVerbanoPlicIrqIdFlashCtrlOpDone = 164,
    TopVerbanoPlicIrqIdFlashCtrlCorrErr = 165,
    TopVerbanoPlicIrqIdHmacHmacDone = 166,
    TopVerbanoPlicIrqIdHmacFifoEmpty = 167,
    TopVerbanoPlicIrqIdHmacHmacErr = 168,
    TopVerbanoPlicIrqIdKmacKmacDone = 169,
    TopVerbanoPlicIrqIdKmacFifoEmpty = 170,
    TopVerbanoPlicIrqIdKmacKmacErr = 171,
    TopVerbanoPlicIrqIdOtbnDone = 172,
    TopVerbanoPlicIrqIdKeymgrOpDone = 173,
    TopVerbanoPlicIrqIdCsrngCsCmdReqDone = 174,
    TopVerbanoPlicIrqIdCsrngCsEntropyReq = 175,
    TopVerbanoPlicIrqIdCsrngCsHwInstExc = 176,
    TopVerbanoPlicIrqIdCsrngCsFatalErr = 177,
    TopVerbanoPlicIrqIdEntropySrcEsEntropyValid = 178,
    TopVerbanoPlicIrqIdEntropySrcEsHealthTestFailed = 179,
    TopVerbanoPlicIrqIdEntropySrcEsObserveFifoReady = 180,
    TopVerbanoPlicIrqIdEntropySrcEsFatalErr = 181,
    TopVerbanoPlicIrqIdEdn0EdnCmdReqDone = 182,
    TopVerbanoPlicIrqIdEdn0EdnFatalErr = 183,
    TopVerbanoPlicIrqIdEdn1EdnCmdReqDone = 184,
    TopVerbanoPlicIrqIdEdn1EdnFatalErr = 185,
    TopVerbanoPlicIrqIdCount
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
    MioInI2c0Sda = 32,
    MioInI2c0Scl = 33,
    MioInI2c1Sda = 34,
    MioInI2c1Scl = 35,
    MioInI2c2Sda = 36,
    MioInI2c2Scl = 37,
    MioInSpiHost1Sd0 = 38,
    MioInSpiHost1Sd1 = 39,
    MioInSpiHost1Sd2 = 40,
    MioInSpiHost1Sd3 = 41,
    MioInUart0Rx = 42,
    MioInUart1Rx = 43,
    MioInUart2Rx = 44,
    MioInUart3Rx = 45,
    MioInSpiDeviceTpmCsb = 46,
    MioInFlashCtrlTck = 47,
    MioInFlashCtrlTms = 48,
    MioInFlashCtrlTdi = 49,
    MioInSysrstCtrlAonAcPresent = 50,
    MioInSysrstCtrlAonKey0In = 51,
    MioInSysrstCtrlAonKey1In = 52,
    MioInSysrstCtrlAonKey2In = 53,
    MioInSysrstCtrlAonPwrbIn = 54,
    MioInSysrstCtrlAonLidOpen = 55,
    MioInUsbdevSense = 56,
    MioInCount = 57
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
    MioOutI2c0Sda = 32,
    MioOutI2c0Scl = 33,
    MioOutI2c1Sda = 34,
    MioOutI2c1Scl = 35,
    MioOutI2c2Sda = 36,
    MioOutI2c2Scl = 37,
    MioOutSpiHost1Sd0 = 38,
    MioOutSpiHost1Sd1 = 39,
    MioOutSpiHost1Sd2 = 40,
    MioOutSpiHost1Sd3 = 41,
    MioOutUart0Tx = 42,
    MioOutUart1Tx = 43,
    MioOutUart2Tx = 44,
    MioOutUart3Tx = 45,
    MioOutPattgenPda0Tx = 46,
    MioOutPattgenPcl0Tx = 47,
    MioOutPattgenPda1Tx = 48,
    MioOutPattgenPcl1Tx = 49,
    MioOutSpiHost1Sck = 50,
    MioOutSpiHost1Csb = 51,
    MioOutFlashCtrlTdo = 52,
    MioOutSensorCtrlAonAstDebugOut0 = 53,
    MioOutSensorCtrlAonAstDebugOut1 = 54,
    MioOutSensorCtrlAonAstDebugOut2 = 55,
    MioOutSensorCtrlAonAstDebugOut3 = 56,
    MioOutSensorCtrlAonAstDebugOut4 = 57,
    MioOutSensorCtrlAonAstDebugOut5 = 58,
    MioOutSensorCtrlAonAstDebugOut6 = 59,
    MioOutSensorCtrlAonAstDebugOut7 = 60,
    MioOutSensorCtrlAonAstDebugOut8 = 61,
    MioOutPwmAonPwm0 = 62,
    MioOutPwmAonPwm1 = 63,
    MioOutPwmAonPwm2 = 64,
    MioOutPwmAonPwm3 = 65,
    MioOutPwmAonPwm4 = 66,
    MioOutPwmAonPwm5 = 67,
    MioOutOtpMacroTest0 = 68,
    MioOutSysrstCtrlAonBatDisable = 69,
    MioOutSysrstCtrlAonKey0Out = 70,
    MioOutSysrstCtrlAonKey1Out = 71,
    MioOutSysrstCtrlAonKey2Out = 72,
    MioOutSysrstCtrlAonPwrbOut = 73,
    MioOutSysrstCtrlAonZ3Wakeup = 74,
    MioOutCount = 75
  } mio_out_e;

  // Enumeration for DIO signals, used on both the top and chip-levels.
  typedef enum int unsigned {
    DioUsbdevUsbDp = 0,
    DioUsbdevUsbDn = 1,
    DioSpiHost0Sd0 = 2,
    DioSpiHost0Sd1 = 3,
    DioSpiHost0Sd2 = 4,
    DioSpiHost0Sd3 = 5,
    DioSpiDeviceSd0 = 6,
    DioSpiDeviceSd1 = 7,
    DioSpiDeviceSd2 = 8,
    DioSpiDeviceSd3 = 9,
    DioSysrstCtrlAonEcRstL = 10,
    DioSysrstCtrlAonFlashWpL = 11,
    DioSpiDeviceSck = 12,
    DioSpiDeviceCsb = 13,
    DioSpiHost0Sck = 14,
    DioSpiHost0Csb = 15,
    DioCount = 16
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
    DioPadOtpExtVolt = 8,
    DioPadSpiHostD0 = 9,
    DioPadSpiHostD1 = 10,
    DioPadSpiHostD2 = 11,
    DioPadSpiHostD3 = 12,
    DioPadSpiHostClk = 13,
    DioPadSpiHostCsL = 14,
    DioPadSpiDevD0 = 15,
    DioPadSpiDevD1 = 16,
    DioPadSpiDevD2 = 17,
    DioPadSpiDevD3 = 18,
    DioPadSpiDevClk = 19,
    DioPadSpiDevCsL = 20,
    DioPadIor8 = 21,
    DioPadIor9 = 22,
    DioPadCount
  } dio_pad_e;

  // List of peripheral instantiated in this chip.
  typedef enum {
    PeripheralAdcCtrlAon,
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
    PeripheralI2c0,
    PeripheralI2c1,
    PeripheralI2c2,
    PeripheralKeymgr,
    PeripheralKmac,
    PeripheralLcCtrl,
    PeripheralOtbn,
    PeripheralOtpCtrl,
    PeripheralOtpMacro,
    PeripheralPattgen,
    PeripheralPinmuxAon,
    PeripheralPwmAon,
    PeripheralPwrmgrAon,
    PeripheralRomCtrl,
    PeripheralRstmgrAon,
    PeripheralRvCoreIbex,
    PeripheralRvDm,
    PeripheralRvPlic,
    PeripheralRvTimer,
    PeripheralSensorCtrlAon,
    PeripheralSpiDevice,
    PeripheralSpiHost0,
    PeripheralSpiHost1,
    PeripheralSramCtrlMain,
    PeripheralSramCtrlRetAon,
    PeripheralSysrstCtrlAon,
    PeripheralUart0,
    PeripheralUart1,
    PeripheralUart2,
    PeripheralUart3,
    PeripheralUsbdev,
    PeripheralCount
  } peripheral_e;

  // MMIO Region
  //
  parameter int unsigned TOP_VERBANO_MMIO_BASE_ADDR = 32'h40000000;
  parameter int unsigned TOP_VERBANO_MMIO_SIZE_BYTES = 32'h10000000;

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
