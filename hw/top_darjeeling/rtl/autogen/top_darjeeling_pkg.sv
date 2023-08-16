// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_darjeeling/data/top_darjeeling.hjson \
//                -o hw/top_darjeeling/ \
//                --rnd_cnst_seed 4881560218908238235

package top_darjeeling_pkg;
  /**
   * Peripheral base address for uart0 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_UART0_BASE_ADDR = 32'h40000000;

  /**
   * Peripheral size in bytes for uart0 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_UART0_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for uart1 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_UART1_BASE_ADDR = 32'h40010000;

  /**
   * Peripheral size in bytes for uart1 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_UART1_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for uart2 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_UART2_BASE_ADDR = 32'h40020000;

  /**
   * Peripheral size in bytes for uart2 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_UART2_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for uart3 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_UART3_BASE_ADDR = 32'h40030000;

  /**
   * Peripheral size in bytes for uart3 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_UART3_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for gpio in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_GPIO_BASE_ADDR = 32'h40040000;

  /**
   * Peripheral size in bytes for gpio in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_GPIO_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for spi_device in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SPI_DEVICE_BASE_ADDR = 32'h40050000;

  /**
   * Peripheral size in bytes for spi_device in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SPI_DEVICE_SIZE_BYTES = 32'h2000;

  /**
   * Peripheral base address for i2c0 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_I2C0_BASE_ADDR = 32'h40080000;

  /**
   * Peripheral size in bytes for i2c0 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_I2C0_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for i2c1 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_I2C1_BASE_ADDR = 32'h40090000;

  /**
   * Peripheral size in bytes for i2c1 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_I2C1_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for i2c2 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_I2C2_BASE_ADDR = 32'h400A0000;

  /**
   * Peripheral size in bytes for i2c2 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_I2C2_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for pattgen in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_PATTGEN_BASE_ADDR = 32'h400E0000;

  /**
   * Peripheral size in bytes for pattgen in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_PATTGEN_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for rv_timer in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RV_TIMER_BASE_ADDR = 32'h40100000;

  /**
   * Peripheral size in bytes for rv_timer in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RV_TIMER_SIZE_BYTES = 32'h200;

  /**
   * Peripheral base address for core device on otp_ctrl in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_OTP_CTRL_CORE_BASE_ADDR = 32'h40130000;

  /**
   * Peripheral size in bytes for core device on otp_ctrl in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_OTP_CTRL_CORE_SIZE_BYTES = 32'h2000;

  /**
   * Peripheral base address for prim device on otp_ctrl in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_OTP_CTRL_PRIM_BASE_ADDR = 32'h40132000;

  /**
   * Peripheral size in bytes for prim device on otp_ctrl in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_OTP_CTRL_PRIM_SIZE_BYTES = 32'h20;

  /**
   * Peripheral base address for lc_ctrl in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_LC_CTRL_BASE_ADDR = 32'h40140000;

  /**
   * Peripheral size in bytes for lc_ctrl in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_LC_CTRL_SIZE_BYTES = 32'h100;

  /**
   * Peripheral base address for alert_handler in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_ALERT_HANDLER_BASE_ADDR = 32'h40150000;

  /**
   * Peripheral size in bytes for alert_handler in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_ALERT_HANDLER_SIZE_BYTES = 32'h800;

  /**
   * Peripheral base address for spi_host0 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SPI_HOST0_BASE_ADDR = 32'h40300000;

  /**
   * Peripheral size in bytes for spi_host0 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SPI_HOST0_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for spi_host1 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SPI_HOST1_BASE_ADDR = 32'h40310000;

  /**
   * Peripheral size in bytes for spi_host1 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SPI_HOST1_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for usbdev in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_USBDEV_BASE_ADDR = 32'h40320000;

  /**
   * Peripheral size in bytes for usbdev in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_USBDEV_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for pwrmgr_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_PWRMGR_AON_BASE_ADDR = 32'h40400000;

  /**
   * Peripheral size in bytes for pwrmgr_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_PWRMGR_AON_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for rstmgr_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RSTMGR_AON_BASE_ADDR = 32'h40410000;

  /**
   * Peripheral size in bytes for rstmgr_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RSTMGR_AON_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for clkmgr_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_CLKMGR_AON_BASE_ADDR = 32'h40420000;

  /**
   * Peripheral size in bytes for clkmgr_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_CLKMGR_AON_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for sysrst_ctrl_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SYSRST_CTRL_AON_BASE_ADDR = 32'h40430000;

  /**
   * Peripheral size in bytes for sysrst_ctrl_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SYSRST_CTRL_AON_SIZE_BYTES = 32'h100;

  /**
   * Peripheral base address for adc_ctrl_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_ADC_CTRL_AON_BASE_ADDR = 32'h40440000;

  /**
   * Peripheral size in bytes for adc_ctrl_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_ADC_CTRL_AON_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for pwm_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_PWM_AON_BASE_ADDR = 32'h40450000;

  /**
   * Peripheral size in bytes for pwm_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_PWM_AON_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for pinmux_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_PINMUX_AON_BASE_ADDR = 32'h40460000;

  /**
   * Peripheral size in bytes for pinmux_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_PINMUX_AON_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for aon_timer_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_AON_TIMER_AON_BASE_ADDR = 32'h40470000;

  /**
   * Peripheral size in bytes for aon_timer_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_AON_TIMER_AON_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for ast in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_AST_BASE_ADDR = 32'h40480000;

  /**
   * Peripheral size in bytes for ast in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_AST_SIZE_BYTES = 32'h400;

  /**
   * Peripheral base address for sensor_ctrl in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SENSOR_CTRL_BASE_ADDR = 32'h40490000;

  /**
   * Peripheral size in bytes for sensor_ctrl in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SENSOR_CTRL_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for regs device on sram_ctrl_ret_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SRAM_CTRL_RET_AON_REGS_BASE_ADDR = 32'h40500000;

  /**
   * Peripheral size in bytes for regs device on sram_ctrl_ret_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SRAM_CTRL_RET_AON_REGS_SIZE_BYTES = 32'h20;

  /**
   * Peripheral base address for ram device on sram_ctrl_ret_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SRAM_CTRL_RET_AON_RAM_BASE_ADDR = 32'h40600000;

  /**
   * Peripheral size in bytes for ram device on sram_ctrl_ret_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SRAM_CTRL_RET_AON_RAM_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for core device on flash_ctrl in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_FLASH_CTRL_CORE_BASE_ADDR = 32'h41000000;

  /**
   * Peripheral size in bytes for core device on flash_ctrl in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_FLASH_CTRL_CORE_SIZE_BYTES = 32'h200;

  /**
   * Peripheral base address for prim device on flash_ctrl in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_FLASH_CTRL_PRIM_BASE_ADDR = 32'h41008000;

  /**
   * Peripheral size in bytes for prim device on flash_ctrl in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_FLASH_CTRL_PRIM_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for mem device on flash_ctrl in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_FLASH_CTRL_MEM_BASE_ADDR = 32'h20000000;

  /**
   * Peripheral size in bytes for mem device on flash_ctrl in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_FLASH_CTRL_MEM_SIZE_BYTES = 32'h100000;

  /**
   * Peripheral base address for regs device on rv_dm in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RV_DM_REGS_BASE_ADDR = 32'h41200000;

  /**
   * Peripheral size in bytes for regs device on rv_dm in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RV_DM_REGS_SIZE_BYTES = 32'h4;

  /**
   * Peripheral base address for mem device on rv_dm in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RV_DM_MEM_BASE_ADDR = 32'h10000;

  /**
   * Peripheral size in bytes for mem device on rv_dm in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RV_DM_MEM_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for rv_plic in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RV_PLIC_BASE_ADDR = 32'h48000000;

  /**
   * Peripheral size in bytes for rv_plic in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RV_PLIC_SIZE_BYTES = 32'h8000000;

  /**
   * Peripheral base address for aes in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_AES_BASE_ADDR = 32'h41100000;

  /**
   * Peripheral size in bytes for aes in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_AES_SIZE_BYTES = 32'h100;

  /**
   * Peripheral base address for hmac in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_HMAC_BASE_ADDR = 32'h41110000;

  /**
   * Peripheral size in bytes for hmac in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_HMAC_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for kmac in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_KMAC_BASE_ADDR = 32'h41120000;

  /**
   * Peripheral size in bytes for kmac in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_KMAC_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for otbn in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_OTBN_BASE_ADDR = 32'h41130000;

  /**
   * Peripheral size in bytes for otbn in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_OTBN_SIZE_BYTES = 32'h10000;

  /**
   * Peripheral base address for keymgr in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_KEYMGR_BASE_ADDR = 32'h41140000;

  /**
   * Peripheral size in bytes for keymgr in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_KEYMGR_SIZE_BYTES = 32'h100;

  /**
   * Peripheral base address for csrng in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_CSRNG_BASE_ADDR = 32'h41150000;

  /**
   * Peripheral size in bytes for csrng in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_CSRNG_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for entropy_src in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_ENTROPY_SRC_BASE_ADDR = 32'h41160000;

  /**
   * Peripheral size in bytes for entropy_src in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_ENTROPY_SRC_SIZE_BYTES = 32'h100;

  /**
   * Peripheral base address for edn0 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_EDN0_BASE_ADDR = 32'h41170000;

  /**
   * Peripheral size in bytes for edn0 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_EDN0_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for edn1 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_EDN1_BASE_ADDR = 32'h41180000;

  /**
   * Peripheral size in bytes for edn1 in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_EDN1_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for regs device on sram_ctrl_main in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SRAM_CTRL_MAIN_REGS_BASE_ADDR = 32'h411C0000;

  /**
   * Peripheral size in bytes for regs device on sram_ctrl_main in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SRAM_CTRL_MAIN_REGS_SIZE_BYTES = 32'h20;

  /**
   * Peripheral base address for ram device on sram_ctrl_main in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SRAM_CTRL_MAIN_RAM_BASE_ADDR = 32'h10000000;

  /**
   * Peripheral size in bytes for ram device on sram_ctrl_main in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_SRAM_CTRL_MAIN_RAM_SIZE_BYTES = 32'h10000;

  /**
   * Peripheral base address for regs device on rom_ctrl in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_ROM_CTRL_REGS_BASE_ADDR = 32'h411E0000;

  /**
   * Peripheral size in bytes for regs device on rom_ctrl in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_ROM_CTRL_REGS_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for rom device on rom_ctrl in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_ROM_CTRL_ROM_BASE_ADDR = 32'h8000;

  /**
   * Peripheral size in bytes for rom device on rom_ctrl in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_ROM_CTRL_ROM_SIZE_BYTES = 32'h8000;

  /**
   * Peripheral base address for cfg device on rv_core_ibex in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RV_CORE_IBEX_CFG_BASE_ADDR = 32'h411F0000;

  /**
   * Peripheral size in bytes for cfg device on rv_core_ibex in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RV_CORE_IBEX_CFG_SIZE_BYTES = 32'h800;

  /**
   * Memory base address for ram_ret_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RAM_RET_AON_BASE_ADDR = 32'h40600000;

  /**
   * Memory size for ram_ret_aon in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RAM_RET_AON_SIZE_BYTES = 32'h1000;

  /**
   * Memory base address for eflash in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_EFLASH_BASE_ADDR = 32'h20000000;

  /**
   * Memory size for eflash in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_EFLASH_SIZE_BYTES = 32'h100000;

  /**
   * Memory base address for ram_main in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RAM_MAIN_BASE_ADDR = 32'h10000000;

  /**
   * Memory size for ram_main in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_RAM_MAIN_SIZE_BYTES = 32'h10000;

  /**
   * Memory base address for rom in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_ROM_BASE_ADDR = 32'h8000;

  /**
   * Memory size for rom in top darjeeling.
   */
  parameter int unsigned TOP_DARJEELING_ROM_SIZE_BYTES = 32'h8000;


  // Enumeration of alert modules
  typedef enum int unsigned {
    TopDarjeelingAlertPeripheralUart0 = 0,
    TopDarjeelingAlertPeripheralUart1 = 1,
    TopDarjeelingAlertPeripheralUart2 = 2,
    TopDarjeelingAlertPeripheralUart3 = 3,
    TopDarjeelingAlertPeripheralGpio = 4,
    TopDarjeelingAlertPeripheralSpiDevice = 5,
    TopDarjeelingAlertPeripheralI2c0 = 6,
    TopDarjeelingAlertPeripheralI2c1 = 7,
    TopDarjeelingAlertPeripheralI2c2 = 8,
    TopDarjeelingAlertPeripheralPattgen = 9,
    TopDarjeelingAlertPeripheralRvTimer = 10,
    TopDarjeelingAlertPeripheralOtpCtrl = 11,
    TopDarjeelingAlertPeripheralLcCtrl = 12,
    TopDarjeelingAlertPeripheralSpiHost0 = 13,
    TopDarjeelingAlertPeripheralSpiHost1 = 14,
    TopDarjeelingAlertPeripheralUsbdev = 15,
    TopDarjeelingAlertPeripheralPwrmgrAon = 16,
    TopDarjeelingAlertPeripheralRstmgrAon = 17,
    TopDarjeelingAlertPeripheralClkmgrAon = 18,
    TopDarjeelingAlertPeripheralSysrstCtrlAon = 19,
    TopDarjeelingAlertPeripheralAdcCtrlAon = 20,
    TopDarjeelingAlertPeripheralPwmAon = 21,
    TopDarjeelingAlertPeripheralPinmuxAon = 22,
    TopDarjeelingAlertPeripheralAonTimerAon = 23,
    TopDarjeelingAlertPeripheralSensorCtrl = 24,
    TopDarjeelingAlertPeripheralSramCtrlRetAon = 25,
    TopDarjeelingAlertPeripheralFlashCtrl = 26,
    TopDarjeelingAlertPeripheralRvDm = 27,
    TopDarjeelingAlertPeripheralRvPlic = 28,
    TopDarjeelingAlertPeripheralAes = 29,
    TopDarjeelingAlertPeripheralHmac = 30,
    TopDarjeelingAlertPeripheralKmac = 31,
    TopDarjeelingAlertPeripheralOtbn = 32,
    TopDarjeelingAlertPeripheralKeymgr = 33,
    TopDarjeelingAlertPeripheralCsrng = 34,
    TopDarjeelingAlertPeripheralEntropySrc = 35,
    TopDarjeelingAlertPeripheralEdn0 = 36,
    TopDarjeelingAlertPeripheralEdn1 = 37,
    TopDarjeelingAlertPeripheralSramCtrlMain = 38,
    TopDarjeelingAlertPeripheralRomCtrl = 39,
    TopDarjeelingAlertPeripheralRvCoreIbex = 40,
    TopDarjeelingAlertPeripheralCount
  } alert_peripheral_e;

  // Enumeration of alerts
  typedef enum int unsigned {
    TopDarjeelingAlertIdUart0FatalFault = 0,
    TopDarjeelingAlertIdUart1FatalFault = 1,
    TopDarjeelingAlertIdUart2FatalFault = 2,
    TopDarjeelingAlertIdUart3FatalFault = 3,
    TopDarjeelingAlertIdGpioFatalFault = 4,
    TopDarjeelingAlertIdSpiDeviceFatalFault = 5,
    TopDarjeelingAlertIdI2c0FatalFault = 6,
    TopDarjeelingAlertIdI2c1FatalFault = 7,
    TopDarjeelingAlertIdI2c2FatalFault = 8,
    TopDarjeelingAlertIdPattgenFatalFault = 9,
    TopDarjeelingAlertIdRvTimerFatalFault = 10,
    TopDarjeelingAlertIdOtpCtrlFatalMacroError = 11,
    TopDarjeelingAlertIdOtpCtrlFatalCheckError = 12,
    TopDarjeelingAlertIdOtpCtrlFatalBusIntegError = 13,
    TopDarjeelingAlertIdOtpCtrlFatalPrimOtpAlert = 14,
    TopDarjeelingAlertIdOtpCtrlRecovPrimOtpAlert = 15,
    TopDarjeelingAlertIdLcCtrlFatalProgError = 16,
    TopDarjeelingAlertIdLcCtrlFatalStateError = 17,
    TopDarjeelingAlertIdLcCtrlFatalBusIntegError = 18,
    TopDarjeelingAlertIdSpiHost0FatalFault = 19,
    TopDarjeelingAlertIdSpiHost1FatalFault = 20,
    TopDarjeelingAlertIdUsbdevFatalFault = 21,
    TopDarjeelingAlertIdPwrmgrAonFatalFault = 22,
    TopDarjeelingAlertIdRstmgrAonFatalFault = 23,
    TopDarjeelingAlertIdRstmgrAonFatalCnstyFault = 24,
    TopDarjeelingAlertIdClkmgrAonRecovFault = 25,
    TopDarjeelingAlertIdClkmgrAonFatalFault = 26,
    TopDarjeelingAlertIdSysrstCtrlAonFatalFault = 27,
    TopDarjeelingAlertIdAdcCtrlAonFatalFault = 28,
    TopDarjeelingAlertIdPwmAonFatalFault = 29,
    TopDarjeelingAlertIdPinmuxAonFatalFault = 30,
    TopDarjeelingAlertIdAonTimerAonFatalFault = 31,
    TopDarjeelingAlertIdSensorCtrlRecovAlert = 32,
    TopDarjeelingAlertIdSensorCtrlFatalAlert = 33,
    TopDarjeelingAlertIdSramCtrlRetAonFatalError = 34,
    TopDarjeelingAlertIdFlashCtrlRecovErr = 35,
    TopDarjeelingAlertIdFlashCtrlFatalStdErr = 36,
    TopDarjeelingAlertIdFlashCtrlFatalErr = 37,
    TopDarjeelingAlertIdFlashCtrlFatalPrimFlashAlert = 38,
    TopDarjeelingAlertIdFlashCtrlRecovPrimFlashAlert = 39,
    TopDarjeelingAlertIdRvDmFatalFault = 40,
    TopDarjeelingAlertIdRvPlicFatalFault = 41,
    TopDarjeelingAlertIdAesRecovCtrlUpdateErr = 42,
    TopDarjeelingAlertIdAesFatalFault = 43,
    TopDarjeelingAlertIdHmacFatalFault = 44,
    TopDarjeelingAlertIdKmacRecovOperationErr = 45,
    TopDarjeelingAlertIdKmacFatalFaultErr = 46,
    TopDarjeelingAlertIdOtbnFatal = 47,
    TopDarjeelingAlertIdOtbnRecov = 48,
    TopDarjeelingAlertIdKeymgrRecovOperationErr = 49,
    TopDarjeelingAlertIdKeymgrFatalFaultErr = 50,
    TopDarjeelingAlertIdCsrngRecovAlert = 51,
    TopDarjeelingAlertIdCsrngFatalAlert = 52,
    TopDarjeelingAlertIdEntropySrcRecovAlert = 53,
    TopDarjeelingAlertIdEntropySrcFatalAlert = 54,
    TopDarjeelingAlertIdEdn0RecovAlert = 55,
    TopDarjeelingAlertIdEdn0FatalAlert = 56,
    TopDarjeelingAlertIdEdn1RecovAlert = 57,
    TopDarjeelingAlertIdEdn1FatalAlert = 58,
    TopDarjeelingAlertIdSramCtrlMainFatalError = 59,
    TopDarjeelingAlertIdRomCtrlFatal = 60,
    TopDarjeelingAlertIdRvCoreIbexFatalSwErr = 61,
    TopDarjeelingAlertIdRvCoreIbexRecovSwErr = 62,
    TopDarjeelingAlertIdRvCoreIbexFatalHwErr = 63,
    TopDarjeelingAlertIdRvCoreIbexRecovHwErr = 64,
    TopDarjeelingAlertIdCount
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
    MioOutSensorCtrlAstDebugOut0 = 53,
    MioOutSensorCtrlAstDebugOut1 = 54,
    MioOutSensorCtrlAstDebugOut2 = 55,
    MioOutSensorCtrlAstDebugOut3 = 56,
    MioOutSensorCtrlAstDebugOut4 = 57,
    MioOutSensorCtrlAstDebugOut5 = 58,
    MioOutSensorCtrlAstDebugOut6 = 59,
    MioOutSensorCtrlAstDebugOut7 = 60,
    MioOutSensorCtrlAstDebugOut8 = 61,
    MioOutPwmAonPwm0 = 62,
    MioOutPwmAonPwm1 = 63,
    MioOutPwmAonPwm2 = 64,
    MioOutPwmAonPwm3 = 65,
    MioOutPwmAonPwm4 = 66,
    MioOutPwmAonPwm5 = 67,
    MioOutOtpCtrlTest0 = 68,
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
    PeripheralSensorCtrl,
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

  // TODO: Enumeration for PLIC Interrupt source peripheral.
  // TODO: Enumeration for PLIC Interrupt Ids.

// MACROs for AST analog simulation support
`ifdef ANALOGSIM
  `define INOUT_AI input ast_pkg::awire_t
  `define INOUT_AO output ast_pkg::awire_t
`else
  `define INOUT_AI inout
  `define INOUT_AO inout
`endif

endpackage
