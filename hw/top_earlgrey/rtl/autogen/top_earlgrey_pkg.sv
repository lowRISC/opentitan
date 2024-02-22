// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_earlgrey/data/top_earlgrey.hjson \
//                -o hw/top_earlgrey/ \
//                --rnd_cnst_seed \
//                1017106219537032642877583828875051302543807092889754935647094601236425074047

package top_earlgrey_pkg;
  /**
   * Peripheral base address for uart0 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_UART0_BASE_ADDR = 32'h40000000;

  /**
   * Peripheral size in bytes for uart0 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_UART0_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for uart1 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_UART1_BASE_ADDR = 32'h40010000;

  /**
   * Peripheral size in bytes for uart1 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_UART1_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for uart2 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_UART2_BASE_ADDR = 32'h40020000;

  /**
   * Peripheral size in bytes for uart2 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_UART2_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for uart3 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_UART3_BASE_ADDR = 32'h40030000;

  /**
   * Peripheral size in bytes for uart3 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_UART3_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for gpio in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_GPIO_BASE_ADDR = 32'h40040000;

  /**
   * Peripheral size in bytes for gpio in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_GPIO_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for spi_device in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SPI_DEVICE_BASE_ADDR = 32'h40050000;

  /**
   * Peripheral size in bytes for spi_device in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SPI_DEVICE_SIZE_BYTES = 32'h2000;

  /**
   * Peripheral base address for i2c0 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_I2C0_BASE_ADDR = 32'h40080000;

  /**
   * Peripheral size in bytes for i2c0 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_I2C0_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for i2c1 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_I2C1_BASE_ADDR = 32'h40090000;

  /**
   * Peripheral size in bytes for i2c1 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_I2C1_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for i2c2 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_I2C2_BASE_ADDR = 32'h400A0000;

  /**
   * Peripheral size in bytes for i2c2 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_I2C2_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for i2c3 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_I2C3_BASE_ADDR = 32'h400B0000;

  /**
   * Peripheral size in bytes for i2c3 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_I2C3_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for pattgen in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_PATTGEN_BASE_ADDR = 32'h400E0000;

  /**
   * Peripheral size in bytes for pattgen in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_PATTGEN_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for rv_timer in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_TIMER_BASE_ADDR = 32'h40100000;

  /**
   * Peripheral size in bytes for rv_timer in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_TIMER_SIZE_BYTES = 32'h200;

  /**
   * Peripheral base address for core device on otp_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR = 32'h40130000;

  /**
   * Peripheral size in bytes for core device on otp_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_OTP_CTRL_CORE_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for prim device on otp_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_OTP_CTRL_PRIM_BASE_ADDR = 32'h40138000;

  /**
   * Peripheral size in bytes for prim device on otp_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_OTP_CTRL_PRIM_SIZE_BYTES = 32'h20;

  /**
   * Peripheral base address for lc_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_LC_CTRL_BASE_ADDR = 32'h40140000;

  /**
   * Peripheral size in bytes for lc_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_LC_CTRL_SIZE_BYTES = 32'h100;

  /**
   * Peripheral base address for alert_handler in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR = 32'h40150000;

  /**
   * Peripheral size in bytes for alert_handler in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ALERT_HANDLER_SIZE_BYTES = 32'h800;

  /**
   * Peripheral base address for spi_host0 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SPI_HOST0_BASE_ADDR = 32'h40300000;

  /**
   * Peripheral size in bytes for spi_host0 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SPI_HOST0_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for spi_host1 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SPI_HOST1_BASE_ADDR = 32'h40310000;

  /**
   * Peripheral size in bytes for spi_host1 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SPI_HOST1_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for usbdev in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_USBDEV_BASE_ADDR = 32'h40320000;

  /**
   * Peripheral size in bytes for usbdev in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_USBDEV_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for pwrmgr_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_PWRMGR_AON_BASE_ADDR = 32'h40400000;

  /**
   * Peripheral size in bytes for pwrmgr_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_PWRMGR_AON_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for rstmgr_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RSTMGR_AON_BASE_ADDR = 32'h40410000;

  /**
   * Peripheral size in bytes for rstmgr_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RSTMGR_AON_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for clkmgr_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_CLKMGR_AON_BASE_ADDR = 32'h40420000;

  /**
   * Peripheral size in bytes for clkmgr_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_CLKMGR_AON_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for sysrst_ctrl_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SYSRST_CTRL_AON_BASE_ADDR = 32'h40430000;

  /**
   * Peripheral size in bytes for sysrst_ctrl_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SYSRST_CTRL_AON_SIZE_BYTES = 32'h100;

  /**
   * Peripheral base address for adc_ctrl_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ADC_CTRL_AON_BASE_ADDR = 32'h40440000;

  /**
   * Peripheral size in bytes for adc_ctrl_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ADC_CTRL_AON_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for pwm_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_PWM_AON_BASE_ADDR = 32'h40450000;

  /**
   * Peripheral size in bytes for pwm_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_PWM_AON_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for pinmux_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_PINMUX_AON_BASE_ADDR = 32'h40460000;

  /**
   * Peripheral size in bytes for pinmux_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_PINMUX_AON_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for aon_timer_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR = 32'h40470000;

  /**
   * Peripheral size in bytes for aon_timer_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_AON_TIMER_AON_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for ast in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_AST_BASE_ADDR = 32'h40480000;

  /**
   * Peripheral size in bytes for ast in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_AST_SIZE_BYTES = 32'h400;

  /**
   * Peripheral base address for sensor_ctrl_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SENSOR_CTRL_AON_BASE_ADDR = 32'h40490000;

  /**
   * Peripheral size in bytes for sensor_ctrl_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SENSOR_CTRL_AON_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for regs device on sram_ctrl_ret_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_BASE_ADDR = 32'h40500000;

  /**
   * Peripheral size in bytes for regs device on sram_ctrl_ret_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_SIZE_BYTES = 32'h20;

  /**
   * Peripheral base address for ram device on sram_ctrl_ret_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR = 32'h40600000;

  /**
   * Peripheral size in bytes for ram device on sram_ctrl_ret_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for core device on flash_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR = 32'h41000000;

  /**
   * Peripheral size in bytes for core device on flash_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_FLASH_CTRL_CORE_SIZE_BYTES = 32'h200;

  /**
   * Peripheral base address for prim device on flash_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_FLASH_CTRL_PRIM_BASE_ADDR = 32'h41008000;

  /**
   * Peripheral size in bytes for prim device on flash_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_FLASH_CTRL_PRIM_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for mem device on flash_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR = 32'h20000000;

  /**
   * Peripheral size in bytes for mem device on flash_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_FLASH_CTRL_MEM_SIZE_BYTES = 32'h100000;

  /**
   * Peripheral base address for regs device on rv_dm in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_DM_REGS_BASE_ADDR = 32'h41200000;

  /**
   * Peripheral size in bytes for regs device on rv_dm in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_DM_REGS_SIZE_BYTES = 32'h4;

  /**
   * Peripheral base address for mem device on rv_dm in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_DM_MEM_BASE_ADDR = 32'h10000;

  /**
   * Peripheral size in bytes for mem device on rv_dm in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_DM_MEM_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for rv_plic in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_PLIC_BASE_ADDR = 32'h48000000;

  /**
   * Peripheral size in bytes for rv_plic in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_PLIC_SIZE_BYTES = 32'h8000000;

  /**
   * Peripheral base address for aes in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_AES_BASE_ADDR = 32'h41100000;

  /**
   * Peripheral size in bytes for aes in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_AES_SIZE_BYTES = 32'h100;

  /**
   * Peripheral base address for hmac in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_HMAC_BASE_ADDR = 32'h41110000;

  /**
   * Peripheral size in bytes for hmac in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_HMAC_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for kmac in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_KMAC_BASE_ADDR = 32'h41120000;

  /**
   * Peripheral size in bytes for kmac in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_KMAC_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for otbn in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_OTBN_BASE_ADDR = 32'h41130000;

  /**
   * Peripheral size in bytes for otbn in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_OTBN_SIZE_BYTES = 32'h10000;

  /**
   * Peripheral base address for keymgr in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_KEYMGR_BASE_ADDR = 32'h41140000;

  /**
   * Peripheral size in bytes for keymgr in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_KEYMGR_SIZE_BYTES = 32'h100;

  /**
   * Peripheral base address for csrng in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_CSRNG_BASE_ADDR = 32'h41150000;

  /**
   * Peripheral size in bytes for csrng in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_CSRNG_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for entropy_src in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR = 32'h41160000;

  /**
   * Peripheral size in bytes for entropy_src in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ENTROPY_SRC_SIZE_BYTES = 32'h100;

  /**
   * Peripheral base address for edn0 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_EDN0_BASE_ADDR = 32'h41170000;

  /**
   * Peripheral size in bytes for edn0 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_EDN0_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for edn1 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_EDN1_BASE_ADDR = 32'h41180000;

  /**
   * Peripheral size in bytes for edn1 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_EDN1_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for regs device on sram_ctrl_main in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR = 32'h411C0000;

  /**
   * Peripheral size in bytes for regs device on sram_ctrl_main in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_SIZE_BYTES = 32'h20;

  /**
   * Peripheral base address for ram device on sram_ctrl_main in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_BASE_ADDR = 32'h10000000;

  /**
   * Peripheral size in bytes for ram device on sram_ctrl_main in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_SIZE_BYTES = 32'h20000;

  /**
   * Peripheral base address for regs device on rom_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ROM_CTRL_REGS_BASE_ADDR = 32'h411E0000;

  /**
   * Peripheral size in bytes for regs device on rom_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ROM_CTRL_REGS_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for rom device on rom_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ROM_CTRL_ROM_BASE_ADDR = 32'h8000;

  /**
   * Peripheral size in bytes for rom device on rom_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ROM_CTRL_ROM_SIZE_BYTES = 32'h8000;

  /**
   * Peripheral base address for cfg device on rv_core_ibex in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR = 32'h411F0000;

  /**
   * Peripheral size in bytes for cfg device on rv_core_ibex in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_CORE_IBEX_CFG_SIZE_BYTES = 32'h100;

  /**
   * Memory base address for ram_ret_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RAM_RET_AON_BASE_ADDR = 32'h40600000;

  /**
   * Memory size for ram_ret_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RAM_RET_AON_SIZE_BYTES = 32'h1000;

  /**
   * Memory base address for eflash in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_EFLASH_BASE_ADDR = 32'h20000000;

  /**
   * Memory size for eflash in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_EFLASH_SIZE_BYTES = 32'h100000;

  /**
   * Memory base address for ram_main in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RAM_MAIN_BASE_ADDR = 32'h10000000;

  /**
   * Memory size for ram_main in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RAM_MAIN_SIZE_BYTES = 32'h20000;

  /**
   * Memory base address for rom in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ROM_BASE_ADDR = 32'h8000;

  /**
   * Memory size for rom in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ROM_SIZE_BYTES = 32'h8000;


  // Enumeration of alert modules
  typedef enum int unsigned {
    TopEarlgreyAlertPeripheralUart0 = 0,
    TopEarlgreyAlertPeripheralUart1 = 1,
    TopEarlgreyAlertPeripheralUart2 = 2,
    TopEarlgreyAlertPeripheralUart3 = 3,
    TopEarlgreyAlertPeripheralGpio = 4,
    TopEarlgreyAlertPeripheralSpiDevice = 5,
    TopEarlgreyAlertPeripheralI2c0 = 6,
    TopEarlgreyAlertPeripheralI2c1 = 7,
    TopEarlgreyAlertPeripheralI2c2 = 8,
    TopEarlgreyAlertPeripheralI2c3 = 9,
    TopEarlgreyAlertPeripheralPattgen = 10,
    TopEarlgreyAlertPeripheralRvTimer = 11,
    TopEarlgreyAlertPeripheralOtpCtrl = 12,
    TopEarlgreyAlertPeripheralLcCtrl = 13,
    TopEarlgreyAlertPeripheralSpiHost0 = 14,
    TopEarlgreyAlertPeripheralSpiHost1 = 15,
    TopEarlgreyAlertPeripheralUsbdev = 16,
    TopEarlgreyAlertPeripheralPwrmgrAon = 17,
    TopEarlgreyAlertPeripheralRstmgrAon = 18,
    TopEarlgreyAlertPeripheralClkmgrAon = 19,
    TopEarlgreyAlertPeripheralSysrstCtrlAon = 20,
    TopEarlgreyAlertPeripheralAdcCtrlAon = 21,
    TopEarlgreyAlertPeripheralPwmAon = 22,
    TopEarlgreyAlertPeripheralPinmuxAon = 23,
    TopEarlgreyAlertPeripheralAonTimerAon = 24,
    TopEarlgreyAlertPeripheralSensorCtrlAon = 25,
    TopEarlgreyAlertPeripheralSramCtrlRetAon = 26,
    TopEarlgreyAlertPeripheralFlashCtrl = 27,
    TopEarlgreyAlertPeripheralRvDm = 28,
    TopEarlgreyAlertPeripheralRvPlic = 29,
    TopEarlgreyAlertPeripheralAes = 30,
    TopEarlgreyAlertPeripheralHmac = 31,
    TopEarlgreyAlertPeripheralKmac = 32,
    TopEarlgreyAlertPeripheralOtbn = 33,
    TopEarlgreyAlertPeripheralKeymgr = 34,
    TopEarlgreyAlertPeripheralCsrng = 35,
    TopEarlgreyAlertPeripheralEntropySrc = 36,
    TopEarlgreyAlertPeripheralEdn0 = 37,
    TopEarlgreyAlertPeripheralEdn1 = 38,
    TopEarlgreyAlertPeripheralSramCtrlMain = 39,
    TopEarlgreyAlertPeripheralRomCtrl = 40,
    TopEarlgreyAlertPeripheralRvCoreIbex = 41,
    TopEarlgreyAlertPeripheralCount
  } alert_peripheral_e;

  // Enumeration of alerts
  typedef enum int unsigned {
    TopEarlgreyAlertIdUart0FatalFault = 0,
    TopEarlgreyAlertIdUart1FatalFault = 1,
    TopEarlgreyAlertIdUart2FatalFault = 2,
    TopEarlgreyAlertIdUart3FatalFault = 3,
    TopEarlgreyAlertIdGpioFatalFault = 4,
    TopEarlgreyAlertIdSpiDeviceFatalFault = 5,
    TopEarlgreyAlertIdI2c0FatalFault = 6,
    TopEarlgreyAlertIdI2c1FatalFault = 7,
    TopEarlgreyAlertIdI2c2FatalFault = 8,
    TopEarlgreyAlertIdI2c3FatalFault = 9,
    TopEarlgreyAlertIdPattgenFatalFault = 10,
    TopEarlgreyAlertIdRvTimerFatalFault = 11,
    TopEarlgreyAlertIdOtpCtrlFatalMacroError = 12,
    TopEarlgreyAlertIdOtpCtrlFatalCheckError = 13,
    TopEarlgreyAlertIdOtpCtrlFatalBusIntegError = 14,
    TopEarlgreyAlertIdOtpCtrlFatalPrimOtpAlert = 15,
    TopEarlgreyAlertIdOtpCtrlRecovPrimOtpAlert = 16,
    TopEarlgreyAlertIdLcCtrlFatalProgError = 17,
    TopEarlgreyAlertIdLcCtrlFatalStateError = 18,
    TopEarlgreyAlertIdLcCtrlFatalBusIntegError = 19,
    TopEarlgreyAlertIdSpiHost0FatalFault = 20,
    TopEarlgreyAlertIdSpiHost1FatalFault = 21,
    TopEarlgreyAlertIdUsbdevFatalFault = 22,
    TopEarlgreyAlertIdPwrmgrAonFatalFault = 23,
    TopEarlgreyAlertIdRstmgrAonFatalFault = 24,
    TopEarlgreyAlertIdRstmgrAonFatalCnstyFault = 25,
    TopEarlgreyAlertIdClkmgrAonRecovFault = 26,
    TopEarlgreyAlertIdClkmgrAonFatalFault = 27,
    TopEarlgreyAlertIdSysrstCtrlAonFatalFault = 28,
    TopEarlgreyAlertIdAdcCtrlAonFatalFault = 29,
    TopEarlgreyAlertIdPwmAonFatalFault = 30,
    TopEarlgreyAlertIdPinmuxAonFatalFault = 31,
    TopEarlgreyAlertIdAonTimerAonFatalFault = 32,
    TopEarlgreyAlertIdSensorCtrlAonRecovAlert = 33,
    TopEarlgreyAlertIdSensorCtrlAonFatalAlert = 34,
    TopEarlgreyAlertIdSramCtrlRetAonFatalError = 35,
    TopEarlgreyAlertIdFlashCtrlRecovErr = 36,
    TopEarlgreyAlertIdFlashCtrlFatalStdErr = 37,
    TopEarlgreyAlertIdFlashCtrlFatalErr = 38,
    TopEarlgreyAlertIdFlashCtrlFatalPrimFlashAlert = 39,
    TopEarlgreyAlertIdFlashCtrlRecovPrimFlashAlert = 40,
    TopEarlgreyAlertIdRvDmFatalFault = 41,
    TopEarlgreyAlertIdRvPlicFatalFault = 42,
    TopEarlgreyAlertIdAesRecovCtrlUpdateErr = 43,
    TopEarlgreyAlertIdAesFatalFault = 44,
    TopEarlgreyAlertIdHmacFatalFault = 45,
    TopEarlgreyAlertIdKmacRecovOperationErr = 46,
    TopEarlgreyAlertIdKmacFatalFaultErr = 47,
    TopEarlgreyAlertIdOtbnFatal = 48,
    TopEarlgreyAlertIdOtbnRecov = 49,
    TopEarlgreyAlertIdKeymgrRecovOperationErr = 50,
    TopEarlgreyAlertIdKeymgrFatalFaultErr = 51,
    TopEarlgreyAlertIdCsrngRecovAlert = 52,
    TopEarlgreyAlertIdCsrngFatalAlert = 53,
    TopEarlgreyAlertIdEntropySrcRecovAlert = 54,
    TopEarlgreyAlertIdEntropySrcFatalAlert = 55,
    TopEarlgreyAlertIdEdn0RecovAlert = 56,
    TopEarlgreyAlertIdEdn0FatalAlert = 57,
    TopEarlgreyAlertIdEdn1RecovAlert = 58,
    TopEarlgreyAlertIdEdn1FatalAlert = 59,
    TopEarlgreyAlertIdSramCtrlMainFatalError = 60,
    TopEarlgreyAlertIdRomCtrlFatal = 61,
    TopEarlgreyAlertIdRvCoreIbexFatalSwErr = 62,
    TopEarlgreyAlertIdRvCoreIbexRecovSwErr = 63,
    TopEarlgreyAlertIdRvCoreIbexFatalHwErr = 64,
    TopEarlgreyAlertIdRvCoreIbexRecovHwErr = 65,
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
    MioInI2c0Sda = 32,
    MioInI2c0Scl = 33,
    MioInI2c1Sda = 34,
    MioInI2c1Scl = 35,
    MioInI2c2Sda = 36,
    MioInI2c2Scl = 37,
    MioInI2c3Sda = 38,
    MioInI2c3Scl = 39,
    MioInSpiHost1Sd0 = 40,
    MioInSpiHost1Sd1 = 41,
    MioInSpiHost1Sd2 = 42,
    MioInSpiHost1Sd3 = 43,
    MioInUart0Rx = 44,
    MioInUart1Rx = 45,
    MioInUart2Rx = 46,
    MioInUart3Rx = 47,
    MioInSpiDeviceTpmCsb = 48,
    MioInFlashCtrlTck = 49,
    MioInFlashCtrlTms = 50,
    MioInFlashCtrlTdi = 51,
    MioInSysrstCtrlAonAcPresent = 52,
    MioInSysrstCtrlAonKey0In = 53,
    MioInSysrstCtrlAonKey1In = 54,
    MioInSysrstCtrlAonKey2In = 55,
    MioInSysrstCtrlAonPwrbIn = 56,
    MioInSysrstCtrlAonLidOpen = 57,
    MioInUsbdevSense = 58,
    MioInCount = 59
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
    MioOutI2c3Sda = 38,
    MioOutI2c3Scl = 39,
    MioOutSpiHost1Sd0 = 40,
    MioOutSpiHost1Sd1 = 41,
    MioOutSpiHost1Sd2 = 42,
    MioOutSpiHost1Sd3 = 43,
    MioOutUart0Tx = 44,
    MioOutUart1Tx = 45,
    MioOutUart2Tx = 46,
    MioOutUart3Tx = 47,
    MioOutPattgenPda0Tx = 48,
    MioOutPattgenPcl0Tx = 49,
    MioOutPattgenPda1Tx = 50,
    MioOutPattgenPcl1Tx = 51,
    MioOutSpiHost1Sck = 52,
    MioOutSpiHost1Csb = 53,
    MioOutFlashCtrlTdo = 54,
    MioOutSensorCtrlAonAstDebugOut0 = 55,
    MioOutSensorCtrlAonAstDebugOut1 = 56,
    MioOutSensorCtrlAonAstDebugOut2 = 57,
    MioOutSensorCtrlAonAstDebugOut3 = 58,
    MioOutSensorCtrlAonAstDebugOut4 = 59,
    MioOutSensorCtrlAonAstDebugOut5 = 60,
    MioOutSensorCtrlAonAstDebugOut6 = 61,
    MioOutSensorCtrlAonAstDebugOut7 = 62,
    MioOutSensorCtrlAonAstDebugOut8 = 63,
    MioOutPwmAonPwm0 = 64,
    MioOutPwmAonPwm1 = 65,
    MioOutPwmAonPwm2 = 66,
    MioOutPwmAonPwm3 = 67,
    MioOutPwmAonPwm4 = 68,
    MioOutPwmAonPwm5 = 69,
    MioOutOtpCtrlTest0 = 70,
    MioOutSysrstCtrlAonBatDisable = 71,
    MioOutSysrstCtrlAonKey0Out = 72,
    MioOutSysrstCtrlAonKey1Out = 73,
    MioOutSysrstCtrlAonKey2Out = 74,
    MioOutSysrstCtrlAonPwrbOut = 75,
    MioOutSysrstCtrlAonZ3Wakeup = 76,
    MioOutCount = 77
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
    PeripheralI2c3,
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
