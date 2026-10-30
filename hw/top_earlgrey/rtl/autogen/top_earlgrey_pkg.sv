// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
//
// util/topgen.py -t hw/top_earlgrey/data/top_earlgrey.hjson
//                -o hw/top_earlgrey/

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
   * Peripheral base address for gpio0 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_GPIO0_BASE_ADDR = 32'h40040000;

  /**
   * Peripheral size in bytes for gpio0 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_GPIO0_SIZE_BYTES = 32'h400;

  /**
   * Peripheral base address for gpio1 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_GPIO1_BASE_ADDR = 32'h40050000;

  /**
   * Peripheral size in bytes for gpio1 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_GPIO1_SIZE_BYTES = 32'h400;

  /**
   * Peripheral base address for spi_device in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SPI_DEVICE_BASE_ADDR = 32'h40060000;

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
   * Peripheral base address for i3c0 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_I3C0_BASE_ADDR = 32'h40330000;

  /**
   * Peripheral size in bytes for i3c0 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_I3C0_SIZE_BYTES = 32'h2000;

  /**
   * Peripheral base address for i3c1 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_I3C1_BASE_ADDR = 32'h40340000;

  /**
   * Peripheral size in bytes for i3c1 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_I3C1_SIZE_BYTES = 32'h2000;

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
  parameter int unsigned TOP_EARLGREY_OTP_CTRL_CORE_SIZE_BYTES = 32'h2000;

  /**
   * Peripheral base address for regs device on lc_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_LC_CTRL_REGS_BASE_ADDR = 32'h40140000;

  /**
   * Peripheral size in bytes for regs device on lc_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_LC_CTRL_REGS_SIZE_BYTES = 32'h100;

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
   * Peripheral base address for pwrmgr in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_PWRMGR_BASE_ADDR = 32'h40400000;

  /**
   * Peripheral size in bytes for pwrmgr in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_PWRMGR_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for rstmgr in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RSTMGR_BASE_ADDR = 32'h40410000;

  /**
   * Peripheral size in bytes for rstmgr in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RSTMGR_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for clkmgr in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_CLKMGR_BASE_ADDR = 32'h40420000;

  /**
   * Peripheral size in bytes for clkmgr in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_CLKMGR_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for sysrst_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SYSRST_CTRL_BASE_ADDR = 32'h40430000;

  /**
   * Peripheral size in bytes for sysrst_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SYSRST_CTRL_SIZE_BYTES = 32'h100;

  /**
   * Peripheral base address for adc_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ADC_CTRL_BASE_ADDR = 32'h40440000;

  /**
   * Peripheral size in bytes for adc_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ADC_CTRL_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for pinmux in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_PINMUX_BASE_ADDR = 32'h40460000;

  /**
   * Peripheral size in bytes for pinmux in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_PINMUX_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for aon_timer in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_AON_TIMER_BASE_ADDR = 32'h40470000;

  /**
   * Peripheral size in bytes for aon_timer in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_AON_TIMER_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for ast in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_AST_BASE_ADDR = 32'h40480000;

  /**
   * Peripheral size in bytes for ast in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_AST_SIZE_BYTES = 32'h400;

  /**
   * Peripheral base address for sensor_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SENSOR_CTRL_BASE_ADDR = 32'h40490000;

  /**
   * Peripheral size in bytes for sensor_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SENSOR_CTRL_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for regs device on sram_ctrl_ret in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_RET_REGS_BASE_ADDR = 32'h40500000;

  /**
   * Peripheral size in bytes for regs device on sram_ctrl_ret in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_RET_REGS_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for core device on rram_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RRAM_CTRL_CORE_BASE_ADDR = 32'h41010000;

  /**
   * Peripheral size in bytes for core device on rram_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RRAM_CTRL_CORE_SIZE_BYTES = 32'h400;

  /**
   * Peripheral base address for prim device on rram_macro in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RRAM_MACRO_PRIM_BASE_ADDR = 32'h41018000;

  /**
   * Peripheral size in bytes for prim device on rram_macro in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RRAM_MACRO_PRIM_SIZE_BYTES = 32'h10;

  /**
   * Peripheral base address for regs device on rv_dm in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_DM_REGS_BASE_ADDR = 32'h41200000;

  /**
   * Peripheral size in bytes for regs device on rv_dm in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_DM_REGS_SIZE_BYTES = 32'h10;

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
  parameter int unsigned TOP_EARLGREY_HMAC_SIZE_BYTES = 32'h2000;

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
   * Peripheral base address for keymgr_dpe in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_KEYMGR_DPE_BASE_ADDR = 32'h41140000;

  /**
   * Peripheral size in bytes for keymgr_dpe in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_KEYMGR_DPE_SIZE_BYTES = 32'h200;

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
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for regs device on sram_ctrl_sec in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_SEC_REGS_BASE_ADDR = 32'h411D0000;

  /**
   * Peripheral size in bytes for regs device on sram_ctrl_sec in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_SEC_REGS_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for regs device on rom_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ROM_CTRL_REGS_BASE_ADDR = 32'h411E0000;

  /**
   * Peripheral size in bytes for regs device on rom_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ROM_CTRL_REGS_SIZE_BYTES = 32'h80;

  /**
   * Peripheral base address for cfg device on rv_core_ibex in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR = 32'h411F0000;

  /**
   * Peripheral size in bytes for cfg device on rv_core_ibex in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_CORE_IBEX_CFG_SIZE_BYTES = 32'h100;

  /**
   * Peripheral base address for regs device on cheriot_mem_sys in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_CHERIOT_MEM_SYS_REGS_BASE_ADDR = 32'h411B0000;

  /**
   * Peripheral size in bytes for regs device on cheriot_mem_sys in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_CHERIOT_MEM_SYS_REGS_SIZE_BYTES = 32'h40;

  /**
   * Peripheral base address for regs device on sram_ctrl_meta in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_META_REGS_BASE_ADDR = 32'h411A0000;

  /**
   * Peripheral size in bytes for regs device on sram_ctrl_meta in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_META_REGS_SIZE_BYTES = 32'h40;

  /**
   * Memory base address for ram memory on sram_ctrl_ret in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_RET_RAM_BASE_ADDR = 32'h40600000;

  /**
   * Memory size for ram memory on sram_ctrl_ret in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_RET_RAM_SIZE_BYTES = 32'h2000;

  /**
   * Memory base address for host memory on rram_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RRAM_CTRL_HOST_BASE_ADDR = 32'h30000000;

  /**
   * Memory size for host memory on rram_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RRAM_CTRL_HOST_SIZE_BYTES = 32'h200000;

  /**
   * Memory base address for ram memory on sram_ctrl_main in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_BASE_ADDR = 32'h10000000;

  /**
   * Memory size for ram memory on sram_ctrl_main in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_SIZE_BYTES = 32'h20000;

  /**
   * Memory base address for ram memory on sram_ctrl_sec in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_SEC_RAM_BASE_ADDR = 32'h10020000;

  /**
   * Memory size for ram memory on sram_ctrl_sec in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_SEC_RAM_SIZE_BYTES = 32'h10000;

  /**
   * Memory base address for rom memory on rom_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ROM_CTRL_ROM_BASE_ADDR = 32'h40000;

  /**
   * Memory size for rom memory on rom_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ROM_CTRL_ROM_SIZE_BYTES = 32'h30000;

  /**
   * Memory base address for revbm memory on cheriot_mem_sys in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_CHERIOT_MEM_SYS_REVBM_BASE_ADDR = 32'h11000000;

  /**
   * Memory size for revbm memory on cheriot_mem_sys in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_CHERIOT_MEM_SYS_REVBM_SIZE_BYTES = 32'hc00;

  /**
   * Memory base address for ram memory on sram_ctrl_meta in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_META_RAM_BASE_ADDR = 32'h11000000;

  /**
   * Memory size for ram memory on sram_ctrl_meta in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_META_RAM_SIZE_BYTES = 32'h9800;


  // Enumeration of alert modules
  typedef enum int unsigned {
    TopEarlgreyAlertPeripheralUart0 = 0,
    TopEarlgreyAlertPeripheralUart1 = 1,
    TopEarlgreyAlertPeripheralUart2 = 2,
    TopEarlgreyAlertPeripheralUart3 = 3,
    TopEarlgreyAlertPeripheralGpio0 = 4,
    TopEarlgreyAlertPeripheralGpio1 = 5,
    TopEarlgreyAlertPeripheralSpiDevice = 6,
    TopEarlgreyAlertPeripheralI2c0 = 7,
    TopEarlgreyAlertPeripheralI2c1 = 8,
    TopEarlgreyAlertPeripheralI2c2 = 9,
    TopEarlgreyAlertPeripheralI3c0 = 10,
    TopEarlgreyAlertPeripheralI3c1 = 11,
    TopEarlgreyAlertPeripheralRvTimer = 12,
    TopEarlgreyAlertPeripheralOtpCtrl = 13,
    TopEarlgreyAlertPeripheralLcCtrl = 14,
    TopEarlgreyAlertPeripheralSpiHost0 = 15,
    TopEarlgreyAlertPeripheralSpiHost1 = 16,
    TopEarlgreyAlertPeripheralUsbdev = 17,
    TopEarlgreyAlertPeripheralPwrmgr = 18,
    TopEarlgreyAlertPeripheralRstmgr = 19,
    TopEarlgreyAlertPeripheralClkmgr = 20,
    TopEarlgreyAlertPeripheralSysrstCtrl = 21,
    TopEarlgreyAlertPeripheralAdcCtrl = 22,
    TopEarlgreyAlertPeripheralPinmux = 23,
    TopEarlgreyAlertPeripheralAonTimer = 24,
    TopEarlgreyAlertPeripheralSensorCtrl = 25,
    TopEarlgreyAlertPeripheralSramCtrlRet = 26,
    TopEarlgreyAlertPeripheralRramCtrl = 27,
    TopEarlgreyAlertPeripheralRvDm = 28,
    TopEarlgreyAlertPeripheralRvPlic = 29,
    TopEarlgreyAlertPeripheralAes = 30,
    TopEarlgreyAlertPeripheralHmac = 31,
    TopEarlgreyAlertPeripheralKmac = 32,
    TopEarlgreyAlertPeripheralOtbn = 33,
    TopEarlgreyAlertPeripheralKeymgrDpe = 34,
    TopEarlgreyAlertPeripheralCsrng = 35,
    TopEarlgreyAlertPeripheralEntropySrc = 36,
    TopEarlgreyAlertPeripheralEdn0 = 37,
    TopEarlgreyAlertPeripheralEdn1 = 38,
    TopEarlgreyAlertPeripheralSramCtrlMain = 39,
    TopEarlgreyAlertPeripheralSramCtrlSec = 40,
    TopEarlgreyAlertPeripheralRomCtrl = 41,
    TopEarlgreyAlertPeripheralRvCoreIbex = 42,
    TopEarlgreyAlertPeripheralCheriotMemSys = 43,
    TopEarlgreyAlertPeripheralSramCtrlMeta = 44,
    TopEarlgreyAlertPeripheralCount
  } alert_peripheral_e;

  // Enumeration of alerts
  typedef enum int unsigned {
    TopEarlgreyAlertIdUart0FatalFault = 0,
    TopEarlgreyAlertIdUart1FatalFault = 1,
    TopEarlgreyAlertIdUart2FatalFault = 2,
    TopEarlgreyAlertIdUart3FatalFault = 3,
    TopEarlgreyAlertIdGpio0FatalFault = 4,
    TopEarlgreyAlertIdGpio1FatalFault = 5,
    TopEarlgreyAlertIdSpiDeviceFatalFault = 6,
    TopEarlgreyAlertIdI2c0FatalFault = 7,
    TopEarlgreyAlertIdI2c1FatalFault = 8,
    TopEarlgreyAlertIdI2c2FatalFault = 9,
    TopEarlgreyAlertIdI3c0FatalFault = 10,
    TopEarlgreyAlertIdI3c1FatalFault = 11,
    TopEarlgreyAlertIdRvTimerFatalFault = 12,
    TopEarlgreyAlertIdOtpCtrlFatalMacroError = 13,
    TopEarlgreyAlertIdOtpCtrlFatalCheckError = 14,
    TopEarlgreyAlertIdOtpCtrlFatalBusIntegError = 15,
    TopEarlgreyAlertIdOtpCtrlFatalPrimOtpAlert = 16,
    TopEarlgreyAlertIdOtpCtrlRecovPrimOtpAlert = 17,
    TopEarlgreyAlertIdLcCtrlFatalProgError = 18,
    TopEarlgreyAlertIdLcCtrlFatalStateError = 19,
    TopEarlgreyAlertIdLcCtrlFatalBusIntegError = 20,
    TopEarlgreyAlertIdSpiHost0FatalFault = 21,
    TopEarlgreyAlertIdSpiHost1FatalFault = 22,
    TopEarlgreyAlertIdUsbdevFatalFault = 23,
    TopEarlgreyAlertIdPwrmgrFatalFault = 24,
    TopEarlgreyAlertIdRstmgrFatalFault = 25,
    TopEarlgreyAlertIdRstmgrFatalCnstyFault = 26,
    TopEarlgreyAlertIdClkmgrRecovFault = 27,
    TopEarlgreyAlertIdClkmgrFatalFault = 28,
    TopEarlgreyAlertIdSysrstCtrlFatalFault = 29,
    TopEarlgreyAlertIdAdcCtrlFatalFault = 30,
    TopEarlgreyAlertIdPinmuxFatalFault = 31,
    TopEarlgreyAlertIdAonTimerFatalFault = 32,
    TopEarlgreyAlertIdSensorCtrlRecovAlert = 33,
    TopEarlgreyAlertIdSensorCtrlFatalAlert = 34,
    TopEarlgreyAlertIdSramCtrlRetFatalError = 35,
    TopEarlgreyAlertIdRramCtrlRecovErr = 36,
    TopEarlgreyAlertIdRramCtrlFatalStdErr = 37,
    TopEarlgreyAlertIdRramCtrlFatalErr = 38,
    TopEarlgreyAlertIdRramCtrlFatalMacroErr = 39,
    TopEarlgreyAlertIdRramCtrlRecovMacroErr = 40,
    TopEarlgreyAlertIdRvDmFatalFault = 41,
    TopEarlgreyAlertIdRvPlicFatalFault = 42,
    TopEarlgreyAlertIdAesRecovCtrlUpdateErr = 43,
    TopEarlgreyAlertIdAesFatalFault = 44,
    TopEarlgreyAlertIdHmacFatalFault = 45,
    TopEarlgreyAlertIdKmacRecovOperationErr = 46,
    TopEarlgreyAlertIdKmacFatalFaultErr = 47,
    TopEarlgreyAlertIdOtbnFatal = 48,
    TopEarlgreyAlertIdOtbnRecov = 49,
    TopEarlgreyAlertIdKeymgrDpeRecovOperationErr = 50,
    TopEarlgreyAlertIdKeymgrDpeFatalFaultErr = 51,
    TopEarlgreyAlertIdCsrngRecovAlert = 52,
    TopEarlgreyAlertIdCsrngFatalAlert = 53,
    TopEarlgreyAlertIdEntropySrcRecovAlert = 54,
    TopEarlgreyAlertIdEntropySrcFatalAlert = 55,
    TopEarlgreyAlertIdEdn0RecovAlert = 56,
    TopEarlgreyAlertIdEdn0FatalAlert = 57,
    TopEarlgreyAlertIdEdn1RecovAlert = 58,
    TopEarlgreyAlertIdEdn1FatalAlert = 59,
    TopEarlgreyAlertIdSramCtrlMainFatalError = 60,
    TopEarlgreyAlertIdSramCtrlSecFatalError = 61,
    TopEarlgreyAlertIdRomCtrlFatal = 62,
    TopEarlgreyAlertIdRvCoreIbexFatalSwErr = 63,
    TopEarlgreyAlertIdRvCoreIbexRecovSwErr = 64,
    TopEarlgreyAlertIdRvCoreIbexFatalHwErr = 65,
    TopEarlgreyAlertIdRvCoreIbexRecovHwErr = 66,
    TopEarlgreyAlertIdCheriotMemSysFatalFault = 67,
    TopEarlgreyAlertIdSramCtrlMetaFatalError = 68,
    TopEarlgreyAlertIdCount
  } alert_id_e;

  // Enumeration of interrupts
  typedef enum int unsigned {
    TopEarlgreyPlicIrqIdNone = 0,
    TopEarlgreyPlicIrqIdUart0TxWatermark = 1,
    TopEarlgreyPlicIrqIdUart0RxWatermark = 2,
    TopEarlgreyPlicIrqIdUart0TxDone = 3,
    TopEarlgreyPlicIrqIdUart0RxOverflow = 4,
    TopEarlgreyPlicIrqIdUart0RxFrameErr = 5,
    TopEarlgreyPlicIrqIdUart0RxBreakErr = 6,
    TopEarlgreyPlicIrqIdUart0RxTimeout = 7,
    TopEarlgreyPlicIrqIdUart0RxParityErr = 8,
    TopEarlgreyPlicIrqIdUart0TxEmpty = 9,
    TopEarlgreyPlicIrqIdUart1TxWatermark = 10,
    TopEarlgreyPlicIrqIdUart1RxWatermark = 11,
    TopEarlgreyPlicIrqIdUart1TxDone = 12,
    TopEarlgreyPlicIrqIdUart1RxOverflow = 13,
    TopEarlgreyPlicIrqIdUart1RxFrameErr = 14,
    TopEarlgreyPlicIrqIdUart1RxBreakErr = 15,
    TopEarlgreyPlicIrqIdUart1RxTimeout = 16,
    TopEarlgreyPlicIrqIdUart1RxParityErr = 17,
    TopEarlgreyPlicIrqIdUart1TxEmpty = 18,
    TopEarlgreyPlicIrqIdUart2TxWatermark = 19,
    TopEarlgreyPlicIrqIdUart2RxWatermark = 20,
    TopEarlgreyPlicIrqIdUart2TxDone = 21,
    TopEarlgreyPlicIrqIdUart2RxOverflow = 22,
    TopEarlgreyPlicIrqIdUart2RxFrameErr = 23,
    TopEarlgreyPlicIrqIdUart2RxBreakErr = 24,
    TopEarlgreyPlicIrqIdUart2RxTimeout = 25,
    TopEarlgreyPlicIrqIdUart2RxParityErr = 26,
    TopEarlgreyPlicIrqIdUart2TxEmpty = 27,
    TopEarlgreyPlicIrqIdUart3TxWatermark = 28,
    TopEarlgreyPlicIrqIdUart3RxWatermark = 29,
    TopEarlgreyPlicIrqIdUart3TxDone = 30,
    TopEarlgreyPlicIrqIdUart3RxOverflow = 31,
    TopEarlgreyPlicIrqIdUart3RxFrameErr = 32,
    TopEarlgreyPlicIrqIdUart3RxBreakErr = 33,
    TopEarlgreyPlicIrqIdUart3RxTimeout = 34,
    TopEarlgreyPlicIrqIdUart3RxParityErr = 35,
    TopEarlgreyPlicIrqIdUart3TxEmpty = 36,
    TopEarlgreyPlicIrqIdGpio0Gpio0 = 37,
    TopEarlgreyPlicIrqIdGpio0Gpio1 = 38,
    TopEarlgreyPlicIrqIdGpio0Gpio2 = 39,
    TopEarlgreyPlicIrqIdGpio0Gpio3 = 40,
    TopEarlgreyPlicIrqIdGpio0Gpio4 = 41,
    TopEarlgreyPlicIrqIdGpio0Gpio5 = 42,
    TopEarlgreyPlicIrqIdGpio0Gpio6 = 43,
    TopEarlgreyPlicIrqIdGpio0Gpio7 = 44,
    TopEarlgreyPlicIrqIdGpio0Gpio8 = 45,
    TopEarlgreyPlicIrqIdGpio0Gpio9 = 46,
    TopEarlgreyPlicIrqIdGpio0Gpio10 = 47,
    TopEarlgreyPlicIrqIdGpio0Gpio11 = 48,
    TopEarlgreyPlicIrqIdGpio0Gpio12 = 49,
    TopEarlgreyPlicIrqIdGpio0Gpio13 = 50,
    TopEarlgreyPlicIrqIdGpio0Gpio14 = 51,
    TopEarlgreyPlicIrqIdGpio0Gpio15 = 52,
    TopEarlgreyPlicIrqIdGpio0Gpio16 = 53,
    TopEarlgreyPlicIrqIdGpio0Gpio17 = 54,
    TopEarlgreyPlicIrqIdGpio0Gpio18 = 55,
    TopEarlgreyPlicIrqIdGpio0Gpio19 = 56,
    TopEarlgreyPlicIrqIdGpio0Gpio20 = 57,
    TopEarlgreyPlicIrqIdGpio0Gpio21 = 58,
    TopEarlgreyPlicIrqIdGpio0Gpio22 = 59,
    TopEarlgreyPlicIrqIdGpio0Gpio23 = 60,
    TopEarlgreyPlicIrqIdGpio0Gpio24 = 61,
    TopEarlgreyPlicIrqIdGpio0Gpio25 = 62,
    TopEarlgreyPlicIrqIdGpio0Gpio26 = 63,
    TopEarlgreyPlicIrqIdGpio0Gpio27 = 64,
    TopEarlgreyPlicIrqIdGpio0Gpio28 = 65,
    TopEarlgreyPlicIrqIdGpio0Gpio29 = 66,
    TopEarlgreyPlicIrqIdGpio0Gpio30 = 67,
    TopEarlgreyPlicIrqIdGpio0Gpio31 = 68,
    TopEarlgreyPlicIrqIdGpio1Gpio0 = 69,
    TopEarlgreyPlicIrqIdGpio1Gpio1 = 70,
    TopEarlgreyPlicIrqIdGpio1Gpio2 = 71,
    TopEarlgreyPlicIrqIdGpio1Gpio3 = 72,
    TopEarlgreyPlicIrqIdGpio1Gpio4 = 73,
    TopEarlgreyPlicIrqIdGpio1Gpio5 = 74,
    TopEarlgreyPlicIrqIdGpio1Gpio6 = 75,
    TopEarlgreyPlicIrqIdGpio1Gpio7 = 76,
    TopEarlgreyPlicIrqIdGpio1Gpio8 = 77,
    TopEarlgreyPlicIrqIdGpio1Gpio9 = 78,
    TopEarlgreyPlicIrqIdGpio1Gpio10 = 79,
    TopEarlgreyPlicIrqIdGpio1Gpio11 = 80,
    TopEarlgreyPlicIrqIdGpio1Gpio12 = 81,
    TopEarlgreyPlicIrqIdGpio1Gpio13 = 82,
    TopEarlgreyPlicIrqIdGpio1Gpio14 = 83,
    TopEarlgreyPlicIrqIdGpio1Gpio15 = 84,
    TopEarlgreyPlicIrqIdGpio1Gpio16 = 85,
    TopEarlgreyPlicIrqIdGpio1Gpio17 = 86,
    TopEarlgreyPlicIrqIdGpio1Gpio18 = 87,
    TopEarlgreyPlicIrqIdGpio1Gpio19 = 88,
    TopEarlgreyPlicIrqIdGpio1Gpio20 = 89,
    TopEarlgreyPlicIrqIdGpio1Gpio21 = 90,
    TopEarlgreyPlicIrqIdGpio1Gpio22 = 91,
    TopEarlgreyPlicIrqIdGpio1Gpio23 = 92,
    TopEarlgreyPlicIrqIdGpio1Gpio24 = 93,
    TopEarlgreyPlicIrqIdGpio1Gpio25 = 94,
    TopEarlgreyPlicIrqIdGpio1Gpio26 = 95,
    TopEarlgreyPlicIrqIdGpio1Gpio27 = 96,
    TopEarlgreyPlicIrqIdGpio1Gpio28 = 97,
    TopEarlgreyPlicIrqIdGpio1Gpio29 = 98,
    TopEarlgreyPlicIrqIdGpio1Gpio30 = 99,
    TopEarlgreyPlicIrqIdGpio1Gpio31 = 100,
    TopEarlgreyPlicIrqIdSpiDeviceUploadCmdfifoNotEmpty = 101,
    TopEarlgreyPlicIrqIdSpiDeviceUploadPayloadNotEmpty = 102,
    TopEarlgreyPlicIrqIdSpiDeviceUploadPayloadOverflow = 103,
    TopEarlgreyPlicIrqIdSpiDeviceReadbufWatermark = 104,
    TopEarlgreyPlicIrqIdSpiDeviceReadbufFlip = 105,
    TopEarlgreyPlicIrqIdSpiDeviceTpmHeaderNotEmpty = 106,
    TopEarlgreyPlicIrqIdSpiDeviceTpmRdfifoCmdEnd = 107,
    TopEarlgreyPlicIrqIdSpiDeviceTpmRdfifoDrop = 108,
    TopEarlgreyPlicIrqIdI2c0FmtThreshold = 109,
    TopEarlgreyPlicIrqIdI2c0RxThreshold = 110,
    TopEarlgreyPlicIrqIdI2c0AcqThreshold = 111,
    TopEarlgreyPlicIrqIdI2c0RxOverflow = 112,
    TopEarlgreyPlicIrqIdI2c0ControllerHalt = 113,
    TopEarlgreyPlicIrqIdI2c0SclInterference = 114,
    TopEarlgreyPlicIrqIdI2c0SdaInterference = 115,
    TopEarlgreyPlicIrqIdI2c0StretchTimeout = 116,
    TopEarlgreyPlicIrqIdI2c0SdaUnstable = 117,
    TopEarlgreyPlicIrqIdI2c0CmdComplete = 118,
    TopEarlgreyPlicIrqIdI2c0TxStretch = 119,
    TopEarlgreyPlicIrqIdI2c0TxThreshold = 120,
    TopEarlgreyPlicIrqIdI2c0AcqStretch = 121,
    TopEarlgreyPlicIrqIdI2c0UnexpStop = 122,
    TopEarlgreyPlicIrqIdI2c0HostTimeout = 123,
    TopEarlgreyPlicIrqIdI2c1FmtThreshold = 124,
    TopEarlgreyPlicIrqIdI2c1RxThreshold = 125,
    TopEarlgreyPlicIrqIdI2c1AcqThreshold = 126,
    TopEarlgreyPlicIrqIdI2c1RxOverflow = 127,
    TopEarlgreyPlicIrqIdI2c1ControllerHalt = 128,
    TopEarlgreyPlicIrqIdI2c1SclInterference = 129,
    TopEarlgreyPlicIrqIdI2c1SdaInterference = 130,
    TopEarlgreyPlicIrqIdI2c1StretchTimeout = 131,
    TopEarlgreyPlicIrqIdI2c1SdaUnstable = 132,
    TopEarlgreyPlicIrqIdI2c1CmdComplete = 133,
    TopEarlgreyPlicIrqIdI2c1TxStretch = 134,
    TopEarlgreyPlicIrqIdI2c1TxThreshold = 135,
    TopEarlgreyPlicIrqIdI2c1AcqStretch = 136,
    TopEarlgreyPlicIrqIdI2c1UnexpStop = 137,
    TopEarlgreyPlicIrqIdI2c1HostTimeout = 138,
    TopEarlgreyPlicIrqIdI2c2FmtThreshold = 139,
    TopEarlgreyPlicIrqIdI2c2RxThreshold = 140,
    TopEarlgreyPlicIrqIdI2c2AcqThreshold = 141,
    TopEarlgreyPlicIrqIdI2c2RxOverflow = 142,
    TopEarlgreyPlicIrqIdI2c2ControllerHalt = 143,
    TopEarlgreyPlicIrqIdI2c2SclInterference = 144,
    TopEarlgreyPlicIrqIdI2c2SdaInterference = 145,
    TopEarlgreyPlicIrqIdI2c2StretchTimeout = 146,
    TopEarlgreyPlicIrqIdI2c2SdaUnstable = 147,
    TopEarlgreyPlicIrqIdI2c2CmdComplete = 148,
    TopEarlgreyPlicIrqIdI2c2TxStretch = 149,
    TopEarlgreyPlicIrqIdI2c2TxThreshold = 150,
    TopEarlgreyPlicIrqIdI2c2AcqStretch = 151,
    TopEarlgreyPlicIrqIdI2c2UnexpStop = 152,
    TopEarlgreyPlicIrqIdI2c2HostTimeout = 153,
    TopEarlgreyPlicIrqIdI3c0Hci = 154,
    TopEarlgreyPlicIrqIdI3c0Targ = 155,
    TopEarlgreyPlicIrqIdI3c1Hci = 156,
    TopEarlgreyPlicIrqIdI3c1Targ = 157,
    TopEarlgreyPlicIrqIdRvTimerTimerExpiredHart0Timer0 = 158,
    TopEarlgreyPlicIrqIdOtpCtrlOtpOperationDone = 159,
    TopEarlgreyPlicIrqIdOtpCtrlOtpError = 160,
    TopEarlgreyPlicIrqIdAlertHandlerClassa = 161,
    TopEarlgreyPlicIrqIdAlertHandlerClassb = 162,
    TopEarlgreyPlicIrqIdAlertHandlerClassc = 163,
    TopEarlgreyPlicIrqIdAlertHandlerClassd = 164,
    TopEarlgreyPlicIrqIdSpiHost0Error = 165,
    TopEarlgreyPlicIrqIdSpiHost0SpiEvent = 166,
    TopEarlgreyPlicIrqIdSpiHost1Error = 167,
    TopEarlgreyPlicIrqIdSpiHost1SpiEvent = 168,
    TopEarlgreyPlicIrqIdUsbdevPktReceived = 169,
    TopEarlgreyPlicIrqIdUsbdevPktSent = 170,
    TopEarlgreyPlicIrqIdUsbdevDisconnected = 171,
    TopEarlgreyPlicIrqIdUsbdevHostLost = 172,
    TopEarlgreyPlicIrqIdUsbdevLinkReset = 173,
    TopEarlgreyPlicIrqIdUsbdevLinkSuspend = 174,
    TopEarlgreyPlicIrqIdUsbdevLinkResume = 175,
    TopEarlgreyPlicIrqIdUsbdevAvOutEmpty = 176,
    TopEarlgreyPlicIrqIdUsbdevRxFull = 177,
    TopEarlgreyPlicIrqIdUsbdevAvOverflow = 178,
    TopEarlgreyPlicIrqIdUsbdevLinkInErr = 179,
    TopEarlgreyPlicIrqIdUsbdevRxCrcErr = 180,
    TopEarlgreyPlicIrqIdUsbdevRxPidErr = 181,
    TopEarlgreyPlicIrqIdUsbdevRxBitstuffErr = 182,
    TopEarlgreyPlicIrqIdUsbdevFrame = 183,
    TopEarlgreyPlicIrqIdUsbdevPowered = 184,
    TopEarlgreyPlicIrqIdUsbdevLinkOutErr = 185,
    TopEarlgreyPlicIrqIdUsbdevAvSetupEmpty = 186,
    TopEarlgreyPlicIrqIdPwrmgrWakeup = 187,
    TopEarlgreyPlicIrqIdSysrstCtrlEventDetected = 188,
    TopEarlgreyPlicIrqIdAdcCtrlMatchPending = 189,
    TopEarlgreyPlicIrqIdAonTimerWkupTimerExpired = 190,
    TopEarlgreyPlicIrqIdAonTimerWdogTimerBark = 191,
    TopEarlgreyPlicIrqIdSensorCtrlIoStatusChange = 192,
    TopEarlgreyPlicIrqIdSensorCtrlInitStatusChange = 193,
    TopEarlgreyPlicIrqIdRramCtrlWrEmpty = 194,
    TopEarlgreyPlicIrqIdRramCtrlWrLvl = 195,
    TopEarlgreyPlicIrqIdRramCtrlRdFull = 196,
    TopEarlgreyPlicIrqIdRramCtrlRdLvl = 197,
    TopEarlgreyPlicIrqIdRramCtrlOpDone = 198,
    TopEarlgreyPlicIrqIdRramCtrlCorr1Err = 199,
    TopEarlgreyPlicIrqIdRramCtrlCorr2Err = 200,
    TopEarlgreyPlicIrqIdHmacHmacDone = 201,
    TopEarlgreyPlicIrqIdHmacFifoEmpty = 202,
    TopEarlgreyPlicIrqIdHmacHmacErr = 203,
    TopEarlgreyPlicIrqIdKmacKmacDone = 204,
    TopEarlgreyPlicIrqIdKmacFifoEmpty = 205,
    TopEarlgreyPlicIrqIdKmacKmacErr = 206,
    TopEarlgreyPlicIrqIdOtbnDone = 207,
    TopEarlgreyPlicIrqIdKeymgrDpeOpDone = 208,
    TopEarlgreyPlicIrqIdCsrngCsCmdReqDone = 209,
    TopEarlgreyPlicIrqIdCsrngCsEntropyReq = 210,
    TopEarlgreyPlicIrqIdCsrngCsHwInstExc = 211,
    TopEarlgreyPlicIrqIdCsrngCsFatalErr = 212,
    TopEarlgreyPlicIrqIdEntropySrcEsEntropyValid = 213,
    TopEarlgreyPlicIrqIdEntropySrcEsHealthTestFailed = 214,
    TopEarlgreyPlicIrqIdEntropySrcEsObserveFifoReady = 215,
    TopEarlgreyPlicIrqIdEntropySrcEsFatalErr = 216,
    TopEarlgreyPlicIrqIdEdn0EdnCmdReqDone = 217,
    TopEarlgreyPlicIrqIdEdn0EdnFatalErr = 218,
    TopEarlgreyPlicIrqIdEdn1EdnCmdReqDone = 219,
    TopEarlgreyPlicIrqIdEdn1EdnFatalErr = 220,
    TopEarlgreyPlicIrqIdCheriotMemSysTbreDone = 221,
    TopEarlgreyPlicIrqIdCount
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
    MioInGpio1Gpio0 = 32,
    MioInGpio1Gpio1 = 33,
    MioInGpio1Gpio2 = 34,
    MioInGpio1Gpio3 = 35,
    MioInGpio1Gpio4 = 36,
    MioInGpio1Gpio5 = 37,
    MioInGpio1Gpio6 = 38,
    MioInGpio1Gpio7 = 39,
    MioInGpio1Gpio8 = 40,
    MioInGpio1Gpio9 = 41,
    MioInGpio1Gpio10 = 42,
    MioInGpio1Gpio11 = 43,
    MioInGpio1Gpio12 = 44,
    MioInGpio1Gpio13 = 45,
    MioInGpio1Gpio14 = 46,
    MioInGpio1Gpio15 = 47,
    MioInGpio1Gpio16 = 48,
    MioInGpio1Gpio17 = 49,
    MioInGpio1Gpio18 = 50,
    MioInGpio1Gpio19 = 51,
    MioInGpio1Gpio20 = 52,
    MioInGpio1Gpio21 = 53,
    MioInGpio1Gpio22 = 54,
    MioInGpio1Gpio23 = 55,
    MioInGpio1Gpio24 = 56,
    MioInGpio1Gpio25 = 57,
    MioInGpio1Gpio26 = 58,
    MioInGpio1Gpio27 = 59,
    MioInGpio1Gpio28 = 60,
    MioInGpio1Gpio29 = 61,
    MioInGpio1Gpio30 = 62,
    MioInGpio1Gpio31 = 63,
    MioInI2c0Sda = 64,
    MioInI2c0Scl = 65,
    MioInI2c1Sda = 66,
    MioInI2c1Scl = 67,
    MioInI2c2Sda = 68,
    MioInI2c2Scl = 69,
    MioInI3c0Scl = 70,
    MioInI3c0Sda = 71,
    MioInI3c1Scl = 72,
    MioInI3c1Sda = 73,
    MioInSpiHost1Sd0 = 74,
    MioInSpiHost1Sd1 = 75,
    MioInSpiHost1Sd2 = 76,
    MioInSpiHost1Sd3 = 77,
    MioInUart0Rx = 78,
    MioInUart1Rx = 79,
    MioInUart2Rx = 80,
    MioInUart3Rx = 81,
    MioInI3c0RstdetScl = 82,
    MioInI3c0RstdetSda = 83,
    MioInI3c1RstdetScl = 84,
    MioInI3c1RstdetSda = 85,
    MioInSpiDeviceTpmCsb = 86,
    MioInRramMacroTck = 87,
    MioInRramMacroTms = 88,
    MioInRramMacroTdi = 89,
    MioInSysrstCtrlAcPresent = 90,
    MioInSysrstCtrlKey0In = 91,
    MioInSysrstCtrlKey1In = 92,
    MioInSysrstCtrlKey2In = 93,
    MioInSysrstCtrlPwrbIn = 94,
    MioInSysrstCtrlLidOpen = 95,
    MioInUsbdevSense = 96,
    MioInCount = 97
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
    MioOutGpio1Gpio0 = 32,
    MioOutGpio1Gpio1 = 33,
    MioOutGpio1Gpio2 = 34,
    MioOutGpio1Gpio3 = 35,
    MioOutGpio1Gpio4 = 36,
    MioOutGpio1Gpio5 = 37,
    MioOutGpio1Gpio6 = 38,
    MioOutGpio1Gpio7 = 39,
    MioOutGpio1Gpio8 = 40,
    MioOutGpio1Gpio9 = 41,
    MioOutGpio1Gpio10 = 42,
    MioOutGpio1Gpio11 = 43,
    MioOutGpio1Gpio12 = 44,
    MioOutGpio1Gpio13 = 45,
    MioOutGpio1Gpio14 = 46,
    MioOutGpio1Gpio15 = 47,
    MioOutGpio1Gpio16 = 48,
    MioOutGpio1Gpio17 = 49,
    MioOutGpio1Gpio18 = 50,
    MioOutGpio1Gpio19 = 51,
    MioOutGpio1Gpio20 = 52,
    MioOutGpio1Gpio21 = 53,
    MioOutGpio1Gpio22 = 54,
    MioOutGpio1Gpio23 = 55,
    MioOutGpio1Gpio24 = 56,
    MioOutGpio1Gpio25 = 57,
    MioOutGpio1Gpio26 = 58,
    MioOutGpio1Gpio27 = 59,
    MioOutGpio1Gpio28 = 60,
    MioOutGpio1Gpio29 = 61,
    MioOutGpio1Gpio30 = 62,
    MioOutGpio1Gpio31 = 63,
    MioOutI2c0Sda = 64,
    MioOutI2c0Scl = 65,
    MioOutI2c1Sda = 66,
    MioOutI2c1Scl = 67,
    MioOutI2c2Sda = 68,
    MioOutI2c2Scl = 69,
    MioOutI3c0Scl = 70,
    MioOutI3c0Sda = 71,
    MioOutI3c1Scl = 72,
    MioOutI3c1Sda = 73,
    MioOutSpiHost1Sd0 = 74,
    MioOutSpiHost1Sd1 = 75,
    MioOutSpiHost1Sd2 = 76,
    MioOutSpiHost1Sd3 = 77,
    MioOutUart0Tx = 78,
    MioOutUart1Tx = 79,
    MioOutUart2Tx = 80,
    MioOutUart3Tx = 81,
    MioOutI3c0CtrlSdaPu = 82,
    MioOutI3c1CtrlSdaPu = 83,
    MioOutSpiHost1Sck = 84,
    MioOutSpiHost1Csb = 85,
    MioOutRramMacroTdo = 86,
    MioOutSensorCtrlAstDebugOut0 = 87,
    MioOutSensorCtrlAstDebugOut1 = 88,
    MioOutSensorCtrlAstDebugOut2 = 89,
    MioOutSensorCtrlAstDebugOut3 = 90,
    MioOutSensorCtrlAstDebugOut4 = 91,
    MioOutSensorCtrlAstDebugOut5 = 92,
    MioOutSensorCtrlAstDebugOut6 = 93,
    MioOutSensorCtrlAstDebugOut7 = 94,
    MioOutSensorCtrlAstDebugOut8 = 95,
    MioOutSysrstCtrlBatDisable = 96,
    MioOutSysrstCtrlKey0Out = 97,
    MioOutSysrstCtrlKey1Out = 98,
    MioOutSysrstCtrlKey2Out = 99,
    MioOutSysrstCtrlPwrbOut = 100,
    MioOutSysrstCtrlZ3Wakeup = 101,
    MioOutCount = 102
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
    DioSysrstCtrlEcRstL = 10,
    DioSysrstCtrlFlashWpL = 11,
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
    DioPadPoraN = 1,
    DioPadUsbP = 2,
    DioPadUsbN = 3,
    DioPadCc1 = 4,
    DioPadCc2 = 5,
    DioPadRramAnalog = 6,
    DioPadSpiHostD0 = 7,
    DioPadSpiHostD1 = 8,
    DioPadSpiHostD2 = 9,
    DioPadSpiHostD3 = 10,
    DioPadSpiHostClk = 11,
    DioPadSpiHostCsL = 12,
    DioPadSpiDevD0 = 13,
    DioPadSpiDevD1 = 14,
    DioPadSpiDevD2 = 15,
    DioPadSpiDevD3 = 16,
    DioPadSpiDevClk = 17,
    DioPadSpiDevCsL = 18,
    DioPadIor8 = 19,
    DioPadIor9 = 20,
    DioPadCount
  } dio_pad_e;

  // List of peripheral instantiated in this chip.
  typedef enum {
    PeripheralAdcCtrl,
    PeripheralAes,
    PeripheralAlertHandler,
    PeripheralAonTimer,
    PeripheralAst,
    PeripheralCheriotMemSys,
    PeripheralClkmgr,
    PeripheralCsrng,
    PeripheralEdn0,
    PeripheralEdn1,
    PeripheralEntropySrc,
    PeripheralGpio0,
    PeripheralGpio1,
    PeripheralHmac,
    PeripheralI2c0,
    PeripheralI2c1,
    PeripheralI2c2,
    PeripheralI3c0,
    PeripheralI3c1,
    PeripheralKeymgrDpe,
    PeripheralKmac,
    PeripheralLcCtrl,
    PeripheralOtbn,
    PeripheralOtpCtrl,
    PeripheralPinmux,
    PeripheralPwrmgr,
    PeripheralRomCtrl,
    PeripheralRramCtrl,
    PeripheralRramMacro,
    PeripheralRstmgr,
    PeripheralRvCoreIbex,
    PeripheralRvDm,
    PeripheralRvPlic,
    PeripheralRvTimer,
    PeripheralSensorCtrl,
    PeripheralSpiDevice,
    PeripheralSpiHost0,
    PeripheralSpiHost1,
    PeripheralSramCtrlMain,
    PeripheralSramCtrlMeta,
    PeripheralSramCtrlRet,
    PeripheralSramCtrlSec,
    PeripheralSysrstCtrl,
    PeripheralUart0,
    PeripheralUart1,
    PeripheralUart2,
    PeripheralUart3,
    PeripheralUsbdev,
    PeripheralCount
  } peripheral_e;

  // MMIO Region
  //
  parameter int unsigned TOP_EARLGREY_MMIO_BASE_ADDR = 32'h40000000;
  parameter int unsigned TOP_EARLGREY_MMIO_SIZE_BYTES = 32'h10000000;

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
