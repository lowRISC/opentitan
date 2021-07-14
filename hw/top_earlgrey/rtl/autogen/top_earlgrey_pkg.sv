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
   * Peripheral base address for uart0 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_UART0_BASE_ADDR = 32'h40000000;

  /**
   * Peripheral size in bytes for uart0 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_UART0_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for uart1 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_UART1_BASE_ADDR = 32'h40010000;

  /**
   * Peripheral size in bytes for uart1 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_UART1_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for uart2 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_UART2_BASE_ADDR = 32'h40020000;

  /**
   * Peripheral size in bytes for uart2 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_UART2_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for uart3 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_UART3_BASE_ADDR = 32'h40030000;

  /**
   * Peripheral size in bytes for uart3 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_UART3_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for gpio in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_GPIO_BASE_ADDR = 32'h40040000;

  /**
   * Peripheral size in bytes for gpio in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_GPIO_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for spi_device in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SPI_DEVICE_BASE_ADDR = 32'h40050000;

  /**
   * Peripheral size in bytes for spi_device in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SPI_DEVICE_SIZE_BYTES = 32'h2000;

  /**
   * Peripheral base address for spi_host0 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SPI_HOST0_BASE_ADDR = 32'h40060000;

  /**
   * Peripheral size in bytes for spi_host0 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SPI_HOST0_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for spi_host1 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SPI_HOST1_BASE_ADDR = 32'h40070000;

  /**
   * Peripheral size in bytes for spi_host1 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SPI_HOST1_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for i2c0 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_I2C0_BASE_ADDR = 32'h40080000;

  /**
   * Peripheral size in bytes for i2c0 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_I2C0_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for i2c1 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_I2C1_BASE_ADDR = 32'h40090000;

  /**
   * Peripheral size in bytes for i2c1 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_I2C1_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for i2c2 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_I2C2_BASE_ADDR = 32'h400A0000;

  /**
   * Peripheral size in bytes for i2c2 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_I2C2_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for pattgen in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_PATTGEN_BASE_ADDR = 32'h400E0000;

  /**
   * Peripheral size in bytes for pattgen in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_PATTGEN_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for rv_timer in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_TIMER_BASE_ADDR = 32'h40100000;

  /**
   * Peripheral size in bytes for rv_timer in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_TIMER_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for usbdev in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_USBDEV_BASE_ADDR = 32'h40110000;

  /**
   * Peripheral size in bytes for usbdev in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_USBDEV_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for otp_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_OTP_CTRL_BASE_ADDR = 32'h40130000;

  /**
   * Peripheral size in bytes for otp_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_OTP_CTRL_SIZE_BYTES = 32'h4000;

  /**
   * Peripheral base address for lc_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_LC_CTRL_BASE_ADDR = 32'h40140000;

  /**
   * Peripheral size in bytes for lc_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_LC_CTRL_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for alert_handler in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR = 32'h40150000;

  /**
   * Peripheral size in bytes for alert_handler in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ALERT_HANDLER_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for pwrmgr_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_PWRMGR_AON_BASE_ADDR = 32'h40400000;

  /**
   * Peripheral size in bytes for pwrmgr_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_PWRMGR_AON_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for rstmgr_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RSTMGR_AON_BASE_ADDR = 32'h40410000;

  /**
   * Peripheral size in bytes for rstmgr_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RSTMGR_AON_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for clkmgr_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_CLKMGR_AON_BASE_ADDR = 32'h40420000;

  /**
   * Peripheral size in bytes for clkmgr_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_CLKMGR_AON_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for sysrst_ctrl_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SYSRST_CTRL_AON_BASE_ADDR = 32'h40430000;

  /**
   * Peripheral size in bytes for sysrst_ctrl_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SYSRST_CTRL_AON_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for adc_ctrl_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ADC_CTRL_AON_BASE_ADDR = 32'h40440000;

  /**
   * Peripheral size in bytes for adc_ctrl_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ADC_CTRL_AON_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for pwm_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_PWM_AON_BASE_ADDR = 32'h40450000;

  /**
   * Peripheral size in bytes for pwm_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_PWM_AON_SIZE_BYTES = 32'h1000;

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
  parameter int unsigned TOP_EARLGREY_AON_TIMER_AON_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for ast in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_AST_BASE_ADDR = 32'h40480000;

  /**
   * Peripheral size in bytes for ast in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_AST_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for sensor_ctrl_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SENSOR_CTRL_AON_BASE_ADDR = 32'h40490000;

  /**
   * Peripheral size in bytes for sensor_ctrl_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SENSOR_CTRL_AON_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for regs device on sram_ctrl_ret_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_BASE_ADDR = 32'h40500000;

  /**
   * Peripheral size in bytes for regs device on sram_ctrl_ret_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_SIZE_BYTES = 32'h1000;

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
  parameter int unsigned TOP_EARLGREY_FLASH_CTRL_CORE_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for prim device on flash_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_FLASH_CTRL_PRIM_BASE_ADDR = 32'h41008000;

  /**
   * Peripheral size in bytes for prim device on flash_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_FLASH_CTRL_PRIM_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for regs device on rv_dm in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_DM_REGS_BASE_ADDR = 32'h41200000;

  /**
   * Peripheral size in bytes for regs device on rv_dm in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_DM_REGS_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for rom device on rv_dm in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_DM_ROM_BASE_ADDR = 32'h10000;

  /**
   * Peripheral size in bytes for rom device on rv_dm in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_DM_ROM_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for rv_plic in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_PLIC_BASE_ADDR = 32'h41010000;

  /**
   * Peripheral size in bytes for rv_plic in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_PLIC_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for aes in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_AES_BASE_ADDR = 32'h41100000;

  /**
   * Peripheral size in bytes for aes in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_AES_SIZE_BYTES = 32'h1000;

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
   * Peripheral base address for keymgr in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_KEYMGR_BASE_ADDR = 32'h41130000;

  /**
   * Peripheral size in bytes for keymgr in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_KEYMGR_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for csrng in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_CSRNG_BASE_ADDR = 32'h41150000;

  /**
   * Peripheral size in bytes for csrng in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_CSRNG_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for entropy_src in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR = 32'h41160000;

  /**
   * Peripheral size in bytes for entropy_src in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ENTROPY_SRC_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for edn0 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_EDN0_BASE_ADDR = 32'h41170000;

  /**
   * Peripheral size in bytes for edn0 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_EDN0_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for edn1 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_EDN1_BASE_ADDR = 32'h41180000;

  /**
   * Peripheral size in bytes for edn1 in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_EDN1_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for regs device on sram_ctrl_main in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR = 32'h411C0000;

  /**
   * Peripheral size in bytes for regs device on sram_ctrl_main in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for ram device on sram_ctrl_main in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_BASE_ADDR = 32'h10000000;

  /**
   * Peripheral size in bytes for ram device on sram_ctrl_main in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_SIZE_BYTES = 32'h20000;

  /**
   * Peripheral base address for otbn in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_OTBN_BASE_ADDR = 32'h411D0000;

  /**
   * Peripheral size in bytes for otbn in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_OTBN_SIZE_BYTES = 32'h10000;

  /**
   * Peripheral base address for regs device on rom_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ROM_CTRL_REGS_BASE_ADDR = 32'h411E0000;

  /**
   * Peripheral size in bytes for regs device on rom_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ROM_CTRL_REGS_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for rom device on rom_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ROM_CTRL_ROM_BASE_ADDR = 32'h8000;

  /**
   * Peripheral size in bytes for rom device on rom_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ROM_CTRL_ROM_SIZE_BYTES = 32'h4000;

  /**
   * Peripheral base address for rv_core_ibex_peri in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_CORE_IBEX_PERI_BASE_ADDR = 32'h411F0000;

  /**
   * Peripheral size in bytes for rv_core_ibex_peri in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_CORE_IBEX_PERI_SIZE_BYTES = 32'h1000;

  /**
   * Memory base address for eflash in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_EFLASH_BASE_ADDR = 32'h20000000;

  /**
   * Memory size for eflash in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_EFLASH_SIZE_BYTES = 32'h100000;

  /**
   * Memory base address for ram_ret_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RAM_RET_AON_BASE_ADDR = 32'h40600000;

  /**
   * Memory size for ram_ret_aon in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RAM_RET_AON_SIZE_BYTES = 32'h1000;

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
  parameter int unsigned TOP_EARLGREY_ROM_SIZE_BYTES = 32'h4000;


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
    MioInFlashCtrlTck = 46,
    MioInFlashCtrlTms = 47,
    MioInFlashCtrlTdi = 48,
    MioInSysrstCtrlAonAcPresent = 49,
    MioInSysrstCtrlAonEcRstInL = 50,
    MioInSysrstCtrlAonKey0In = 51,
    MioInSysrstCtrlAonKey1In = 52,
    MioInSysrstCtrlAonKey2In = 53,
    MioInSysrstCtrlAonPwrbIn = 54,
    MioInSysrstCtrlAonLidOpen = 55,
    MioInCount = 56
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
    MioOutSysrstCtrlAonBatDisable = 68,
    MioOutSysrstCtrlAonKey0Out = 69,
    MioOutSysrstCtrlAonKey1Out = 70,
    MioOutSysrstCtrlAonKey2Out = 71,
    MioOutSysrstCtrlAonZ3Wakeup = 72,
    MioOutCount = 73
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
    DioUsbdevD = 8,
    DioUsbdevDp = 9,
    DioUsbdevDn = 10,
    DioSpiDeviceSck = 11,
    DioSpiDeviceCsb = 12,
    DioUsbdevSense = 13,
    DioSpiHost0Sck = 14,
    DioSpiHost0Csb = 15,
    DioUsbdevSe0 = 16,
    DioUsbdevDpPullup = 17,
    DioUsbdevDnPullup = 18,
    DioUsbdevTxModeSe = 19,
    DioUsbdevSuspend = 20,
    DioUsbdevRxEnable = 21,
    DioSysrstCtrlAonEcRstOutL = 22,
    DioSysrstCtrlAonPwrbOut = 23,
    DioCount = 24
  } dio_e;

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

  // TODO: Enumeration for PLIC Interrupt source peripheral.
  // TODO: Enumeration for PLIC Interrupt Ids.

endpackage
