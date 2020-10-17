// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package top_earlgrey_pkg;
  /**
   * Peripheral base address for uart in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_UART_BASE_ADDR = 32'h40000000;

  /**
   * Peripheral size in bytes for uart in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_UART_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for gpio in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_GPIO_BASE_ADDR = 32'h40010000;

  /**
   * Peripheral size in bytes for gpio in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_GPIO_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for spi_device in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SPI_DEVICE_BASE_ADDR = 32'h40020000;

  /**
   * Peripheral size in bytes for spi_device in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SPI_DEVICE_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for flash_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_FLASH_CTRL_BASE_ADDR = 32'h40030000;

  /**
   * Peripheral size in bytes for flash_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_FLASH_CTRL_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for rv_timer in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_TIMER_BASE_ADDR = 32'h40080000;

  /**
   * Peripheral size in bytes for rv_timer in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_TIMER_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for aes in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_AES_BASE_ADDR = 32'h40110000;

  /**
   * Peripheral size in bytes for aes in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_AES_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for hmac in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_HMAC_BASE_ADDR = 32'h40120000;

  /**
   * Peripheral size in bytes for hmac in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_HMAC_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for rv_plic in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_PLIC_BASE_ADDR = 32'h40090000;

  /**
   * Peripheral size in bytes for rv_plic in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RV_PLIC_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for pinmux in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_PINMUX_BASE_ADDR = 32'h40070000;

  /**
   * Peripheral size in bytes for pinmux in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_PINMUX_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for padctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_PADCTRL_BASE_ADDR = 32'h40160000;

  /**
   * Peripheral size in bytes for padctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_PADCTRL_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for alert_handler in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR = 32'h40130000;

  /**
   * Peripheral size in bytes for alert_handler in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ALERT_HANDLER_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for pwrmgr in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_PWRMGR_BASE_ADDR = 32'h400A0000;

  /**
   * Peripheral size in bytes for pwrmgr in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_PWRMGR_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for rstmgr in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RSTMGR_BASE_ADDR = 32'h400B0000;

  /**
   * Peripheral size in bytes for rstmgr in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RSTMGR_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for clkmgr in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_CLKMGR_BASE_ADDR = 32'h400C0000;

  /**
   * Peripheral size in bytes for clkmgr in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_CLKMGR_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for nmi_gen in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_NMI_GEN_BASE_ADDR = 32'h40140000;

  /**
   * Peripheral size in bytes for nmi_gen in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_NMI_GEN_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for usbdev in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_USBDEV_BASE_ADDR = 32'h40150000;

  /**
   * Peripheral size in bytes for usbdev in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_USBDEV_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for sensor_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SENSOR_CTRL_BASE_ADDR = 32'h40170000;

  /**
   * Peripheral size in bytes for sensor_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_SENSOR_CTRL_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for keymgr in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_KEYMGR_BASE_ADDR = 32'h401a0000;

  /**
   * Peripheral size in bytes for keymgr in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_KEYMGR_SIZE_BYTES = 32'h1000;

  /**
   * Peripheral base address for otp_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_OTP_CTRL_BASE_ADDR = 32'h401b0000;

  /**
   * Peripheral size in bytes for otp_ctrl in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_OTP_CTRL_SIZE_BYTES = 32'h4000;

  /**
   * Peripheral base address for otbn in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_OTBN_BASE_ADDR = 32'h50000000;

  /**
   * Peripheral size in bytes for otbn in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_OTBN_SIZE_BYTES = 32'h400000;

  /**
   * Memory base address for rom in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ROM_BASE_ADDR = 32'h00008000;

  /**
   * Memory size for rom in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_ROM_SIZE_BYTES = 32'h4000;

  /**
   * Memory base address for ram_main in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RAM_MAIN_BASE_ADDR = 32'h10000000;

  /**
   * Memory size for ram_main in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RAM_MAIN_SIZE_BYTES = 32'h10000;

  /**
   * Memory base address for ram_ret in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RAM_RET_BASE_ADDR = 32'h18000000;

  /**
   * Memory size for ram_ret in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_RAM_RET_SIZE_BYTES = 32'h1000;

  /**
   * Memory base address for eflash in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_EFLASH_BASE_ADDR = 32'h20000000;

  /**
   * Memory size for eflash in top earlgrey.
   */
  parameter int unsigned TOP_EARLGREY_EFLASH_SIZE_BYTES = 32'h80000;

  // Enumeration for DIO pins.
  typedef enum {
    TopEarlgreyDioPinUsbdevDn = 0,
    TopEarlgreyDioPinUsbdevDp = 1,
    TopEarlgreyDioPinUsbdevD = 2,
    TopEarlgreyDioPinUsbdevSuspend = 3,
    TopEarlgreyDioPinUsbdevTxModeSe = 4,
    TopEarlgreyDioPinUsbdevDnPullup = 5,
    TopEarlgreyDioPinUsbdevDpPullup = 6,
    TopEarlgreyDioPinUsbdevSe0 = 7,
    TopEarlgreyDioPinUsbdevSense = 8,
    TopEarlgreyDioPinUartTx = 9,
    TopEarlgreyDioPinUartRx = 10,
    TopEarlgreyDioPinSpiDeviceSdo = 11,
    TopEarlgreyDioPinSpiDeviceSdi = 12,
    TopEarlgreyDioPinSpiDeviceCsb = 13,
    TopEarlgreyDioPinSpiDeviceSck = 14,
    TopEarlgreyDioPinCount = 15
  } top_earlgrey_dio_pin_e;

  // TODO: Enumeration for PLIC Interrupt source peripheral.
  // TODO: Enumeration for PLIC Interrupt Ids.

endpackage
