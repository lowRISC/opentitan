// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_TOP_EARLGREY_SW_AUTOGEN_TOP_EARLGREY_H_
#define OPENTITAN_HW_TOP_EARLGREY_SW_AUTOGEN_TOP_EARLGREY_H_

/**
 * @file
 * @brief Top-specific Definitions
 *
 * This file contains preprocessor and type definitions for use within the
 * device C/C++ codebase.
 *
 * These definitions are for information that depends on the top-specific chip
 * configuration, which includes:
 * - Device Memory Information (for Peripherals and Memory)
 * - PLIC Interrupt ID Names and Source Mappings
 * - Alert ID Names and Source Mappings
 * - Pinmux Pin/Select Names
 * - Power Manager Wakeups
 */

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Peripheral base address for uart in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_UART_BASE_ADDR 0x40000000u

/**
 * Peripheral size for uart in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_UART_BASE_ADDR and
 * `TOP_EARLGREY_UART_BASE_ADDR + TOP_EARLGREY_UART_SIZE_BYTES`.
 */
#define TOP_EARLGREY_UART_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for gpio in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_GPIO_BASE_ADDR 0x40040000u

/**
 * Peripheral size for gpio in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_GPIO_BASE_ADDR and
 * `TOP_EARLGREY_GPIO_BASE_ADDR + TOP_EARLGREY_GPIO_SIZE_BYTES`.
 */
#define TOP_EARLGREY_GPIO_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for spi_device in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_SPI_DEVICE_BASE_ADDR 0x40050000u

/**
 * Peripheral size for spi_device in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_SPI_DEVICE_BASE_ADDR and
 * `TOP_EARLGREY_SPI_DEVICE_BASE_ADDR + TOP_EARLGREY_SPI_DEVICE_SIZE_BYTES`.
 */
#define TOP_EARLGREY_SPI_DEVICE_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for rv_timer in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_RV_TIMER_BASE_ADDR 0x40100000u

/**
 * Peripheral size for rv_timer in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_RV_TIMER_BASE_ADDR and
 * `TOP_EARLGREY_RV_TIMER_BASE_ADDR + TOP_EARLGREY_RV_TIMER_SIZE_BYTES`.
 */
#define TOP_EARLGREY_RV_TIMER_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for sensor_ctrl in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_SENSOR_CTRL_BASE_ADDR 0x40110000u

/**
 * Peripheral size for sensor_ctrl in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_SENSOR_CTRL_BASE_ADDR and
 * `TOP_EARLGREY_SENSOR_CTRL_BASE_ADDR + TOP_EARLGREY_SENSOR_CTRL_SIZE_BYTES`.
 */
#define TOP_EARLGREY_SENSOR_CTRL_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for otp_ctrl in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_OTP_CTRL_BASE_ADDR 0x40130000u

/**
 * Peripheral size for otp_ctrl in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_OTP_CTRL_BASE_ADDR and
 * `TOP_EARLGREY_OTP_CTRL_BASE_ADDR + TOP_EARLGREY_OTP_CTRL_SIZE_BYTES`.
 */
#define TOP_EARLGREY_OTP_CTRL_SIZE_BYTES 0x4000u

/**
 * Peripheral base address for lc_ctrl in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_LC_CTRL_BASE_ADDR 0x40140000u

/**
 * Peripheral size for lc_ctrl in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_LC_CTRL_BASE_ADDR and
 * `TOP_EARLGREY_LC_CTRL_BASE_ADDR + TOP_EARLGREY_LC_CTRL_SIZE_BYTES`.
 */
#define TOP_EARLGREY_LC_CTRL_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for alert_handler in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR 0x40150000u

/**
 * Peripheral size for alert_handler in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR and
 * `TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR + TOP_EARLGREY_ALERT_HANDLER_SIZE_BYTES`.
 */
#define TOP_EARLGREY_ALERT_HANDLER_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for nmi_gen in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_NMI_GEN_BASE_ADDR 0x40160000u

/**
 * Peripheral size for nmi_gen in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_NMI_GEN_BASE_ADDR and
 * `TOP_EARLGREY_NMI_GEN_BASE_ADDR + TOP_EARLGREY_NMI_GEN_SIZE_BYTES`.
 */
#define TOP_EARLGREY_NMI_GEN_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for pwrmgr in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_PWRMGR_BASE_ADDR 0x40400000u

/**
 * Peripheral size for pwrmgr in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_PWRMGR_BASE_ADDR and
 * `TOP_EARLGREY_PWRMGR_BASE_ADDR + TOP_EARLGREY_PWRMGR_SIZE_BYTES`.
 */
#define TOP_EARLGREY_PWRMGR_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for rstmgr in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_RSTMGR_BASE_ADDR 0x40410000u

/**
 * Peripheral size for rstmgr in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_RSTMGR_BASE_ADDR and
 * `TOP_EARLGREY_RSTMGR_BASE_ADDR + TOP_EARLGREY_RSTMGR_SIZE_BYTES`.
 */
#define TOP_EARLGREY_RSTMGR_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for clkmgr in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_CLKMGR_BASE_ADDR 0x40420000u

/**
 * Peripheral size for clkmgr in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_CLKMGR_BASE_ADDR and
 * `TOP_EARLGREY_CLKMGR_BASE_ADDR + TOP_EARLGREY_CLKMGR_SIZE_BYTES`.
 */
#define TOP_EARLGREY_CLKMGR_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for pinmux in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_PINMUX_BASE_ADDR 0x40460000u

/**
 * Peripheral size for pinmux in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_PINMUX_BASE_ADDR and
 * `TOP_EARLGREY_PINMUX_BASE_ADDR + TOP_EARLGREY_PINMUX_SIZE_BYTES`.
 */
#define TOP_EARLGREY_PINMUX_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for padctrl in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_PADCTRL_BASE_ADDR 0x40470000u

/**
 * Peripheral size for padctrl in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_PADCTRL_BASE_ADDR and
 * `TOP_EARLGREY_PADCTRL_BASE_ADDR + TOP_EARLGREY_PADCTRL_SIZE_BYTES`.
 */
#define TOP_EARLGREY_PADCTRL_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for usbdev in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_USBDEV_BASE_ADDR 0x40500000u

/**
 * Peripheral size for usbdev in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_USBDEV_BASE_ADDR and
 * `TOP_EARLGREY_USBDEV_BASE_ADDR + TOP_EARLGREY_USBDEV_SIZE_BYTES`.
 */
#define TOP_EARLGREY_USBDEV_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for sram_ctrl_ret in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_SRAM_CTRL_RET_BASE_ADDR 0x40510000u

/**
 * Peripheral size for sram_ctrl_ret in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_SRAM_CTRL_RET_BASE_ADDR and
 * `TOP_EARLGREY_SRAM_CTRL_RET_BASE_ADDR + TOP_EARLGREY_SRAM_CTRL_RET_SIZE_BYTES`.
 */
#define TOP_EARLGREY_SRAM_CTRL_RET_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for flash_ctrl in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_FLASH_CTRL_BASE_ADDR 0x41000000u

/**
 * Peripheral size for flash_ctrl in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_FLASH_CTRL_BASE_ADDR and
 * `TOP_EARLGREY_FLASH_CTRL_BASE_ADDR + TOP_EARLGREY_FLASH_CTRL_SIZE_BYTES`.
 */
#define TOP_EARLGREY_FLASH_CTRL_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for rv_plic in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_RV_PLIC_BASE_ADDR 0x41010000u

/**
 * Peripheral size for rv_plic in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_RV_PLIC_BASE_ADDR and
 * `TOP_EARLGREY_RV_PLIC_BASE_ADDR + TOP_EARLGREY_RV_PLIC_SIZE_BYTES`.
 */
#define TOP_EARLGREY_RV_PLIC_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for aes in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_AES_BASE_ADDR 0x41100000u

/**
 * Peripheral size for aes in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_AES_BASE_ADDR and
 * `TOP_EARLGREY_AES_BASE_ADDR + TOP_EARLGREY_AES_SIZE_BYTES`.
 */
#define TOP_EARLGREY_AES_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for hmac in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_HMAC_BASE_ADDR 0x41110000u

/**
 * Peripheral size for hmac in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_HMAC_BASE_ADDR and
 * `TOP_EARLGREY_HMAC_BASE_ADDR + TOP_EARLGREY_HMAC_SIZE_BYTES`.
 */
#define TOP_EARLGREY_HMAC_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for kmac in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_KMAC_BASE_ADDR 0x41120000u

/**
 * Peripheral size for kmac in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_KMAC_BASE_ADDR and
 * `TOP_EARLGREY_KMAC_BASE_ADDR + TOP_EARLGREY_KMAC_SIZE_BYTES`.
 */
#define TOP_EARLGREY_KMAC_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for keymgr in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_KEYMGR_BASE_ADDR 0x41130000u

/**
 * Peripheral size for keymgr in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_KEYMGR_BASE_ADDR and
 * `TOP_EARLGREY_KEYMGR_BASE_ADDR + TOP_EARLGREY_KEYMGR_SIZE_BYTES`.
 */
#define TOP_EARLGREY_KEYMGR_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for csrng in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_CSRNG_BASE_ADDR 0x41150000u

/**
 * Peripheral size for csrng in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_CSRNG_BASE_ADDR and
 * `TOP_EARLGREY_CSRNG_BASE_ADDR + TOP_EARLGREY_CSRNG_SIZE_BYTES`.
 */
#define TOP_EARLGREY_CSRNG_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for entropy_src in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR 0x41160000u

/**
 * Peripheral size for entropy_src in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR and
 * `TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR + TOP_EARLGREY_ENTROPY_SRC_SIZE_BYTES`.
 */
#define TOP_EARLGREY_ENTROPY_SRC_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for edn0 in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_EDN0_BASE_ADDR 0x41170000u

/**
 * Peripheral size for edn0 in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_EDN0_BASE_ADDR and
 * `TOP_EARLGREY_EDN0_BASE_ADDR + TOP_EARLGREY_EDN0_SIZE_BYTES`.
 */
#define TOP_EARLGREY_EDN0_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for edn1 in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_EDN1_BASE_ADDR 0x41180000u

/**
 * Peripheral size for edn1 in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_EDN1_BASE_ADDR and
 * `TOP_EARLGREY_EDN1_BASE_ADDR + TOP_EARLGREY_EDN1_SIZE_BYTES`.
 */
#define TOP_EARLGREY_EDN1_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for sram_ctrl_main in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_SRAM_CTRL_MAIN_BASE_ADDR 0x411C0000u

/**
 * Peripheral size for sram_ctrl_main in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_SRAM_CTRL_MAIN_BASE_ADDR and
 * `TOP_EARLGREY_SRAM_CTRL_MAIN_BASE_ADDR + TOP_EARLGREY_SRAM_CTRL_MAIN_SIZE_BYTES`.
 */
#define TOP_EARLGREY_SRAM_CTRL_MAIN_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for otbn in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_OTBN_BASE_ADDR 0x411D0000u

/**
 * Peripheral size for otbn in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_OTBN_BASE_ADDR and
 * `TOP_EARLGREY_OTBN_BASE_ADDR + TOP_EARLGREY_OTBN_SIZE_BYTES`.
 */
#define TOP_EARLGREY_OTBN_SIZE_BYTES 0x10000u


/**
 * Memory base address for rom in top earlgrey.
 */
#define TOP_EARLGREY_ROM_BASE_ADDR 0x00008000u

/**
 * Memory size for rom in top earlgrey.
 */
#define TOP_EARLGREY_ROM_SIZE_BYTES 0x4000u

/**
 * Memory base address for ram_main in top earlgrey.
 */
#define TOP_EARLGREY_RAM_MAIN_BASE_ADDR 0x10000000u

/**
 * Memory size for ram_main in top earlgrey.
 */
#define TOP_EARLGREY_RAM_MAIN_SIZE_BYTES 0x10000u

/**
 * Memory base address for ram_ret in top earlgrey.
 */
#define TOP_EARLGREY_RAM_RET_BASE_ADDR 0x18000000u

/**
 * Memory size for ram_ret in top earlgrey.
 */
#define TOP_EARLGREY_RAM_RET_SIZE_BYTES 0x1000u

/**
 * Memory base address for eflash in top earlgrey.
 */
#define TOP_EARLGREY_EFLASH_BASE_ADDR 0x20000000u

/**
 * Memory size for eflash in top earlgrey.
 */
#define TOP_EARLGREY_EFLASH_SIZE_BYTES 0x80000u


/**
 * PLIC Interrupt Source Peripheral.
 *
 * Enumeration used to determine which peripheral asserted the corresponding
 * interrupt.
 */
typedef enum top_earlgrey_plic_peripheral {
  kTopEarlgreyPlicPeripheralUnknown = 0, /**< Unknown Peripheral */
  kTopEarlgreyPlicPeripheralGpio = 1, /**< gpio */
  kTopEarlgreyPlicPeripheralUart = 2, /**< uart */
  kTopEarlgreyPlicPeripheralSpiDevice = 3, /**< spi_device */
  kTopEarlgreyPlicPeripheralFlashCtrl = 4, /**< flash_ctrl */
  kTopEarlgreyPlicPeripheralHmac = 5, /**< hmac */
  kTopEarlgreyPlicPeripheralAlertHandler = 6, /**< alert_handler */
  kTopEarlgreyPlicPeripheralNmiGen = 7, /**< nmi_gen */
  kTopEarlgreyPlicPeripheralUsbdev = 8, /**< usbdev */
  kTopEarlgreyPlicPeripheralPwrmgr = 9, /**< pwrmgr */
  kTopEarlgreyPlicPeripheralOtbn = 10, /**< otbn */
  kTopEarlgreyPlicPeripheralKeymgr = 11, /**< keymgr */
  kTopEarlgreyPlicPeripheralKmac = 12, /**< kmac */
  kTopEarlgreyPlicPeripheralOtpCtrl = 13, /**< otp_ctrl */
  kTopEarlgreyPlicPeripheralCsrng = 14, /**< csrng */
  kTopEarlgreyPlicPeripheralEdn0 = 15, /**< edn0 */
  kTopEarlgreyPlicPeripheralEdn1 = 16, /**< edn1 */
  kTopEarlgreyPlicPeripheralEntropySrc = 17, /**< entropy_src */
  kTopEarlgreyPlicPeripheralLast = 17, /**< \internal Final PLIC peripheral */
} top_earlgrey_plic_peripheral_t;

/**
 * PLIC Interrupt Source.
 *
 * Enumeration of all PLIC interrupt sources. The interrupt sources belonging to
 * the same peripheral are guaranteed to be consecutive.
 */
typedef enum top_earlgrey_plic_irq_id {
  kTopEarlgreyPlicIrqIdNone = 0, /**< No Interrupt */
  kTopEarlgreyPlicIrqIdGpioGpio0 = 1, /**< gpio_gpio 0 */
  kTopEarlgreyPlicIrqIdGpioGpio1 = 2, /**< gpio_gpio 1 */
  kTopEarlgreyPlicIrqIdGpioGpio2 = 3, /**< gpio_gpio 2 */
  kTopEarlgreyPlicIrqIdGpioGpio3 = 4, /**< gpio_gpio 3 */
  kTopEarlgreyPlicIrqIdGpioGpio4 = 5, /**< gpio_gpio 4 */
  kTopEarlgreyPlicIrqIdGpioGpio5 = 6, /**< gpio_gpio 5 */
  kTopEarlgreyPlicIrqIdGpioGpio6 = 7, /**< gpio_gpio 6 */
  kTopEarlgreyPlicIrqIdGpioGpio7 = 8, /**< gpio_gpio 7 */
  kTopEarlgreyPlicIrqIdGpioGpio8 = 9, /**< gpio_gpio 8 */
  kTopEarlgreyPlicIrqIdGpioGpio9 = 10, /**< gpio_gpio 9 */
  kTopEarlgreyPlicIrqIdGpioGpio10 = 11, /**< gpio_gpio 10 */
  kTopEarlgreyPlicIrqIdGpioGpio11 = 12, /**< gpio_gpio 11 */
  kTopEarlgreyPlicIrqIdGpioGpio12 = 13, /**< gpio_gpio 12 */
  kTopEarlgreyPlicIrqIdGpioGpio13 = 14, /**< gpio_gpio 13 */
  kTopEarlgreyPlicIrqIdGpioGpio14 = 15, /**< gpio_gpio 14 */
  kTopEarlgreyPlicIrqIdGpioGpio15 = 16, /**< gpio_gpio 15 */
  kTopEarlgreyPlicIrqIdGpioGpio16 = 17, /**< gpio_gpio 16 */
  kTopEarlgreyPlicIrqIdGpioGpio17 = 18, /**< gpio_gpio 17 */
  kTopEarlgreyPlicIrqIdGpioGpio18 = 19, /**< gpio_gpio 18 */
  kTopEarlgreyPlicIrqIdGpioGpio19 = 20, /**< gpio_gpio 19 */
  kTopEarlgreyPlicIrqIdGpioGpio20 = 21, /**< gpio_gpio 20 */
  kTopEarlgreyPlicIrqIdGpioGpio21 = 22, /**< gpio_gpio 21 */
  kTopEarlgreyPlicIrqIdGpioGpio22 = 23, /**< gpio_gpio 22 */
  kTopEarlgreyPlicIrqIdGpioGpio23 = 24, /**< gpio_gpio 23 */
  kTopEarlgreyPlicIrqIdGpioGpio24 = 25, /**< gpio_gpio 24 */
  kTopEarlgreyPlicIrqIdGpioGpio25 = 26, /**< gpio_gpio 25 */
  kTopEarlgreyPlicIrqIdGpioGpio26 = 27, /**< gpio_gpio 26 */
  kTopEarlgreyPlicIrqIdGpioGpio27 = 28, /**< gpio_gpio 27 */
  kTopEarlgreyPlicIrqIdGpioGpio28 = 29, /**< gpio_gpio 28 */
  kTopEarlgreyPlicIrqIdGpioGpio29 = 30, /**< gpio_gpio 29 */
  kTopEarlgreyPlicIrqIdGpioGpio30 = 31, /**< gpio_gpio 30 */
  kTopEarlgreyPlicIrqIdGpioGpio31 = 32, /**< gpio_gpio 31 */
  kTopEarlgreyPlicIrqIdUartTxWatermark = 33, /**< uart_tx_watermark */
  kTopEarlgreyPlicIrqIdUartRxWatermark = 34, /**< uart_rx_watermark */
  kTopEarlgreyPlicIrqIdUartTxEmpty = 35, /**< uart_tx_empty */
  kTopEarlgreyPlicIrqIdUartRxOverflow = 36, /**< uart_rx_overflow */
  kTopEarlgreyPlicIrqIdUartRxFrameErr = 37, /**< uart_rx_frame_err */
  kTopEarlgreyPlicIrqIdUartRxBreakErr = 38, /**< uart_rx_break_err */
  kTopEarlgreyPlicIrqIdUartRxTimeout = 39, /**< uart_rx_timeout */
  kTopEarlgreyPlicIrqIdUartRxParityErr = 40, /**< uart_rx_parity_err */
  kTopEarlgreyPlicIrqIdSpiDeviceRxf = 41, /**< spi_device_rxf */
  kTopEarlgreyPlicIrqIdSpiDeviceRxlvl = 42, /**< spi_device_rxlvl */
  kTopEarlgreyPlicIrqIdSpiDeviceTxlvl = 43, /**< spi_device_txlvl */
  kTopEarlgreyPlicIrqIdSpiDeviceRxerr = 44, /**< spi_device_rxerr */
  kTopEarlgreyPlicIrqIdSpiDeviceRxoverflow = 45, /**< spi_device_rxoverflow */
  kTopEarlgreyPlicIrqIdSpiDeviceTxunderflow = 46, /**< spi_device_txunderflow */
  kTopEarlgreyPlicIrqIdFlashCtrlProgEmpty = 47, /**< flash_ctrl_prog_empty */
  kTopEarlgreyPlicIrqIdFlashCtrlProgLvl = 48, /**< flash_ctrl_prog_lvl */
  kTopEarlgreyPlicIrqIdFlashCtrlRdFull = 49, /**< flash_ctrl_rd_full */
  kTopEarlgreyPlicIrqIdFlashCtrlRdLvl = 50, /**< flash_ctrl_rd_lvl */
  kTopEarlgreyPlicIrqIdFlashCtrlOpDone = 51, /**< flash_ctrl_op_done */
  kTopEarlgreyPlicIrqIdFlashCtrlOpError = 52, /**< flash_ctrl_op_error */
  kTopEarlgreyPlicIrqIdHmacHmacDone = 53, /**< hmac_hmac_done */
  kTopEarlgreyPlicIrqIdHmacFifoEmpty = 54, /**< hmac_fifo_empty */
  kTopEarlgreyPlicIrqIdHmacHmacErr = 55, /**< hmac_hmac_err */
  kTopEarlgreyPlicIrqIdAlertHandlerClassa = 56, /**< alert_handler_classa */
  kTopEarlgreyPlicIrqIdAlertHandlerClassb = 57, /**< alert_handler_classb */
  kTopEarlgreyPlicIrqIdAlertHandlerClassc = 58, /**< alert_handler_classc */
  kTopEarlgreyPlicIrqIdAlertHandlerClassd = 59, /**< alert_handler_classd */
  kTopEarlgreyPlicIrqIdNmiGenEsc0 = 60, /**< nmi_gen_esc0 */
  kTopEarlgreyPlicIrqIdNmiGenEsc1 = 61, /**< nmi_gen_esc1 */
  kTopEarlgreyPlicIrqIdNmiGenEsc2 = 62, /**< nmi_gen_esc2 */
  kTopEarlgreyPlicIrqIdUsbdevPktReceived = 63, /**< usbdev_pkt_received */
  kTopEarlgreyPlicIrqIdUsbdevPktSent = 64, /**< usbdev_pkt_sent */
  kTopEarlgreyPlicIrqIdUsbdevDisconnected = 65, /**< usbdev_disconnected */
  kTopEarlgreyPlicIrqIdUsbdevHostLost = 66, /**< usbdev_host_lost */
  kTopEarlgreyPlicIrqIdUsbdevLinkReset = 67, /**< usbdev_link_reset */
  kTopEarlgreyPlicIrqIdUsbdevLinkSuspend = 68, /**< usbdev_link_suspend */
  kTopEarlgreyPlicIrqIdUsbdevLinkResume = 69, /**< usbdev_link_resume */
  kTopEarlgreyPlicIrqIdUsbdevAvEmpty = 70, /**< usbdev_av_empty */
  kTopEarlgreyPlicIrqIdUsbdevRxFull = 71, /**< usbdev_rx_full */
  kTopEarlgreyPlicIrqIdUsbdevAvOverflow = 72, /**< usbdev_av_overflow */
  kTopEarlgreyPlicIrqIdUsbdevLinkInErr = 73, /**< usbdev_link_in_err */
  kTopEarlgreyPlicIrqIdUsbdevRxCrcErr = 74, /**< usbdev_rx_crc_err */
  kTopEarlgreyPlicIrqIdUsbdevRxPidErr = 75, /**< usbdev_rx_pid_err */
  kTopEarlgreyPlicIrqIdUsbdevRxBitstuffErr = 76, /**< usbdev_rx_bitstuff_err */
  kTopEarlgreyPlicIrqIdUsbdevFrame = 77, /**< usbdev_frame */
  kTopEarlgreyPlicIrqIdUsbdevConnected = 78, /**< usbdev_connected */
  kTopEarlgreyPlicIrqIdUsbdevLinkOutErr = 79, /**< usbdev_link_out_err */
  kTopEarlgreyPlicIrqIdPwrmgrWakeup = 80, /**< pwrmgr_wakeup */
  kTopEarlgreyPlicIrqIdOtbnDone = 81, /**< otbn_done */
  kTopEarlgreyPlicIrqIdKeymgrOpDone = 82, /**< keymgr_op_done */
  kTopEarlgreyPlicIrqIdKmacKmacDone = 83, /**< kmac_kmac_done */
  kTopEarlgreyPlicIrqIdKmacFifoEmpty = 84, /**< kmac_fifo_empty */
  kTopEarlgreyPlicIrqIdKmacKmacErr = 85, /**< kmac_kmac_err */
  kTopEarlgreyPlicIrqIdOtpCtrlOtpOperationDone = 86, /**< otp_ctrl_otp_operation_done */
  kTopEarlgreyPlicIrqIdOtpCtrlOtpError = 87, /**< otp_ctrl_otp_error */
  kTopEarlgreyPlicIrqIdCsrngCsCmdReqDone = 88, /**< csrng_cs_cmd_req_done */
  kTopEarlgreyPlicIrqIdCsrngCsEntropyReq = 89, /**< csrng_cs_entropy_req */
  kTopEarlgreyPlicIrqIdCsrngCsHwInstExc = 90, /**< csrng_cs_hw_inst_exc */
  kTopEarlgreyPlicIrqIdCsrngCsFifoErr = 91, /**< csrng_cs_fifo_err */
  kTopEarlgreyPlicIrqIdEdn0EdnCmdReqDone = 92, /**< edn0_edn_cmd_req_done */
  kTopEarlgreyPlicIrqIdEdn0EdnFifoErr = 93, /**< edn0_edn_fifo_err */
  kTopEarlgreyPlicIrqIdEdn1EdnCmdReqDone = 94, /**< edn1_edn_cmd_req_done */
  kTopEarlgreyPlicIrqIdEdn1EdnFifoErr = 95, /**< edn1_edn_fifo_err */
  kTopEarlgreyPlicIrqIdEntropySrcEsEntropyValid = 96, /**< entropy_src_es_entropy_valid */
  kTopEarlgreyPlicIrqIdEntropySrcEsHealthTestFailed = 97, /**< entropy_src_es_health_test_failed */
  kTopEarlgreyPlicIrqIdEntropySrcEsFifoErr = 98, /**< entropy_src_es_fifo_err */
  kTopEarlgreyPlicIrqIdLast = 98, /**< \internal The Last Valid Interrupt ID. */
} top_earlgrey_plic_irq_id_t;

/**
 * PLIC Interrupt Source to Peripheral Map
 *
 * This array is a mapping from `top_earlgrey_plic_irq_id_t` to
 * `top_earlgrey_plic_peripheral_t`.
 */
extern const top_earlgrey_plic_peripheral_t
    top_earlgrey_plic_interrupt_for_peripheral[99];

/**
 * PLIC Interrupt Target.
 *
 * Enumeration used to determine which set of IE, CC, threshold registers to
 * access for a given interrupt target.
 */
typedef enum top_earlgrey_plic_target {
  kTopEarlgreyPlicTargetIbex0 = 0, /**< Ibex Core 0 */
  kTopEarlgreyPlicTargetLast = 0, /**< \internal Final PLIC target */
} top_earlgrey_plic_target_t;

/**
 * Alert Handler Source Peripheral.
 *
 * Enumeration used to determine which peripheral asserted the corresponding
 * alert.
 */
typedef enum top_earlgrey_alert_peripheral {
  kTopEarlgreyAlertPeripheralAes = 0, /**< aes */
  kTopEarlgreyAlertPeripheralOtbn = 1, /**< otbn */
  kTopEarlgreyAlertPeripheralSensorCtrl = 2, /**< sensor_ctrl */
  kTopEarlgreyAlertPeripheralKeymgr = 3, /**< keymgr */
  kTopEarlgreyAlertPeripheralOtpCtrl = 4, /**< otp_ctrl */
  kTopEarlgreyAlertPeripheralLcCtrl = 5, /**< lc_ctrl */
  kTopEarlgreyAlertPeripheralEntropySrc = 6, /**< entropy_src */
  kTopEarlgreyAlertPeripheralSramCtrlMain = 7, /**< sram_ctrl_main */
  kTopEarlgreyAlertPeripheralSramCtrlRet = 8, /**< sram_ctrl_ret */
  kTopEarlgreyAlertPeripheralLast = 8, /**< \internal Final Alert peripheral */
} top_earlgrey_alert_peripheral_t;

/**
 * Alert Handler Alert Source.
 *
 * Enumeration of all Alert Handler Alert Sources. The alert sources belonging to
 * the same peripheral are guaranteed to be consecutive.
 */
typedef enum top_earlgrey_alert_id {
  kTopEarlgreyAlertIdAesRecovCtrlUpdateErr = 0, /**< aes_recov_ctrl_update_err */
  kTopEarlgreyAlertIdAesFatalFault = 1, /**< aes_fatal_fault */
  kTopEarlgreyAlertIdOtbnFatal = 2, /**< otbn_fatal */
  kTopEarlgreyAlertIdOtbnRecov = 3, /**< otbn_recov */
  kTopEarlgreyAlertIdSensorCtrlAs = 4, /**< sensor_ctrl_as */
  kTopEarlgreyAlertIdSensorCtrlCg = 5, /**< sensor_ctrl_cg */
  kTopEarlgreyAlertIdSensorCtrlGd = 6, /**< sensor_ctrl_gd */
  kTopEarlgreyAlertIdSensorCtrlTsHi = 7, /**< sensor_ctrl_ts_hi */
  kTopEarlgreyAlertIdSensorCtrlTsLo = 8, /**< sensor_ctrl_ts_lo */
  kTopEarlgreyAlertIdSensorCtrlLs = 9, /**< sensor_ctrl_ls */
  kTopEarlgreyAlertIdSensorCtrlOt = 10, /**< sensor_ctrl_ot */
  kTopEarlgreyAlertIdKeymgrFaultErr = 11, /**< keymgr_fault_err */
  kTopEarlgreyAlertIdKeymgrOperationErr = 12, /**< keymgr_operation_err */
  kTopEarlgreyAlertIdOtpCtrlFatalMacroError = 13, /**< otp_ctrl_fatal_macro_error */
  kTopEarlgreyAlertIdOtpCtrlFatalCheckError = 14, /**< otp_ctrl_fatal_check_error */
  kTopEarlgreyAlertIdLcCtrlFatalProgError = 15, /**< lc_ctrl_fatal_prog_error */
  kTopEarlgreyAlertIdLcCtrlFatalStateError = 16, /**< lc_ctrl_fatal_state_error */
  kTopEarlgreyAlertIdEntropySrcRecovAlertCountMet = 17, /**< entropy_src_recov_alert_count_met */
  kTopEarlgreyAlertIdSramCtrlMainFatalParityError = 18, /**< sram_ctrl_main_fatal_parity_error */
  kTopEarlgreyAlertIdSramCtrlRetFatalParityError = 19, /**< sram_ctrl_ret_fatal_parity_error */
  kTopEarlgreyAlertIdLast = 19, /**< \internal The Last Valid Alert ID. */
} top_earlgrey_alert_id_t;

/**
 * Alert Handler Alert Source to Peripheral Map
 *
 * This array is a mapping from `top_earlgrey_alert_id_t` to
 * `top_earlgrey_alert_peripheral_t`.
 */
extern const top_earlgrey_alert_peripheral_t
    top_earlgrey_alert_for_peripheral[20];

#define PINMUX_PERIPH_INSEL_IDX_OFFSET 2

// PERIPH_INSEL ranges from 0 to NUM_MIO + 2 -1}
//  0 and 1 are tied to value 0 and 1
#define NUM_MIO 32
#define NUM_DIO 15

#define PINMUX_PERIPH_OUTSEL_IDX_OFFSET 3

/**
 * Pinmux Peripheral Input.
 */
typedef enum top_earlgrey_pinmux_peripheral_in {
  kTopEarlgreyPinmuxPeripheralInGpioGpio0 = 0, /**< gpio_gpio 0 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio1 = 1, /**< gpio_gpio 1 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio2 = 2, /**< gpio_gpio 2 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio3 = 3, /**< gpio_gpio 3 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio4 = 4, /**< gpio_gpio 4 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio5 = 5, /**< gpio_gpio 5 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio6 = 6, /**< gpio_gpio 6 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio7 = 7, /**< gpio_gpio 7 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio8 = 8, /**< gpio_gpio 8 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio9 = 9, /**< gpio_gpio 9 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio10 = 10, /**< gpio_gpio 10 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio11 = 11, /**< gpio_gpio 11 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio12 = 12, /**< gpio_gpio 12 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio13 = 13, /**< gpio_gpio 13 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio14 = 14, /**< gpio_gpio 14 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio15 = 15, /**< gpio_gpio 15 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio16 = 16, /**< gpio_gpio 16 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio17 = 17, /**< gpio_gpio 17 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio18 = 18, /**< gpio_gpio 18 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio19 = 19, /**< gpio_gpio 19 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio20 = 20, /**< gpio_gpio 20 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio21 = 21, /**< gpio_gpio 21 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio22 = 22, /**< gpio_gpio 22 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio23 = 23, /**< gpio_gpio 23 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio24 = 24, /**< gpio_gpio 24 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio25 = 25, /**< gpio_gpio 25 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio26 = 26, /**< gpio_gpio 26 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio27 = 27, /**< gpio_gpio 27 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio28 = 28, /**< gpio_gpio 28 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio29 = 29, /**< gpio_gpio 29 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio30 = 30, /**< gpio_gpio 30 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio31 = 31, /**< gpio_gpio 31 */
  kTopEarlgreyPinmuxPeripheralInLast = 31, /**< \internal Last valid peripheral input */
} top_earlgrey_pinmux_peripheral_in_t;

/**
 * Pinmux MIO Input Selector.
 */
typedef enum top_earlgrey_pinmux_insel {
  kTopEarlgreyPinmuxInselConstantZero = 0, /**< Tie constantly to zero */
  kTopEarlgreyPinmuxInselConstantOne = 1, /**< Tie constantly to one */
  kTopEarlgreyPinmuxInselMio0 = 2, /**< MIO Pad 0 */
  kTopEarlgreyPinmuxInselMio1 = 3, /**< MIO Pad 1 */
  kTopEarlgreyPinmuxInselMio2 = 4, /**< MIO Pad 2 */
  kTopEarlgreyPinmuxInselMio3 = 5, /**< MIO Pad 3 */
  kTopEarlgreyPinmuxInselMio4 = 6, /**< MIO Pad 4 */
  kTopEarlgreyPinmuxInselMio5 = 7, /**< MIO Pad 5 */
  kTopEarlgreyPinmuxInselMio6 = 8, /**< MIO Pad 6 */
  kTopEarlgreyPinmuxInselMio7 = 9, /**< MIO Pad 7 */
  kTopEarlgreyPinmuxInselMio8 = 10, /**< MIO Pad 8 */
  kTopEarlgreyPinmuxInselMio9 = 11, /**< MIO Pad 9 */
  kTopEarlgreyPinmuxInselMio10 = 12, /**< MIO Pad 10 */
  kTopEarlgreyPinmuxInselMio11 = 13, /**< MIO Pad 11 */
  kTopEarlgreyPinmuxInselMio12 = 14, /**< MIO Pad 12 */
  kTopEarlgreyPinmuxInselMio13 = 15, /**< MIO Pad 13 */
  kTopEarlgreyPinmuxInselMio14 = 16, /**< MIO Pad 14 */
  kTopEarlgreyPinmuxInselMio15 = 17, /**< MIO Pad 15 */
  kTopEarlgreyPinmuxInselMio16 = 18, /**< MIO Pad 16 */
  kTopEarlgreyPinmuxInselMio17 = 19, /**< MIO Pad 17 */
  kTopEarlgreyPinmuxInselMio18 = 20, /**< MIO Pad 18 */
  kTopEarlgreyPinmuxInselMio19 = 21, /**< MIO Pad 19 */
  kTopEarlgreyPinmuxInselMio20 = 22, /**< MIO Pad 20 */
  kTopEarlgreyPinmuxInselMio21 = 23, /**< MIO Pad 21 */
  kTopEarlgreyPinmuxInselMio22 = 24, /**< MIO Pad 22 */
  kTopEarlgreyPinmuxInselMio23 = 25, /**< MIO Pad 23 */
  kTopEarlgreyPinmuxInselMio24 = 26, /**< MIO Pad 24 */
  kTopEarlgreyPinmuxInselMio25 = 27, /**< MIO Pad 25 */
  kTopEarlgreyPinmuxInselMio26 = 28, /**< MIO Pad 26 */
  kTopEarlgreyPinmuxInselMio27 = 29, /**< MIO Pad 27 */
  kTopEarlgreyPinmuxInselMio28 = 30, /**< MIO Pad 28 */
  kTopEarlgreyPinmuxInselMio29 = 31, /**< MIO Pad 29 */
  kTopEarlgreyPinmuxInselMio30 = 32, /**< MIO Pad 30 */
  kTopEarlgreyPinmuxInselMio31 = 33, /**< MIO Pad 31 */
  kTopEarlgreyPinmuxInselLast = 33, /**< \internal Last valid insel value */
} top_earlgrey_pinmux_insel_t;

/**
 * Pinmux MIO Output.
 */
typedef enum top_earlgrey_pinmux_mio_out {
  kTopEarlgreyPinmuxMioOut0 = 0, /**< MIO Pad 0 */
  kTopEarlgreyPinmuxMioOut1 = 1, /**< MIO Pad 1 */
  kTopEarlgreyPinmuxMioOut2 = 2, /**< MIO Pad 2 */
  kTopEarlgreyPinmuxMioOut3 = 3, /**< MIO Pad 3 */
  kTopEarlgreyPinmuxMioOut4 = 4, /**< MIO Pad 4 */
  kTopEarlgreyPinmuxMioOut5 = 5, /**< MIO Pad 5 */
  kTopEarlgreyPinmuxMioOut6 = 6, /**< MIO Pad 6 */
  kTopEarlgreyPinmuxMioOut7 = 7, /**< MIO Pad 7 */
  kTopEarlgreyPinmuxMioOut8 = 8, /**< MIO Pad 8 */
  kTopEarlgreyPinmuxMioOut9 = 9, /**< MIO Pad 9 */
  kTopEarlgreyPinmuxMioOut10 = 10, /**< MIO Pad 10 */
  kTopEarlgreyPinmuxMioOut11 = 11, /**< MIO Pad 11 */
  kTopEarlgreyPinmuxMioOut12 = 12, /**< MIO Pad 12 */
  kTopEarlgreyPinmuxMioOut13 = 13, /**< MIO Pad 13 */
  kTopEarlgreyPinmuxMioOut14 = 14, /**< MIO Pad 14 */
  kTopEarlgreyPinmuxMioOut15 = 15, /**< MIO Pad 15 */
  kTopEarlgreyPinmuxMioOut16 = 16, /**< MIO Pad 16 */
  kTopEarlgreyPinmuxMioOut17 = 17, /**< MIO Pad 17 */
  kTopEarlgreyPinmuxMioOut18 = 18, /**< MIO Pad 18 */
  kTopEarlgreyPinmuxMioOut19 = 19, /**< MIO Pad 19 */
  kTopEarlgreyPinmuxMioOut20 = 20, /**< MIO Pad 20 */
  kTopEarlgreyPinmuxMioOut21 = 21, /**< MIO Pad 21 */
  kTopEarlgreyPinmuxMioOut22 = 22, /**< MIO Pad 22 */
  kTopEarlgreyPinmuxMioOut23 = 23, /**< MIO Pad 23 */
  kTopEarlgreyPinmuxMioOut24 = 24, /**< MIO Pad 24 */
  kTopEarlgreyPinmuxMioOut25 = 25, /**< MIO Pad 25 */
  kTopEarlgreyPinmuxMioOut26 = 26, /**< MIO Pad 26 */
  kTopEarlgreyPinmuxMioOut27 = 27, /**< MIO Pad 27 */
  kTopEarlgreyPinmuxMioOut28 = 28, /**< MIO Pad 28 */
  kTopEarlgreyPinmuxMioOut29 = 29, /**< MIO Pad 29 */
  kTopEarlgreyPinmuxMioOut30 = 30, /**< MIO Pad 30 */
  kTopEarlgreyPinmuxMioOut31 = 31, /**< MIO Pad 31 */
  kTopEarlgreyPinmuxMioOutLast = 31, /**< \internal Last valid mio output */
} top_earlgrey_pinmux_mio_out_t;

/**
 * Pinmux Peripheral Output Selector.
 */
typedef enum top_earlgrey_pinmux_outsel {
  kTopEarlgreyPinmuxOutselConstantZero = 0, /**< Tie constantly to zero */
  kTopEarlgreyPinmuxOutselConstantOne = 1, /**< Tie constantly to one */
  kTopEarlgreyPinmuxOutselConstantHighZ = 2, /**< Tie constantly to high-Z */
  kTopEarlgreyPinmuxOutselGpioGpio0 = 3, /**< gpio_gpio 0 */
  kTopEarlgreyPinmuxOutselGpioGpio1 = 4, /**< gpio_gpio 1 */
  kTopEarlgreyPinmuxOutselGpioGpio2 = 5, /**< gpio_gpio 2 */
  kTopEarlgreyPinmuxOutselGpioGpio3 = 6, /**< gpio_gpio 3 */
  kTopEarlgreyPinmuxOutselGpioGpio4 = 7, /**< gpio_gpio 4 */
  kTopEarlgreyPinmuxOutselGpioGpio5 = 8, /**< gpio_gpio 5 */
  kTopEarlgreyPinmuxOutselGpioGpio6 = 9, /**< gpio_gpio 6 */
  kTopEarlgreyPinmuxOutselGpioGpio7 = 10, /**< gpio_gpio 7 */
  kTopEarlgreyPinmuxOutselGpioGpio8 = 11, /**< gpio_gpio 8 */
  kTopEarlgreyPinmuxOutselGpioGpio9 = 12, /**< gpio_gpio 9 */
  kTopEarlgreyPinmuxOutselGpioGpio10 = 13, /**< gpio_gpio 10 */
  kTopEarlgreyPinmuxOutselGpioGpio11 = 14, /**< gpio_gpio 11 */
  kTopEarlgreyPinmuxOutselGpioGpio12 = 15, /**< gpio_gpio 12 */
  kTopEarlgreyPinmuxOutselGpioGpio13 = 16, /**< gpio_gpio 13 */
  kTopEarlgreyPinmuxOutselGpioGpio14 = 17, /**< gpio_gpio 14 */
  kTopEarlgreyPinmuxOutselGpioGpio15 = 18, /**< gpio_gpio 15 */
  kTopEarlgreyPinmuxOutselGpioGpio16 = 19, /**< gpio_gpio 16 */
  kTopEarlgreyPinmuxOutselGpioGpio17 = 20, /**< gpio_gpio 17 */
  kTopEarlgreyPinmuxOutselGpioGpio18 = 21, /**< gpio_gpio 18 */
  kTopEarlgreyPinmuxOutselGpioGpio19 = 22, /**< gpio_gpio 19 */
  kTopEarlgreyPinmuxOutselGpioGpio20 = 23, /**< gpio_gpio 20 */
  kTopEarlgreyPinmuxOutselGpioGpio21 = 24, /**< gpio_gpio 21 */
  kTopEarlgreyPinmuxOutselGpioGpio22 = 25, /**< gpio_gpio 22 */
  kTopEarlgreyPinmuxOutselGpioGpio23 = 26, /**< gpio_gpio 23 */
  kTopEarlgreyPinmuxOutselGpioGpio24 = 27, /**< gpio_gpio 24 */
  kTopEarlgreyPinmuxOutselGpioGpio25 = 28, /**< gpio_gpio 25 */
  kTopEarlgreyPinmuxOutselGpioGpio26 = 29, /**< gpio_gpio 26 */
  kTopEarlgreyPinmuxOutselGpioGpio27 = 30, /**< gpio_gpio 27 */
  kTopEarlgreyPinmuxOutselGpioGpio28 = 31, /**< gpio_gpio 28 */
  kTopEarlgreyPinmuxOutselGpioGpio29 = 32, /**< gpio_gpio 29 */
  kTopEarlgreyPinmuxOutselGpioGpio30 = 33, /**< gpio_gpio 30 */
  kTopEarlgreyPinmuxOutselGpioGpio31 = 34, /**< gpio_gpio 31 */
  kTopEarlgreyPinmuxOutselLast = 34, /**< \internal Last valid outsel value */
} top_earlgrey_pinmux_outsel_t;

/**
 * Power Manager Wakeup Signals
 */
typedef enum top_earlgrey_power_manager_wake_ups {
  kTopEarlgreyPowerManagerWakeUpsPinmuxAonWkupReq = 0, /**<  */
  kTopEarlgreyPowerManagerWakeUpsLast = 0, /**< \internal Last valid pwrmgr wakeup signal */
} top_earlgrey_power_manager_wake_ups_t;

/**
 * Reset Manager Software Controlled Resets
 */
typedef enum top_earlgrey_reset_manager_sw_resets {
  kTopEarlgreyResetManagerSwResetsSpiDevice = 0, /**<  */
  kTopEarlgreyResetManagerSwResetsUsb = 1, /**<  */
  kTopEarlgreyResetManagerSwResetsLast = 1, /**< \internal Last valid rstmgr software reset request */
} top_earlgrey_reset_manager_sw_resets_t;

/**
 * Power Manager Reset Request Signals
 */
typedef enum top_earlgrey_power_manager_reset_requests {
  kTopEarlgreyPowerManagerResetRequestsNmiGenNmiRstReq = 0, /**<  */
  kTopEarlgreyPowerManagerResetRequestsLast = 0, /**< \internal Last valid pwrmgr reset_request signal */
} top_earlgrey_power_manager_reset_requests_t;

/**
 * Clock Manager Software-Controlled ("Gated") Clocks.
 *
 * The Software has full control over these clocks.
 */
typedef enum top_earlgrey_gateable_clocks {
  kTopEarlgreyGateableClocksIoDiv4Peri = 0, /**< Clock clk_io_div4_peri in group peri */
  kTopEarlgreyGateableClocksUsbPeri = 1, /**< Clock clk_usb_peri in group peri */
  kTopEarlgreyGateableClocksLast = 1, /**< \internal Last Valid Gateable Clock */
} top_earlgrey_gateable_clocks_t;

/**
 * Clock Manager Software-Hinted Clocks.
 *
 * The Software has partial control over these clocks. It can ask them to stop,
 * but the clock manager is in control of whether the clock actually is stopped.
 */
typedef enum top_earlgrey_hintable_clocks {
  kTopEarlgreyHintableClocksMainAes = 0, /**< Clock clk_main_aes in group trans */
  kTopEarlgreyHintableClocksMainHmac = 1, /**< Clock clk_main_hmac in group trans */
  kTopEarlgreyHintableClocksMainKmac = 2, /**< Clock clk_main_kmac in group trans */
  kTopEarlgreyHintableClocksMainOtbn = 3, /**< Clock clk_main_otbn in group trans */
  kTopEarlgreyHintableClocksLast = 3, /**< \internal Last Valid Hintable Clock */
} top_earlgrey_hintable_clocks_t;

// Header Extern Guard
#ifdef __cplusplus
}  // extern "C"
#endif

#endif  // OPENTITAN_HW_TOP_EARLGREY_SW_AUTOGEN_TOP_EARLGREY_H_
