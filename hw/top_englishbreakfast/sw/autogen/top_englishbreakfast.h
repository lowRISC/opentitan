// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
// util/topgen.py -t hw/top_englishbreakfast/data/top_englishbreakfast.hjson
// -o hw/top_englishbreakfast

#ifndef OPENTITAN_HW_TOP_ENGLISHBREAKFAST_SW_AUTOGEN_TOP_ENGLISHBREAKFAST_H_
#define OPENTITAN_HW_TOP_ENGLISHBREAKFAST_SW_AUTOGEN_TOP_ENGLISHBREAKFAST_H_

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
 * Peripheral base address for uart0 in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_UART0_BASE_ADDR 0x40000000u

/**
 * Peripheral size for uart0 in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_UART0_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_UART0_BASE_ADDR + TOP_ENGLISHBREAKFAST_UART0_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_UART0_SIZE_BYTES 0x40u

/**
 * Peripheral base address for uart1 in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_UART1_BASE_ADDR 0x40010000u

/**
 * Peripheral size for uart1 in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_UART1_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_UART1_BASE_ADDR + TOP_ENGLISHBREAKFAST_UART1_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_UART1_SIZE_BYTES 0x40u

/**
 * Peripheral base address for gpio in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_GPIO_BASE_ADDR 0x40040000u

/**
 * Peripheral size for gpio in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_GPIO_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_GPIO_BASE_ADDR + TOP_ENGLISHBREAKFAST_GPIO_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_GPIO_SIZE_BYTES 0x40u

/**
 * Peripheral base address for spi_device in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_SPI_DEVICE_BASE_ADDR 0x40050000u

/**
 * Peripheral size for spi_device in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_SPI_DEVICE_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_SPI_DEVICE_BASE_ADDR + TOP_ENGLISHBREAKFAST_SPI_DEVICE_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_SPI_DEVICE_SIZE_BYTES 0x2000u

/**
 * Peripheral base address for spi_host0 in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_SPI_HOST0_BASE_ADDR 0x40060000u

/**
 * Peripheral size for spi_host0 in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_SPI_HOST0_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_SPI_HOST0_BASE_ADDR + TOP_ENGLISHBREAKFAST_SPI_HOST0_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_SPI_HOST0_SIZE_BYTES 0x40u

/**
 * Peripheral base address for rv_timer in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_RV_TIMER_BASE_ADDR 0x40100000u

/**
 * Peripheral size for rv_timer in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_RV_TIMER_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_RV_TIMER_BASE_ADDR + TOP_ENGLISHBREAKFAST_RV_TIMER_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_RV_TIMER_SIZE_BYTES 0x200u

/**
 * Peripheral base address for usbdev in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_USBDEV_BASE_ADDR 0x40320000u

/**
 * Peripheral size for usbdev in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_USBDEV_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_USBDEV_BASE_ADDR + TOP_ENGLISHBREAKFAST_USBDEV_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_USBDEV_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for pwrmgr_aon in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_PWRMGR_AON_BASE_ADDR 0x40400000u

/**
 * Peripheral size for pwrmgr_aon in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_PWRMGR_AON_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_PWRMGR_AON_BASE_ADDR + TOP_ENGLISHBREAKFAST_PWRMGR_AON_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_PWRMGR_AON_SIZE_BYTES 0x80u

/**
 * Peripheral base address for rstmgr_aon in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_RSTMGR_AON_BASE_ADDR 0x40410000u

/**
 * Peripheral size for rstmgr_aon in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_RSTMGR_AON_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_RSTMGR_AON_BASE_ADDR + TOP_ENGLISHBREAKFAST_RSTMGR_AON_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_RSTMGR_AON_SIZE_BYTES 0x80u

/**
 * Peripheral base address for clkmgr_aon in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_CLKMGR_AON_BASE_ADDR 0x40420000u

/**
 * Peripheral size for clkmgr_aon in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_CLKMGR_AON_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_CLKMGR_AON_BASE_ADDR + TOP_ENGLISHBREAKFAST_CLKMGR_AON_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_CLKMGR_AON_SIZE_BYTES 0x80u

/**
 * Peripheral base address for pinmux_aon in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_PINMUX_AON_BASE_ADDR 0x40460000u

/**
 * Peripheral size for pinmux_aon in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_PINMUX_AON_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_PINMUX_AON_BASE_ADDR + TOP_ENGLISHBREAKFAST_PINMUX_AON_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_PINMUX_AON_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for aon_timer_aon in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_AON_TIMER_AON_BASE_ADDR 0x40470000u

/**
 * Peripheral size for aon_timer_aon in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_AON_TIMER_AON_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_AON_TIMER_AON_BASE_ADDR + TOP_ENGLISHBREAKFAST_AON_TIMER_AON_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_AON_TIMER_AON_SIZE_BYTES 0x40u

/**
 * Peripheral base address for ast in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_AST_BASE_ADDR 0x40480000u

/**
 * Peripheral size for ast in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_AST_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_AST_BASE_ADDR + TOP_ENGLISHBREAKFAST_AST_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_AST_SIZE_BYTES 0x400u

/**
 * Peripheral base address for core device on flash_ctrl in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_FLASH_CTRL_CORE_BASE_ADDR 0x41000000u

/**
 * Peripheral size for core device on flash_ctrl in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_FLASH_CTRL_CORE_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_FLASH_CTRL_CORE_BASE_ADDR + TOP_ENGLISHBREAKFAST_FLASH_CTRL_CORE_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_FLASH_CTRL_CORE_SIZE_BYTES 0x200u

/**
 * Peripheral base address for prim device on flash_ctrl in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_FLASH_CTRL_PRIM_BASE_ADDR 0x41008000u

/**
 * Peripheral size for prim device on flash_ctrl in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_FLASH_CTRL_PRIM_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_FLASH_CTRL_PRIM_BASE_ADDR + TOP_ENGLISHBREAKFAST_FLASH_CTRL_PRIM_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_FLASH_CTRL_PRIM_SIZE_BYTES 0x80u

/**
 * Peripheral base address for mem device on flash_ctrl in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_FLASH_CTRL_MEM_BASE_ADDR 0x20000000u

/**
 * Peripheral size for mem device on flash_ctrl in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_FLASH_CTRL_MEM_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_FLASH_CTRL_MEM_BASE_ADDR + TOP_ENGLISHBREAKFAST_FLASH_CTRL_MEM_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_FLASH_CTRL_MEM_SIZE_BYTES 0x10000u

/**
 * Peripheral base address for rv_plic in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_RV_PLIC_BASE_ADDR 0x48000000u

/**
 * Peripheral size for rv_plic in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_RV_PLIC_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_RV_PLIC_BASE_ADDR + TOP_ENGLISHBREAKFAST_RV_PLIC_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_RV_PLIC_SIZE_BYTES 0x8000000u

/**
 * Peripheral base address for aes in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_AES_BASE_ADDR 0x41100000u

/**
 * Peripheral size for aes in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_AES_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_AES_BASE_ADDR + TOP_ENGLISHBREAKFAST_AES_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_AES_SIZE_BYTES 0x100u

/**
 * Peripheral base address for regs device on sram_ctrl_main in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_SRAM_CTRL_MAIN_REGS_BASE_ADDR 0x411C0000u

/**
 * Peripheral size for regs device on sram_ctrl_main in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_SRAM_CTRL_MAIN_REGS_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_SRAM_CTRL_MAIN_REGS_BASE_ADDR + TOP_ENGLISHBREAKFAST_SRAM_CTRL_MAIN_REGS_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_SRAM_CTRL_MAIN_REGS_SIZE_BYTES 0x40u

/**
 * Peripheral base address for ram device on sram_ctrl_main in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_SRAM_CTRL_MAIN_RAM_BASE_ADDR 0x10000000u

/**
 * Peripheral size for ram device on sram_ctrl_main in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_SRAM_CTRL_MAIN_RAM_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_SRAM_CTRL_MAIN_RAM_BASE_ADDR + TOP_ENGLISHBREAKFAST_SRAM_CTRL_MAIN_RAM_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_SRAM_CTRL_MAIN_RAM_SIZE_BYTES 0x20000u

/**
 * Peripheral base address for regs device on rom_ctrl in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_ROM_CTRL_REGS_BASE_ADDR 0x411E0000u

/**
 * Peripheral size for regs device on rom_ctrl in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_ROM_CTRL_REGS_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_ROM_CTRL_REGS_BASE_ADDR + TOP_ENGLISHBREAKFAST_ROM_CTRL_REGS_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_ROM_CTRL_REGS_SIZE_BYTES 0x80u

/**
 * Peripheral base address for rom device on rom_ctrl in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_ROM_CTRL_ROM_BASE_ADDR 0x8000u

/**
 * Peripheral size for rom device on rom_ctrl in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_ROM_CTRL_ROM_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_ROM_CTRL_ROM_BASE_ADDR + TOP_ENGLISHBREAKFAST_ROM_CTRL_ROM_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_ROM_CTRL_ROM_SIZE_BYTES 0x8000u

/**
 * Peripheral base address for cfg device on rv_core_ibex in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_RV_CORE_IBEX_CFG_BASE_ADDR 0x411F0000u

/**
 * Peripheral size for cfg device on rv_core_ibex in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_RV_CORE_IBEX_CFG_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_RV_CORE_IBEX_CFG_BASE_ADDR + TOP_ENGLISHBREAKFAST_RV_CORE_IBEX_CFG_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_RV_CORE_IBEX_CFG_SIZE_BYTES 0x100u


/**
 * Memory base address for eflash in top englishbreakfast.
 */
#define TOP_ENGLISHBREAKFAST_EFLASH_BASE_ADDR 0x20000000u

/**
 * Memory size for eflash in top englishbreakfast.
 */
#define TOP_ENGLISHBREAKFAST_EFLASH_SIZE_BYTES 0x10000u

/**
 * Memory base address for ram_main in top englishbreakfast.
 */
#define TOP_ENGLISHBREAKFAST_RAM_MAIN_BASE_ADDR 0x10000000u

/**
 * Memory size for ram_main in top englishbreakfast.
 */
#define TOP_ENGLISHBREAKFAST_RAM_MAIN_SIZE_BYTES 0x20000u

/**
 * Memory base address for rom in top englishbreakfast.
 */
#define TOP_ENGLISHBREAKFAST_ROM_BASE_ADDR 0x8000u

/**
 * Memory size for rom in top englishbreakfast.
 */
#define TOP_ENGLISHBREAKFAST_ROM_SIZE_BYTES 0x8000u


/**
 * PLIC Interrupt Source Peripheral.
 *
 * Enumeration used to determine which peripheral asserted the corresponding
 * interrupt.
 */
typedef enum top_englishbreakfast_plic_peripheral {
  kTopEnglishbreakfastPlicPeripheralUnknown = 0, /**< Unknown Peripheral */
  kTopEnglishbreakfastPlicPeripheralUart0 = 1, /**< uart0 */
  kTopEnglishbreakfastPlicPeripheralUart1 = 2, /**< uart1 */
  kTopEnglishbreakfastPlicPeripheralGpio = 3, /**< gpio */
  kTopEnglishbreakfastPlicPeripheralSpiDevice = 4, /**< spi_device */
  kTopEnglishbreakfastPlicPeripheralSpiHost0 = 5, /**< spi_host0 */
  kTopEnglishbreakfastPlicPeripheralUsbdev = 6, /**< usbdev */
  kTopEnglishbreakfastPlicPeripheralPwrmgrAon = 7, /**< pwrmgr_aon */
  kTopEnglishbreakfastPlicPeripheralAonTimerAon = 8, /**< aon_timer_aon */
  kTopEnglishbreakfastPlicPeripheralFlashCtrl = 9, /**< flash_ctrl */
  kTopEnglishbreakfastPlicPeripheralLast = 9, /**< \internal Final PLIC peripheral */
} top_englishbreakfast_plic_peripheral_t;

/**
 * PLIC Interrupt Source.
 *
 * Enumeration of all PLIC interrupt sources. The interrupt sources belonging to
 * the same peripheral are guaranteed to be consecutive.
 */
typedef enum top_englishbreakfast_plic_irq_id {
  kTopEnglishbreakfastPlicIrqIdNone = 0, /**< No Interrupt */
  kTopEnglishbreakfastPlicIrqIdUart0TxWatermark = 1, /**< uart0_tx_watermark */
  kTopEnglishbreakfastPlicIrqIdUart0RxWatermark = 2, /**< uart0_rx_watermark */
  kTopEnglishbreakfastPlicIrqIdUart0TxDone = 3, /**< uart0_tx_done */
  kTopEnglishbreakfastPlicIrqIdUart0RxOverflow = 4, /**< uart0_rx_overflow */
  kTopEnglishbreakfastPlicIrqIdUart0RxFrameErr = 5, /**< uart0_rx_frame_err */
  kTopEnglishbreakfastPlicIrqIdUart0RxBreakErr = 6, /**< uart0_rx_break_err */
  kTopEnglishbreakfastPlicIrqIdUart0RxTimeout = 7, /**< uart0_rx_timeout */
  kTopEnglishbreakfastPlicIrqIdUart0RxParityErr = 8, /**< uart0_rx_parity_err */
  kTopEnglishbreakfastPlicIrqIdUart0TxEmpty = 9, /**< uart0_tx_empty */
  kTopEnglishbreakfastPlicIrqIdUart1TxWatermark = 10, /**< uart1_tx_watermark */
  kTopEnglishbreakfastPlicIrqIdUart1RxWatermark = 11, /**< uart1_rx_watermark */
  kTopEnglishbreakfastPlicIrqIdUart1TxDone = 12, /**< uart1_tx_done */
  kTopEnglishbreakfastPlicIrqIdUart1RxOverflow = 13, /**< uart1_rx_overflow */
  kTopEnglishbreakfastPlicIrqIdUart1RxFrameErr = 14, /**< uart1_rx_frame_err */
  kTopEnglishbreakfastPlicIrqIdUart1RxBreakErr = 15, /**< uart1_rx_break_err */
  kTopEnglishbreakfastPlicIrqIdUart1RxTimeout = 16, /**< uart1_rx_timeout */
  kTopEnglishbreakfastPlicIrqIdUart1RxParityErr = 17, /**< uart1_rx_parity_err */
  kTopEnglishbreakfastPlicIrqIdUart1TxEmpty = 18, /**< uart1_tx_empty */
  kTopEnglishbreakfastPlicIrqIdGpioGpio0 = 19, /**< gpio_gpio 0 */
  kTopEnglishbreakfastPlicIrqIdGpioGpio1 = 20, /**< gpio_gpio 1 */
  kTopEnglishbreakfastPlicIrqIdGpioGpio2 = 21, /**< gpio_gpio 2 */
  kTopEnglishbreakfastPlicIrqIdGpioGpio3 = 22, /**< gpio_gpio 3 */
  kTopEnglishbreakfastPlicIrqIdGpioGpio4 = 23, /**< gpio_gpio 4 */
  kTopEnglishbreakfastPlicIrqIdGpioGpio5 = 24, /**< gpio_gpio 5 */
  kTopEnglishbreakfastPlicIrqIdGpioGpio6 = 25, /**< gpio_gpio 6 */
  kTopEnglishbreakfastPlicIrqIdGpioGpio7 = 26, /**< gpio_gpio 7 */
  kTopEnglishbreakfastPlicIrqIdGpioGpio8 = 27, /**< gpio_gpio 8 */
  kTopEnglishbreakfastPlicIrqIdGpioGpio9 = 28, /**< gpio_gpio 9 */
  kTopEnglishbreakfastPlicIrqIdGpioGpio10 = 29, /**< gpio_gpio 10 */
  kTopEnglishbreakfastPlicIrqIdGpioGpio11 = 30, /**< gpio_gpio 11 */
  kTopEnglishbreakfastPlicIrqIdGpioGpio12 = 31, /**< gpio_gpio 12 */
  kTopEnglishbreakfastPlicIrqIdGpioGpio13 = 32, /**< gpio_gpio 13 */
  kTopEnglishbreakfastPlicIrqIdGpioGpio14 = 33, /**< gpio_gpio 14 */
  kTopEnglishbreakfastPlicIrqIdGpioGpio15 = 34, /**< gpio_gpio 15 */
  kTopEnglishbreakfastPlicIrqIdGpioGpio16 = 35, /**< gpio_gpio 16 */
  kTopEnglishbreakfastPlicIrqIdGpioGpio17 = 36, /**< gpio_gpio 17 */
  kTopEnglishbreakfastPlicIrqIdGpioGpio18 = 37, /**< gpio_gpio 18 */
  kTopEnglishbreakfastPlicIrqIdGpioGpio19 = 38, /**< gpio_gpio 19 */
  kTopEnglishbreakfastPlicIrqIdGpioGpio20 = 39, /**< gpio_gpio 20 */
  kTopEnglishbreakfastPlicIrqIdGpioGpio21 = 40, /**< gpio_gpio 21 */
  kTopEnglishbreakfastPlicIrqIdGpioGpio22 = 41, /**< gpio_gpio 22 */
  kTopEnglishbreakfastPlicIrqIdGpioGpio23 = 42, /**< gpio_gpio 23 */
  kTopEnglishbreakfastPlicIrqIdGpioGpio24 = 43, /**< gpio_gpio 24 */
  kTopEnglishbreakfastPlicIrqIdGpioGpio25 = 44, /**< gpio_gpio 25 */
  kTopEnglishbreakfastPlicIrqIdGpioGpio26 = 45, /**< gpio_gpio 26 */
  kTopEnglishbreakfastPlicIrqIdGpioGpio27 = 46, /**< gpio_gpio 27 */
  kTopEnglishbreakfastPlicIrqIdGpioGpio28 = 47, /**< gpio_gpio 28 */
  kTopEnglishbreakfastPlicIrqIdGpioGpio29 = 48, /**< gpio_gpio 29 */
  kTopEnglishbreakfastPlicIrqIdGpioGpio30 = 49, /**< gpio_gpio 30 */
  kTopEnglishbreakfastPlicIrqIdGpioGpio31 = 50, /**< gpio_gpio 31 */
  kTopEnglishbreakfastPlicIrqIdSpiDeviceUploadCmdfifoNotEmpty = 51, /**< spi_device_upload_cmdfifo_not_empty */
  kTopEnglishbreakfastPlicIrqIdSpiDeviceUploadPayloadNotEmpty = 52, /**< spi_device_upload_payload_not_empty */
  kTopEnglishbreakfastPlicIrqIdSpiDeviceUploadPayloadOverflow = 53, /**< spi_device_upload_payload_overflow */
  kTopEnglishbreakfastPlicIrqIdSpiDeviceReadbufWatermark = 54, /**< spi_device_readbuf_watermark */
  kTopEnglishbreakfastPlicIrqIdSpiDeviceReadbufFlip = 55, /**< spi_device_readbuf_flip */
  kTopEnglishbreakfastPlicIrqIdSpiDeviceTpmHeaderNotEmpty = 56, /**< spi_device_tpm_header_not_empty */
  kTopEnglishbreakfastPlicIrqIdSpiDeviceTpmRdfifoCmdEnd = 57, /**< spi_device_tpm_rdfifo_cmd_end */
  kTopEnglishbreakfastPlicIrqIdSpiDeviceTpmRdfifoDrop = 58, /**< spi_device_tpm_rdfifo_drop */
  kTopEnglishbreakfastPlicIrqIdSpiHost0Error = 59, /**< spi_host0_error */
  kTopEnglishbreakfastPlicIrqIdSpiHost0SpiEvent = 60, /**< spi_host0_spi_event */
  kTopEnglishbreakfastPlicIrqIdUsbdevPktReceived = 61, /**< usbdev_pkt_received */
  kTopEnglishbreakfastPlicIrqIdUsbdevPktSent = 62, /**< usbdev_pkt_sent */
  kTopEnglishbreakfastPlicIrqIdUsbdevDisconnected = 63, /**< usbdev_disconnected */
  kTopEnglishbreakfastPlicIrqIdUsbdevHostLost = 64, /**< usbdev_host_lost */
  kTopEnglishbreakfastPlicIrqIdUsbdevLinkReset = 65, /**< usbdev_link_reset */
  kTopEnglishbreakfastPlicIrqIdUsbdevLinkSuspend = 66, /**< usbdev_link_suspend */
  kTopEnglishbreakfastPlicIrqIdUsbdevLinkResume = 67, /**< usbdev_link_resume */
  kTopEnglishbreakfastPlicIrqIdUsbdevAvOutEmpty = 68, /**< usbdev_av_out_empty */
  kTopEnglishbreakfastPlicIrqIdUsbdevRxFull = 69, /**< usbdev_rx_full */
  kTopEnglishbreakfastPlicIrqIdUsbdevAvOverflow = 70, /**< usbdev_av_overflow */
  kTopEnglishbreakfastPlicIrqIdUsbdevLinkInErr = 71, /**< usbdev_link_in_err */
  kTopEnglishbreakfastPlicIrqIdUsbdevRxCrcErr = 72, /**< usbdev_rx_crc_err */
  kTopEnglishbreakfastPlicIrqIdUsbdevRxPidErr = 73, /**< usbdev_rx_pid_err */
  kTopEnglishbreakfastPlicIrqIdUsbdevRxBitstuffErr = 74, /**< usbdev_rx_bitstuff_err */
  kTopEnglishbreakfastPlicIrqIdUsbdevFrame = 75, /**< usbdev_frame */
  kTopEnglishbreakfastPlicIrqIdUsbdevPowered = 76, /**< usbdev_powered */
  kTopEnglishbreakfastPlicIrqIdUsbdevLinkOutErr = 77, /**< usbdev_link_out_err */
  kTopEnglishbreakfastPlicIrqIdUsbdevAvSetupEmpty = 78, /**< usbdev_av_setup_empty */
  kTopEnglishbreakfastPlicIrqIdPwrmgrAonWakeup = 79, /**< pwrmgr_aon_wakeup */
  kTopEnglishbreakfastPlicIrqIdAonTimerAonWkupTimerExpired = 80, /**< aon_timer_aon_wkup_timer_expired */
  kTopEnglishbreakfastPlicIrqIdAonTimerAonWdogTimerBark = 81, /**< aon_timer_aon_wdog_timer_bark */
  kTopEnglishbreakfastPlicIrqIdFlashCtrlProgEmpty = 82, /**< flash_ctrl_prog_empty */
  kTopEnglishbreakfastPlicIrqIdFlashCtrlProgLvl = 83, /**< flash_ctrl_prog_lvl */
  kTopEnglishbreakfastPlicIrqIdFlashCtrlRdFull = 84, /**< flash_ctrl_rd_full */
  kTopEnglishbreakfastPlicIrqIdFlashCtrlRdLvl = 85, /**< flash_ctrl_rd_lvl */
  kTopEnglishbreakfastPlicIrqIdFlashCtrlOpDone = 86, /**< flash_ctrl_op_done */
  kTopEnglishbreakfastPlicIrqIdFlashCtrlCorrErr = 87, /**< flash_ctrl_corr_err */
  kTopEnglishbreakfastPlicIrqIdLast = 87, /**< \internal The Last Valid Interrupt ID. */
} top_englishbreakfast_plic_irq_id_t;

/**
 * PLIC Interrupt Source to Peripheral Map
 *
 * This array is a mapping from `top_englishbreakfast_plic_irq_id_t` to
 * `top_englishbreakfast_plic_peripheral_t`.
 */
extern const top_englishbreakfast_plic_peripheral_t
    top_englishbreakfast_plic_interrupt_for_peripheral[88];

/**
 * PLIC Interrupt Target.
 *
 * Enumeration used to determine which set of IE, CC, threshold registers to
 * access for a given interrupt target.
 */
typedef enum top_englishbreakfast_plic_target {
  kTopEnglishbreakfastPlicTargetIbex0 = 0, /**< Ibex Core 0 */
  kTopEnglishbreakfastPlicTargetLast = 0, /**< \internal Final PLIC target */
} top_englishbreakfast_plic_target_t;

/**
 * Alert Handler Source Peripheral.
 *
 * Enumeration used to determine which peripheral asserted the corresponding
 * alert.
 */
typedef enum top_englishbreakfast_alert_peripheral {
  kTopEnglishbreakfastAlertPeripheralUart0 = 0, /**< uart0 */
  kTopEnglishbreakfastAlertPeripheralUart1 = 1, /**< uart1 */
  kTopEnglishbreakfastAlertPeripheralGpio = 2, /**< gpio */
  kTopEnglishbreakfastAlertPeripheralSpiDevice = 3, /**< spi_device */
  kTopEnglishbreakfastAlertPeripheralSpiHost0 = 4, /**< spi_host0 */
  kTopEnglishbreakfastAlertPeripheralRvTimer = 5, /**< rv_timer */
  kTopEnglishbreakfastAlertPeripheralUsbdev = 6, /**< usbdev */
  kTopEnglishbreakfastAlertPeripheralPwrmgrAon = 7, /**< pwrmgr_aon */
  kTopEnglishbreakfastAlertPeripheralRstmgrAon = 8, /**< rstmgr_aon */
  kTopEnglishbreakfastAlertPeripheralClkmgrAon = 9, /**< clkmgr_aon */
  kTopEnglishbreakfastAlertPeripheralPinmuxAon = 10, /**< pinmux_aon */
  kTopEnglishbreakfastAlertPeripheralAonTimerAon = 11, /**< aon_timer_aon */
  kTopEnglishbreakfastAlertPeripheralFlashCtrl = 12, /**< flash_ctrl */
  kTopEnglishbreakfastAlertPeripheralRvPlic = 13, /**< rv_plic */
  kTopEnglishbreakfastAlertPeripheralAes = 14, /**< aes */
  kTopEnglishbreakfastAlertPeripheralSramCtrlMain = 15, /**< sram_ctrl_main */
  kTopEnglishbreakfastAlertPeripheralRomCtrl = 16, /**< rom_ctrl */
  kTopEnglishbreakfastAlertPeripheralRvCoreIbex = 17, /**< rv_core_ibex */
  kTopEnglishbreakfastAlertPeripheralLast = 17, /**< \internal Final Alert peripheral */
} top_englishbreakfast_alert_peripheral_t;

/**
 * Alert Handler Alert Source.
 *
 * Enumeration of all Alert Handler Alert Sources. The alert sources belonging to
 * the same peripheral are guaranteed to be consecutive.
 */
typedef enum top_englishbreakfast_alert_id {
  kTopEnglishbreakfastAlertIdUart0FatalFault = 0, /**< uart0_fatal_fault */
  kTopEnglishbreakfastAlertIdUart1FatalFault = 1, /**< uart1_fatal_fault */
  kTopEnglishbreakfastAlertIdGpioFatalFault = 2, /**< gpio_fatal_fault */
  kTopEnglishbreakfastAlertIdSpiDeviceFatalFault = 3, /**< spi_device_fatal_fault */
  kTopEnglishbreakfastAlertIdSpiHost0FatalFault = 4, /**< spi_host0_fatal_fault */
  kTopEnglishbreakfastAlertIdRvTimerFatalFault = 5, /**< rv_timer_fatal_fault */
  kTopEnglishbreakfastAlertIdUsbdevFatalFault = 6, /**< usbdev_fatal_fault */
  kTopEnglishbreakfastAlertIdPwrmgrAonFatalFault = 7, /**< pwrmgr_aon_fatal_fault */
  kTopEnglishbreakfastAlertIdRstmgrAonFatalFault = 8, /**< rstmgr_aon_fatal_fault */
  kTopEnglishbreakfastAlertIdRstmgrAonFatalCnstyFault = 9, /**< rstmgr_aon_fatal_cnsty_fault */
  kTopEnglishbreakfastAlertIdClkmgrAonRecovFault = 10, /**< clkmgr_aon_recov_fault */
  kTopEnglishbreakfastAlertIdClkmgrAonFatalFault = 11, /**< clkmgr_aon_fatal_fault */
  kTopEnglishbreakfastAlertIdPinmuxAonFatalFault = 12, /**< pinmux_aon_fatal_fault */
  kTopEnglishbreakfastAlertIdAonTimerAonFatalFault = 13, /**< aon_timer_aon_fatal_fault */
  kTopEnglishbreakfastAlertIdFlashCtrlRecovErr = 14, /**< flash_ctrl_recov_err */
  kTopEnglishbreakfastAlertIdFlashCtrlFatalStdErr = 15, /**< flash_ctrl_fatal_std_err */
  kTopEnglishbreakfastAlertIdFlashCtrlFatalErr = 16, /**< flash_ctrl_fatal_err */
  kTopEnglishbreakfastAlertIdFlashCtrlFatalPrimFlashAlert = 17, /**< flash_ctrl_fatal_prim_flash_alert */
  kTopEnglishbreakfastAlertIdFlashCtrlRecovPrimFlashAlert = 18, /**< flash_ctrl_recov_prim_flash_alert */
  kTopEnglishbreakfastAlertIdRvPlicFatalFault = 19, /**< rv_plic_fatal_fault */
  kTopEnglishbreakfastAlertIdAesRecovCtrlUpdateErr = 20, /**< aes_recov_ctrl_update_err */
  kTopEnglishbreakfastAlertIdAesFatalFault = 21, /**< aes_fatal_fault */
  kTopEnglishbreakfastAlertIdSramCtrlMainFatalError = 22, /**< sram_ctrl_main_fatal_error */
  kTopEnglishbreakfastAlertIdRomCtrlFatal = 23, /**< rom_ctrl_fatal */
  kTopEnglishbreakfastAlertIdRvCoreIbexFatalSwErr = 24, /**< rv_core_ibex_fatal_sw_err */
  kTopEnglishbreakfastAlertIdRvCoreIbexRecovSwErr = 25, /**< rv_core_ibex_recov_sw_err */
  kTopEnglishbreakfastAlertIdRvCoreIbexFatalHwErr = 26, /**< rv_core_ibex_fatal_hw_err */
  kTopEnglishbreakfastAlertIdRvCoreIbexRecovHwErr = 27, /**< rv_core_ibex_recov_hw_err */
  kTopEnglishbreakfastAlertIdLast = 27, /**< \internal The Last Valid Alert ID. */
} top_englishbreakfast_alert_id_t;

/**
 * Alert Handler Alert Source to Peripheral Map
 *
 * This array is a mapping from `top_englishbreakfast_alert_id_t` to
 * `top_englishbreakfast_alert_peripheral_t`.
 */
extern const top_englishbreakfast_alert_peripheral_t
    top_englishbreakfast_alert_for_peripheral[28];

#define PINMUX_MIO_PERIPH_INSEL_IDX_OFFSET 2

// PERIPH_INSEL ranges from 0 to NUM_MIO_PADS + 2 -1}
//  0 and 1 are tied to value 0 and 1
#define NUM_MIO_PADS 47
#define NUM_DIO_PADS 14

#define PINMUX_PERIPH_OUTSEL_IDX_OFFSET 3

/**
 * Pinmux Peripheral Input.
 */
typedef enum top_englishbreakfast_pinmux_peripheral_in {
  kTopEnglishbreakfastPinmuxPeripheralInGpioGpio0 = 0, /**< Peripheral Input 0 */
  kTopEnglishbreakfastPinmuxPeripheralInGpioGpio1 = 1, /**< Peripheral Input 1 */
  kTopEnglishbreakfastPinmuxPeripheralInGpioGpio2 = 2, /**< Peripheral Input 2 */
  kTopEnglishbreakfastPinmuxPeripheralInGpioGpio3 = 3, /**< Peripheral Input 3 */
  kTopEnglishbreakfastPinmuxPeripheralInGpioGpio4 = 4, /**< Peripheral Input 4 */
  kTopEnglishbreakfastPinmuxPeripheralInGpioGpio5 = 5, /**< Peripheral Input 5 */
  kTopEnglishbreakfastPinmuxPeripheralInGpioGpio6 = 6, /**< Peripheral Input 6 */
  kTopEnglishbreakfastPinmuxPeripheralInGpioGpio7 = 7, /**< Peripheral Input 7 */
  kTopEnglishbreakfastPinmuxPeripheralInGpioGpio8 = 8, /**< Peripheral Input 8 */
  kTopEnglishbreakfastPinmuxPeripheralInGpioGpio9 = 9, /**< Peripheral Input 9 */
  kTopEnglishbreakfastPinmuxPeripheralInGpioGpio10 = 10, /**< Peripheral Input 10 */
  kTopEnglishbreakfastPinmuxPeripheralInGpioGpio11 = 11, /**< Peripheral Input 11 */
  kTopEnglishbreakfastPinmuxPeripheralInGpioGpio12 = 12, /**< Peripheral Input 12 */
  kTopEnglishbreakfastPinmuxPeripheralInGpioGpio13 = 13, /**< Peripheral Input 13 */
  kTopEnglishbreakfastPinmuxPeripheralInGpioGpio14 = 14, /**< Peripheral Input 14 */
  kTopEnglishbreakfastPinmuxPeripheralInGpioGpio15 = 15, /**< Peripheral Input 15 */
  kTopEnglishbreakfastPinmuxPeripheralInGpioGpio16 = 16, /**< Peripheral Input 16 */
  kTopEnglishbreakfastPinmuxPeripheralInGpioGpio17 = 17, /**< Peripheral Input 17 */
  kTopEnglishbreakfastPinmuxPeripheralInGpioGpio18 = 18, /**< Peripheral Input 18 */
  kTopEnglishbreakfastPinmuxPeripheralInGpioGpio19 = 19, /**< Peripheral Input 19 */
  kTopEnglishbreakfastPinmuxPeripheralInGpioGpio20 = 20, /**< Peripheral Input 20 */
  kTopEnglishbreakfastPinmuxPeripheralInGpioGpio21 = 21, /**< Peripheral Input 21 */
  kTopEnglishbreakfastPinmuxPeripheralInGpioGpio22 = 22, /**< Peripheral Input 22 */
  kTopEnglishbreakfastPinmuxPeripheralInGpioGpio23 = 23, /**< Peripheral Input 23 */
  kTopEnglishbreakfastPinmuxPeripheralInGpioGpio24 = 24, /**< Peripheral Input 24 */
  kTopEnglishbreakfastPinmuxPeripheralInGpioGpio25 = 25, /**< Peripheral Input 25 */
  kTopEnglishbreakfastPinmuxPeripheralInGpioGpio26 = 26, /**< Peripheral Input 26 */
  kTopEnglishbreakfastPinmuxPeripheralInGpioGpio27 = 27, /**< Peripheral Input 27 */
  kTopEnglishbreakfastPinmuxPeripheralInGpioGpio28 = 28, /**< Peripheral Input 28 */
  kTopEnglishbreakfastPinmuxPeripheralInGpioGpio29 = 29, /**< Peripheral Input 29 */
  kTopEnglishbreakfastPinmuxPeripheralInGpioGpio30 = 30, /**< Peripheral Input 30 */
  kTopEnglishbreakfastPinmuxPeripheralInGpioGpio31 = 31, /**< Peripheral Input 31 */
  kTopEnglishbreakfastPinmuxPeripheralInUart0Rx = 32, /**< Peripheral Input 32 */
  kTopEnglishbreakfastPinmuxPeripheralInUart1Rx = 33, /**< Peripheral Input 33 */
  kTopEnglishbreakfastPinmuxPeripheralInFlashCtrlTck = 34, /**< Peripheral Input 34 */
  kTopEnglishbreakfastPinmuxPeripheralInFlashCtrlTms = 35, /**< Peripheral Input 35 */
  kTopEnglishbreakfastPinmuxPeripheralInFlashCtrlTdi = 36, /**< Peripheral Input 36 */
  kTopEnglishbreakfastPinmuxPeripheralInUsbdevSense = 37, /**< Peripheral Input 37 */
  kTopEnglishbreakfastPinmuxPeripheralInLast = 37, /**< \internal Last valid peripheral input */
} top_englishbreakfast_pinmux_peripheral_in_t;

/**
 * Pinmux MIO Input Selector.
 */
typedef enum top_englishbreakfast_pinmux_insel {
  kTopEnglishbreakfastPinmuxInselConstantZero = 0, /**< Tie constantly to zero */
  kTopEnglishbreakfastPinmuxInselConstantOne = 1, /**< Tie constantly to one */
  kTopEnglishbreakfastPinmuxInselIoa0 = 2, /**< MIO Pad 0 */
  kTopEnglishbreakfastPinmuxInselIoa1 = 3, /**< MIO Pad 1 */
  kTopEnglishbreakfastPinmuxInselIoa2 = 4, /**< MIO Pad 2 */
  kTopEnglishbreakfastPinmuxInselIoa3 = 5, /**< MIO Pad 3 */
  kTopEnglishbreakfastPinmuxInselIoa4 = 6, /**< MIO Pad 4 */
  kTopEnglishbreakfastPinmuxInselIoa5 = 7, /**< MIO Pad 5 */
  kTopEnglishbreakfastPinmuxInselIoa6 = 8, /**< MIO Pad 6 */
  kTopEnglishbreakfastPinmuxInselIoa7 = 9, /**< MIO Pad 7 */
  kTopEnglishbreakfastPinmuxInselIoa8 = 10, /**< MIO Pad 8 */
  kTopEnglishbreakfastPinmuxInselIob0 = 11, /**< MIO Pad 9 */
  kTopEnglishbreakfastPinmuxInselIob1 = 12, /**< MIO Pad 10 */
  kTopEnglishbreakfastPinmuxInselIob2 = 13, /**< MIO Pad 11 */
  kTopEnglishbreakfastPinmuxInselIob3 = 14, /**< MIO Pad 12 */
  kTopEnglishbreakfastPinmuxInselIob4 = 15, /**< MIO Pad 13 */
  kTopEnglishbreakfastPinmuxInselIob5 = 16, /**< MIO Pad 14 */
  kTopEnglishbreakfastPinmuxInselIob6 = 17, /**< MIO Pad 15 */
  kTopEnglishbreakfastPinmuxInselIob7 = 18, /**< MIO Pad 16 */
  kTopEnglishbreakfastPinmuxInselIob8 = 19, /**< MIO Pad 17 */
  kTopEnglishbreakfastPinmuxInselIob9 = 20, /**< MIO Pad 18 */
  kTopEnglishbreakfastPinmuxInselIob10 = 21, /**< MIO Pad 19 */
  kTopEnglishbreakfastPinmuxInselIob11 = 22, /**< MIO Pad 20 */
  kTopEnglishbreakfastPinmuxInselIob12 = 23, /**< MIO Pad 21 */
  kTopEnglishbreakfastPinmuxInselIoc0 = 24, /**< MIO Pad 22 */
  kTopEnglishbreakfastPinmuxInselIoc1 = 25, /**< MIO Pad 23 */
  kTopEnglishbreakfastPinmuxInselIoc2 = 26, /**< MIO Pad 24 */
  kTopEnglishbreakfastPinmuxInselIoc3 = 27, /**< MIO Pad 25 */
  kTopEnglishbreakfastPinmuxInselIoc4 = 28, /**< MIO Pad 26 */
  kTopEnglishbreakfastPinmuxInselIoc5 = 29, /**< MIO Pad 27 */
  kTopEnglishbreakfastPinmuxInselIoc6 = 30, /**< MIO Pad 28 */
  kTopEnglishbreakfastPinmuxInselIoc7 = 31, /**< MIO Pad 29 */
  kTopEnglishbreakfastPinmuxInselIoc8 = 32, /**< MIO Pad 30 */
  kTopEnglishbreakfastPinmuxInselIoc9 = 33, /**< MIO Pad 31 */
  kTopEnglishbreakfastPinmuxInselIoc10 = 34, /**< MIO Pad 32 */
  kTopEnglishbreakfastPinmuxInselIoc11 = 35, /**< MIO Pad 33 */
  kTopEnglishbreakfastPinmuxInselIoc12 = 36, /**< MIO Pad 34 */
  kTopEnglishbreakfastPinmuxInselIor0 = 37, /**< MIO Pad 35 */
  kTopEnglishbreakfastPinmuxInselIor1 = 38, /**< MIO Pad 36 */
  kTopEnglishbreakfastPinmuxInselIor2 = 39, /**< MIO Pad 37 */
  kTopEnglishbreakfastPinmuxInselIor3 = 40, /**< MIO Pad 38 */
  kTopEnglishbreakfastPinmuxInselIor4 = 41, /**< MIO Pad 39 */
  kTopEnglishbreakfastPinmuxInselIor5 = 42, /**< MIO Pad 40 */
  kTopEnglishbreakfastPinmuxInselIor6 = 43, /**< MIO Pad 41 */
  kTopEnglishbreakfastPinmuxInselIor7 = 44, /**< MIO Pad 42 */
  kTopEnglishbreakfastPinmuxInselIor10 = 45, /**< MIO Pad 43 */
  kTopEnglishbreakfastPinmuxInselIor11 = 46, /**< MIO Pad 44 */
  kTopEnglishbreakfastPinmuxInselIor12 = 47, /**< MIO Pad 45 */
  kTopEnglishbreakfastPinmuxInselIor13 = 48, /**< MIO Pad 46 */
  kTopEnglishbreakfastPinmuxInselLast = 48, /**< \internal Last valid insel value */
} top_englishbreakfast_pinmux_insel_t;

/**
 * Pinmux MIO Output.
 */
typedef enum top_englishbreakfast_pinmux_mio_out {
  kTopEnglishbreakfastPinmuxMioOutIoa0 = 0, /**< MIO Pad 0 */
  kTopEnglishbreakfastPinmuxMioOutIoa1 = 1, /**< MIO Pad 1 */
  kTopEnglishbreakfastPinmuxMioOutIoa2 = 2, /**< MIO Pad 2 */
  kTopEnglishbreakfastPinmuxMioOutIoa3 = 3, /**< MIO Pad 3 */
  kTopEnglishbreakfastPinmuxMioOutIoa4 = 4, /**< MIO Pad 4 */
  kTopEnglishbreakfastPinmuxMioOutIoa5 = 5, /**< MIO Pad 5 */
  kTopEnglishbreakfastPinmuxMioOutIoa6 = 6, /**< MIO Pad 6 */
  kTopEnglishbreakfastPinmuxMioOutIoa7 = 7, /**< MIO Pad 7 */
  kTopEnglishbreakfastPinmuxMioOutIoa8 = 8, /**< MIO Pad 8 */
  kTopEnglishbreakfastPinmuxMioOutIob0 = 9, /**< MIO Pad 9 */
  kTopEnglishbreakfastPinmuxMioOutIob1 = 10, /**< MIO Pad 10 */
  kTopEnglishbreakfastPinmuxMioOutIob2 = 11, /**< MIO Pad 11 */
  kTopEnglishbreakfastPinmuxMioOutIob3 = 12, /**< MIO Pad 12 */
  kTopEnglishbreakfastPinmuxMioOutIob4 = 13, /**< MIO Pad 13 */
  kTopEnglishbreakfastPinmuxMioOutIob5 = 14, /**< MIO Pad 14 */
  kTopEnglishbreakfastPinmuxMioOutIob6 = 15, /**< MIO Pad 15 */
  kTopEnglishbreakfastPinmuxMioOutIob7 = 16, /**< MIO Pad 16 */
  kTopEnglishbreakfastPinmuxMioOutIob8 = 17, /**< MIO Pad 17 */
  kTopEnglishbreakfastPinmuxMioOutIob9 = 18, /**< MIO Pad 18 */
  kTopEnglishbreakfastPinmuxMioOutIob10 = 19, /**< MIO Pad 19 */
  kTopEnglishbreakfastPinmuxMioOutIob11 = 20, /**< MIO Pad 20 */
  kTopEnglishbreakfastPinmuxMioOutIob12 = 21, /**< MIO Pad 21 */
  kTopEnglishbreakfastPinmuxMioOutIoc0 = 22, /**< MIO Pad 22 */
  kTopEnglishbreakfastPinmuxMioOutIoc1 = 23, /**< MIO Pad 23 */
  kTopEnglishbreakfastPinmuxMioOutIoc2 = 24, /**< MIO Pad 24 */
  kTopEnglishbreakfastPinmuxMioOutIoc3 = 25, /**< MIO Pad 25 */
  kTopEnglishbreakfastPinmuxMioOutIoc4 = 26, /**< MIO Pad 26 */
  kTopEnglishbreakfastPinmuxMioOutIoc5 = 27, /**< MIO Pad 27 */
  kTopEnglishbreakfastPinmuxMioOutIoc6 = 28, /**< MIO Pad 28 */
  kTopEnglishbreakfastPinmuxMioOutIoc7 = 29, /**< MIO Pad 29 */
  kTopEnglishbreakfastPinmuxMioOutIoc8 = 30, /**< MIO Pad 30 */
  kTopEnglishbreakfastPinmuxMioOutIoc9 = 31, /**< MIO Pad 31 */
  kTopEnglishbreakfastPinmuxMioOutIoc10 = 32, /**< MIO Pad 32 */
  kTopEnglishbreakfastPinmuxMioOutIoc11 = 33, /**< MIO Pad 33 */
  kTopEnglishbreakfastPinmuxMioOutIoc12 = 34, /**< MIO Pad 34 */
  kTopEnglishbreakfastPinmuxMioOutIor0 = 35, /**< MIO Pad 35 */
  kTopEnglishbreakfastPinmuxMioOutIor1 = 36, /**< MIO Pad 36 */
  kTopEnglishbreakfastPinmuxMioOutIor2 = 37, /**< MIO Pad 37 */
  kTopEnglishbreakfastPinmuxMioOutIor3 = 38, /**< MIO Pad 38 */
  kTopEnglishbreakfastPinmuxMioOutIor4 = 39, /**< MIO Pad 39 */
  kTopEnglishbreakfastPinmuxMioOutIor5 = 40, /**< MIO Pad 40 */
  kTopEnglishbreakfastPinmuxMioOutIor6 = 41, /**< MIO Pad 41 */
  kTopEnglishbreakfastPinmuxMioOutIor7 = 42, /**< MIO Pad 42 */
  kTopEnglishbreakfastPinmuxMioOutIor10 = 43, /**< MIO Pad 43 */
  kTopEnglishbreakfastPinmuxMioOutIor11 = 44, /**< MIO Pad 44 */
  kTopEnglishbreakfastPinmuxMioOutIor12 = 45, /**< MIO Pad 45 */
  kTopEnglishbreakfastPinmuxMioOutIor13 = 46, /**< MIO Pad 46 */
  kTopEnglishbreakfastPinmuxMioOutLast = 46, /**< \internal Last valid mio output */
} top_englishbreakfast_pinmux_mio_out_t;

/**
 * Pinmux Peripheral Output Selector.
 */
typedef enum top_englishbreakfast_pinmux_outsel {
  kTopEnglishbreakfastPinmuxOutselConstantZero = 0, /**< Tie constantly to zero */
  kTopEnglishbreakfastPinmuxOutselConstantOne = 1, /**< Tie constantly to one */
  kTopEnglishbreakfastPinmuxOutselConstantHighZ = 2, /**< Tie constantly to high-Z */
  kTopEnglishbreakfastPinmuxOutselGpioGpio0 = 3, /**< Peripheral Output 0 */
  kTopEnglishbreakfastPinmuxOutselGpioGpio1 = 4, /**< Peripheral Output 1 */
  kTopEnglishbreakfastPinmuxOutselGpioGpio2 = 5, /**< Peripheral Output 2 */
  kTopEnglishbreakfastPinmuxOutselGpioGpio3 = 6, /**< Peripheral Output 3 */
  kTopEnglishbreakfastPinmuxOutselGpioGpio4 = 7, /**< Peripheral Output 4 */
  kTopEnglishbreakfastPinmuxOutselGpioGpio5 = 8, /**< Peripheral Output 5 */
  kTopEnglishbreakfastPinmuxOutselGpioGpio6 = 9, /**< Peripheral Output 6 */
  kTopEnglishbreakfastPinmuxOutselGpioGpio7 = 10, /**< Peripheral Output 7 */
  kTopEnglishbreakfastPinmuxOutselGpioGpio8 = 11, /**< Peripheral Output 8 */
  kTopEnglishbreakfastPinmuxOutselGpioGpio9 = 12, /**< Peripheral Output 9 */
  kTopEnglishbreakfastPinmuxOutselGpioGpio10 = 13, /**< Peripheral Output 10 */
  kTopEnglishbreakfastPinmuxOutselGpioGpio11 = 14, /**< Peripheral Output 11 */
  kTopEnglishbreakfastPinmuxOutselGpioGpio12 = 15, /**< Peripheral Output 12 */
  kTopEnglishbreakfastPinmuxOutselGpioGpio13 = 16, /**< Peripheral Output 13 */
  kTopEnglishbreakfastPinmuxOutselGpioGpio14 = 17, /**< Peripheral Output 14 */
  kTopEnglishbreakfastPinmuxOutselGpioGpio15 = 18, /**< Peripheral Output 15 */
  kTopEnglishbreakfastPinmuxOutselGpioGpio16 = 19, /**< Peripheral Output 16 */
  kTopEnglishbreakfastPinmuxOutselGpioGpio17 = 20, /**< Peripheral Output 17 */
  kTopEnglishbreakfastPinmuxOutselGpioGpio18 = 21, /**< Peripheral Output 18 */
  kTopEnglishbreakfastPinmuxOutselGpioGpio19 = 22, /**< Peripheral Output 19 */
  kTopEnglishbreakfastPinmuxOutselGpioGpio20 = 23, /**< Peripheral Output 20 */
  kTopEnglishbreakfastPinmuxOutselGpioGpio21 = 24, /**< Peripheral Output 21 */
  kTopEnglishbreakfastPinmuxOutselGpioGpio22 = 25, /**< Peripheral Output 22 */
  kTopEnglishbreakfastPinmuxOutselGpioGpio23 = 26, /**< Peripheral Output 23 */
  kTopEnglishbreakfastPinmuxOutselGpioGpio24 = 27, /**< Peripheral Output 24 */
  kTopEnglishbreakfastPinmuxOutselGpioGpio25 = 28, /**< Peripheral Output 25 */
  kTopEnglishbreakfastPinmuxOutselGpioGpio26 = 29, /**< Peripheral Output 26 */
  kTopEnglishbreakfastPinmuxOutselGpioGpio27 = 30, /**< Peripheral Output 27 */
  kTopEnglishbreakfastPinmuxOutselGpioGpio28 = 31, /**< Peripheral Output 28 */
  kTopEnglishbreakfastPinmuxOutselGpioGpio29 = 32, /**< Peripheral Output 29 */
  kTopEnglishbreakfastPinmuxOutselGpioGpio30 = 33, /**< Peripheral Output 30 */
  kTopEnglishbreakfastPinmuxOutselGpioGpio31 = 34, /**< Peripheral Output 31 */
  kTopEnglishbreakfastPinmuxOutselUart0Tx = 35, /**< Peripheral Output 32 */
  kTopEnglishbreakfastPinmuxOutselUart1Tx = 36, /**< Peripheral Output 33 */
  kTopEnglishbreakfastPinmuxOutselFlashCtrlTdo = 37, /**< Peripheral Output 34 */
  kTopEnglishbreakfastPinmuxOutselLast = 37, /**< \internal Last valid outsel value */
} top_englishbreakfast_pinmux_outsel_t;

/**
 * Dedicated Pad Selects
 */
typedef enum top_englishbreakfast_direct_pads {
  kTopEnglishbreakfastDirectPadsSpiHost0Sd0 = 0, /**<  */
  kTopEnglishbreakfastDirectPadsSpiHost0Sd1 = 1, /**<  */
  kTopEnglishbreakfastDirectPadsSpiHost0Sd2 = 2, /**<  */
  kTopEnglishbreakfastDirectPadsSpiHost0Sd3 = 3, /**<  */
  kTopEnglishbreakfastDirectPadsSpiDeviceSd0 = 4, /**<  */
  kTopEnglishbreakfastDirectPadsSpiDeviceSd1 = 5, /**<  */
  kTopEnglishbreakfastDirectPadsSpiDeviceSd2 = 6, /**<  */
  kTopEnglishbreakfastDirectPadsSpiDeviceSd3 = 7, /**<  */
  kTopEnglishbreakfastDirectPadsUsbdevUsbDp = 8, /**<  */
  kTopEnglishbreakfastDirectPadsUsbdevUsbDn = 9, /**<  */
  kTopEnglishbreakfastDirectPadsSpiDeviceSck = 10, /**<  */
  kTopEnglishbreakfastDirectPadsSpiDeviceCsb = 11, /**<  */
  kTopEnglishbreakfastDirectPadsSpiHost0Sck = 12, /**<  */
  kTopEnglishbreakfastDirectPadsSpiHost0Csb = 13, /**<  */
  kTopEnglishbreakfastDirectPadsLast = 13, /**< \internal Last valid direct pad */
} top_englishbreakfast_direct_pads_t;

/**
 * Muxed Pad Selects
 */
typedef enum top_englishbreakfast_muxed_pads {
  kTopEnglishbreakfastMuxedPadsIoa0 = 0, /**<  */
  kTopEnglishbreakfastMuxedPadsIoa1 = 1, /**<  */
  kTopEnglishbreakfastMuxedPadsIoa2 = 2, /**<  */
  kTopEnglishbreakfastMuxedPadsIoa3 = 3, /**<  */
  kTopEnglishbreakfastMuxedPadsIoa4 = 4, /**<  */
  kTopEnglishbreakfastMuxedPadsIoa5 = 5, /**<  */
  kTopEnglishbreakfastMuxedPadsIoa6 = 6, /**<  */
  kTopEnglishbreakfastMuxedPadsIoa7 = 7, /**<  */
  kTopEnglishbreakfastMuxedPadsIoa8 = 8, /**<  */
  kTopEnglishbreakfastMuxedPadsIob0 = 9, /**<  */
  kTopEnglishbreakfastMuxedPadsIob1 = 10, /**<  */
  kTopEnglishbreakfastMuxedPadsIob2 = 11, /**<  */
  kTopEnglishbreakfastMuxedPadsIob3 = 12, /**<  */
  kTopEnglishbreakfastMuxedPadsIob4 = 13, /**<  */
  kTopEnglishbreakfastMuxedPadsIob5 = 14, /**<  */
  kTopEnglishbreakfastMuxedPadsIob6 = 15, /**<  */
  kTopEnglishbreakfastMuxedPadsIob7 = 16, /**<  */
  kTopEnglishbreakfastMuxedPadsIob8 = 17, /**<  */
  kTopEnglishbreakfastMuxedPadsIob9 = 18, /**<  */
  kTopEnglishbreakfastMuxedPadsIob10 = 19, /**<  */
  kTopEnglishbreakfastMuxedPadsIob11 = 20, /**<  */
  kTopEnglishbreakfastMuxedPadsIob12 = 21, /**<  */
  kTopEnglishbreakfastMuxedPadsIoc0 = 22, /**<  */
  kTopEnglishbreakfastMuxedPadsIoc1 = 23, /**<  */
  kTopEnglishbreakfastMuxedPadsIoc2 = 24, /**<  */
  kTopEnglishbreakfastMuxedPadsIoc3 = 25, /**<  */
  kTopEnglishbreakfastMuxedPadsIoc4 = 26, /**<  */
  kTopEnglishbreakfastMuxedPadsIoc5 = 27, /**<  */
  kTopEnglishbreakfastMuxedPadsIoc6 = 28, /**<  */
  kTopEnglishbreakfastMuxedPadsIoc7 = 29, /**<  */
  kTopEnglishbreakfastMuxedPadsIoc8 = 30, /**<  */
  kTopEnglishbreakfastMuxedPadsIoc9 = 31, /**<  */
  kTopEnglishbreakfastMuxedPadsIoc10 = 32, /**<  */
  kTopEnglishbreakfastMuxedPadsIoc11 = 33, /**<  */
  kTopEnglishbreakfastMuxedPadsIoc12 = 34, /**<  */
  kTopEnglishbreakfastMuxedPadsIor0 = 35, /**<  */
  kTopEnglishbreakfastMuxedPadsIor1 = 36, /**<  */
  kTopEnglishbreakfastMuxedPadsIor2 = 37, /**<  */
  kTopEnglishbreakfastMuxedPadsIor3 = 38, /**<  */
  kTopEnglishbreakfastMuxedPadsIor4 = 39, /**<  */
  kTopEnglishbreakfastMuxedPadsIor5 = 40, /**<  */
  kTopEnglishbreakfastMuxedPadsIor6 = 41, /**<  */
  kTopEnglishbreakfastMuxedPadsIor7 = 42, /**<  */
  kTopEnglishbreakfastMuxedPadsIor10 = 43, /**<  */
  kTopEnglishbreakfastMuxedPadsIor11 = 44, /**<  */
  kTopEnglishbreakfastMuxedPadsIor12 = 45, /**<  */
  kTopEnglishbreakfastMuxedPadsIor13 = 46, /**<  */
  kTopEnglishbreakfastMuxedPadsLast = 46, /**< \internal Last valid muxed pad */
} top_englishbreakfast_muxed_pads_t;

/**
 * Power Manager Wakeup Signals
 */
typedef enum top_englishbreakfast_power_manager_wake_ups {
  kTopEnglishbreakfastPowerManagerWakeUpsPinmuxAonPinWkupReq = 0, /**<  */
  kTopEnglishbreakfastPowerManagerWakeUpsPinmuxAonUsbWkupReq = 1, /**<  */
  kTopEnglishbreakfastPowerManagerWakeUpsAonTimerAonWkupReq = 2, /**<  */
  kTopEnglishbreakfastPowerManagerWakeUpsLast = 2, /**< \internal Last valid pwrmgr wakeup signal */
} top_englishbreakfast_power_manager_wake_ups_t;

/**
 * Reset Manager Software Controlled Resets
 */
typedef enum top_englishbreakfast_reset_manager_sw_resets {
  kTopEnglishbreakfastResetManagerSwResetsSpiDevice = 0, /**<  */
  kTopEnglishbreakfastResetManagerSwResetsSpiHost0 = 1, /**<  */
  kTopEnglishbreakfastResetManagerSwResetsUsb = 2, /**<  */
  kTopEnglishbreakfastResetManagerSwResetsLast = 2, /**< \internal Last valid rstmgr software reset request */
} top_englishbreakfast_reset_manager_sw_resets_t;

/**
 * Power Manager Reset Request Signals
 */
typedef enum top_englishbreakfast_power_manager_reset_requests {
  kTopEnglishbreakfastPowerManagerResetRequestsAonTimerAonAonTimerRstReq = 0, /**<  */
  kTopEnglishbreakfastPowerManagerResetRequestsLast = 0, /**< \internal Last valid pwrmgr reset_request signal */
} top_englishbreakfast_power_manager_reset_requests_t;

/**
 * Clock Manager Software-Controlled ("Gated") Clocks.
 *
 * The Software has full control over these clocks.
 */
typedef enum top_englishbreakfast_gateable_clocks {
  kTopEnglishbreakfastGateableClocksIoDiv4Peri = 0, /**< Clock clk_io_div4_peri in group peri */
  kTopEnglishbreakfastGateableClocksIoDiv2Peri = 1, /**< Clock clk_io_div2_peri in group peri */
  kTopEnglishbreakfastGateableClocksIoPeri = 2, /**< Clock clk_io_peri in group peri */
  kTopEnglishbreakfastGateableClocksUsbPeri = 3, /**< Clock clk_usb_peri in group peri */
  kTopEnglishbreakfastGateableClocksLast = 3, /**< \internal Last Valid Gateable Clock */
} top_englishbreakfast_gateable_clocks_t;

/**
 * Clock Manager Software-Hinted Clocks.
 *
 * The Software has partial control over these clocks. It can ask them to stop,
 * but the clock manager is in control of whether the clock actually is stopped.
 */
typedef enum top_englishbreakfast_hintable_clocks {
  kTopEnglishbreakfastHintableClocksMainAes = 0, /**< Clock clk_main_aes in group trans */
  kTopEnglishbreakfastHintableClocksLast = 0, /**< \internal Last Valid Hintable Clock */
} top_englishbreakfast_hintable_clocks_t;

/**
 * Clock IDs for peripherals to map against properties.
 */
typedef enum top_englishbreakfast_clock_src {
  kTopEnglishbreakfastClockSrcUnknown = 0, /**< ID representing unknown clock */
  kTopEnglishbreakfastClockSrcMain = 1, /**< Clock main */
  kTopEnglishbreakfastClockSrcIo = 2, /**< Clock io */
  kTopEnglishbreakfastClockSrcUsb = 3, /**< Clock usb */
  kTopEnglishbreakfastClockSrcAon = 4, /**< Clock aon */
  kTopEnglishbreakfastClockSrcIoDiv2 = 5, /**< Clock io_div2 */
  kTopEnglishbreakfastClockSrcIoDiv4 = 6, /**< Clock io_div4 */
  kTopEnglishbreakfastClockSrcCount = 7, /**< Number of clock IDs */
} top_englishbreakfast_clock_src_t;

/**
 * MMIO Region
 *
 * MMIO region excludes any memory that is separate from the module
 * configuration space, i.e. ROM, main SRAM, and flash are excluded but
 * retention SRAM, spi_device memory, or usbdev memory are included.
 */
#define TOP_ENGLISHBREAKFAST_MMIO_BASE_ADDR 0x40000000u
#define TOP_ENGLISHBREAKFAST_MMIO_SIZE_BYTES 0x10000000u

// Header Extern Guard
#ifdef __cplusplus
}  // extern "C"
#endif

#endif  // OPENTITAN_HW_TOP_ENGLISHBREAKFAST_SW_AUTOGEN_TOP_ENGLISHBREAKFAST_H_
