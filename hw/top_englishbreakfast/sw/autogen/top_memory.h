// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
// util/topgen.py -t hw/top_englishbreakfast/data/top_englishbreakfast.hjson
//                -o hw/top_englishbreakfast/

#ifndef OPENTITAN_HW_TOP_ENGLISHBREAKFAST_SW_AUTOGEN_TOP_MEMORY_H_
#define OPENTITAN_HW_TOP_ENGLISHBREAKFAST_SW_AUTOGEN_TOP_MEMORY_H_

/**
 * @file
 * @brief Assembler-only Top-Specific Definitions.
 *
 * This file contains preprocessor definitions for use within assembly code.
 *
 * These are not shared with C/C++ code because these are only allowed to be
 * preprocessor definitions, no data or type declarations are allowed. The
 * assembler is also stricter about literals (not allowing suffixes for
 * signed/unsigned which are sensible to use for unsigned values in C/C++).
 */

// Include guard for assembler
#ifdef __ASSEMBLER__

/**
 * Memory base for mem memory on flash_ctrl in top englishbreakfast.
 */
#define TOP_FLASH_CTRL_MEM_BASE_ADDR 0x20000000

/**
 * Memory size for mem memory on flash_ctrl in top englishbreakfast.
 */
#define TOP_FLASH_CTRL_MEM_SIZE_BYTES 0x10000

/**
 * Memory base for ram memory on sram_ctrl_main in top englishbreakfast.
 */
#define TOP_SRAM_CTRL_MAIN_RAM_BASE_ADDR 0x10000000

/**
 * Memory size for ram memory on sram_ctrl_main in top englishbreakfast.
 */
#define TOP_SRAM_CTRL_MAIN_RAM_SIZE_BYTES 0x20000

/**
 * Memory base for rom memory on rom_ctrl in top englishbreakfast.
 */
#define TOP_ROM_CTRL_ROM_BASE_ADDR 0x8000

/**
 * Memory size for rom memory on rom_ctrl in top englishbreakfast.
 */
#define TOP_ROM_CTRL_ROM_SIZE_BYTES 0x8000


/**
 * Peripheral base address for uart0 in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_UART0_BASE_ADDR 0x40000000

/**
 * Peripheral size for uart0 in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_UART0_BASE_ADDR and
 * `TOP_UART0_BASE_ADDR + TOP_UART0_SIZE_BYTES`.
 */
#define TOP_UART0_SIZE_BYTES 0x40
/**
 * Peripheral base address for uart1 in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_UART1_BASE_ADDR 0x40010000

/**
 * Peripheral size for uart1 in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_UART1_BASE_ADDR and
 * `TOP_UART1_BASE_ADDR + TOP_UART1_SIZE_BYTES`.
 */
#define TOP_UART1_SIZE_BYTES 0x40
/**
 * Peripheral base address for gpio in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_GPIO_BASE_ADDR 0x40040000

/**
 * Peripheral size for gpio in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_GPIO_BASE_ADDR and
 * `TOP_GPIO_BASE_ADDR + TOP_GPIO_SIZE_BYTES`.
 */
#define TOP_GPIO_SIZE_BYTES 0x80
/**
 * Peripheral base address for spi_device in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_SPI_DEVICE_BASE_ADDR 0x40050000

/**
 * Peripheral size for spi_device in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_SPI_DEVICE_BASE_ADDR and
 * `TOP_SPI_DEVICE_BASE_ADDR + TOP_SPI_DEVICE_SIZE_BYTES`.
 */
#define TOP_SPI_DEVICE_SIZE_BYTES 0x2000
/**
 * Peripheral base address for spi_host0 in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_SPI_HOST0_BASE_ADDR 0x40060000

/**
 * Peripheral size for spi_host0 in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_SPI_HOST0_BASE_ADDR and
 * `TOP_SPI_HOST0_BASE_ADDR + TOP_SPI_HOST0_SIZE_BYTES`.
 */
#define TOP_SPI_HOST0_SIZE_BYTES 0x40
/**
 * Peripheral base address for rv_timer in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_RV_TIMER_BASE_ADDR 0x40100000

/**
 * Peripheral size for rv_timer in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_RV_TIMER_BASE_ADDR and
 * `TOP_RV_TIMER_BASE_ADDR + TOP_RV_TIMER_SIZE_BYTES`.
 */
#define TOP_RV_TIMER_SIZE_BYTES 0x200
/**
 * Peripheral base address for usbdev in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_USBDEV_BASE_ADDR 0x40320000

/**
 * Peripheral size for usbdev in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_USBDEV_BASE_ADDR and
 * `TOP_USBDEV_BASE_ADDR + TOP_USBDEV_SIZE_BYTES`.
 */
#define TOP_USBDEV_SIZE_BYTES 0x1000
/**
 * Peripheral base address for pwrmgr in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_PWRMGR_BASE_ADDR 0x40400000

/**
 * Peripheral size for pwrmgr in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_PWRMGR_BASE_ADDR and
 * `TOP_PWRMGR_BASE_ADDR + TOP_PWRMGR_SIZE_BYTES`.
 */
#define TOP_PWRMGR_SIZE_BYTES 0x80
/**
 * Peripheral base address for rstmgr in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_RSTMGR_BASE_ADDR 0x40410000

/**
 * Peripheral size for rstmgr in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_RSTMGR_BASE_ADDR and
 * `TOP_RSTMGR_BASE_ADDR + TOP_RSTMGR_SIZE_BYTES`.
 */
#define TOP_RSTMGR_SIZE_BYTES 0x80
/**
 * Peripheral base address for clkmgr in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_CLKMGR_BASE_ADDR 0x40420000

/**
 * Peripheral size for clkmgr in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_CLKMGR_BASE_ADDR and
 * `TOP_CLKMGR_BASE_ADDR + TOP_CLKMGR_SIZE_BYTES`.
 */
#define TOP_CLKMGR_SIZE_BYTES 0x80
/**
 * Peripheral base address for pinmux in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_PINMUX_BASE_ADDR 0x40460000

/**
 * Peripheral size for pinmux in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_PINMUX_BASE_ADDR and
 * `TOP_PINMUX_BASE_ADDR + TOP_PINMUX_SIZE_BYTES`.
 */
#define TOP_PINMUX_SIZE_BYTES 0x1000
/**
 * Peripheral base address for aon_timer in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_AON_TIMER_BASE_ADDR 0x40470000

/**
 * Peripheral size for aon_timer in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_AON_TIMER_BASE_ADDR and
 * `TOP_AON_TIMER_BASE_ADDR + TOP_AON_TIMER_SIZE_BYTES`.
 */
#define TOP_AON_TIMER_SIZE_BYTES 0x40
/**
 * Peripheral base address for ast in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_AST_BASE_ADDR 0x40480000

/**
 * Peripheral size for ast in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_AST_BASE_ADDR and
 * `TOP_AST_BASE_ADDR + TOP_AST_SIZE_BYTES`.
 */
#define TOP_AST_SIZE_BYTES 0x400
/**
 * Peripheral base address for core device on flash_ctrl in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_FLASH_CTRL_CORE_BASE_ADDR 0x41000000

/**
 * Peripheral size for core device on flash_ctrl in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_FLASH_CTRL_CORE_BASE_ADDR and
 * `TOP_FLASH_CTRL_CORE_BASE_ADDR + TOP_FLASH_CTRL_CORE_SIZE_BYTES`.
 */
#define TOP_FLASH_CTRL_CORE_SIZE_BYTES 0x200
/**
 * Peripheral base address for prim device on flash_ctrl in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_FLASH_CTRL_PRIM_BASE_ADDR 0x41008000

/**
 * Peripheral size for prim device on flash_ctrl in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_FLASH_CTRL_PRIM_BASE_ADDR and
 * `TOP_FLASH_CTRL_PRIM_BASE_ADDR + TOP_FLASH_CTRL_PRIM_SIZE_BYTES`.
 */
#define TOP_FLASH_CTRL_PRIM_SIZE_BYTES 0x80
/**
 * Peripheral base address for rv_plic in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_RV_PLIC_BASE_ADDR 0x48000000

/**
 * Peripheral size for rv_plic in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_RV_PLIC_BASE_ADDR and
 * `TOP_RV_PLIC_BASE_ADDR + TOP_RV_PLIC_SIZE_BYTES`.
 */
#define TOP_RV_PLIC_SIZE_BYTES 0x8000000
/**
 * Peripheral base address for aes in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_AES_BASE_ADDR 0x41100000

/**
 * Peripheral size for aes in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_AES_BASE_ADDR and
 * `TOP_AES_BASE_ADDR + TOP_AES_SIZE_BYTES`.
 */
#define TOP_AES_SIZE_BYTES 0x100
/**
 * Peripheral base address for regs device on sram_ctrl_main in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_SRAM_CTRL_MAIN_REGS_BASE_ADDR 0x411C0000

/**
 * Peripheral size for regs device on sram_ctrl_main in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_SRAM_CTRL_MAIN_REGS_BASE_ADDR and
 * `TOP_SRAM_CTRL_MAIN_REGS_BASE_ADDR + TOP_SRAM_CTRL_MAIN_REGS_SIZE_BYTES`.
 */
#define TOP_SRAM_CTRL_MAIN_REGS_SIZE_BYTES 0x40
/**
 * Peripheral base address for regs device on rom_ctrl in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ROM_CTRL_REGS_BASE_ADDR 0x411E0000

/**
 * Peripheral size for regs device on rom_ctrl in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ROM_CTRL_REGS_BASE_ADDR and
 * `TOP_ROM_CTRL_REGS_BASE_ADDR + TOP_ROM_CTRL_REGS_SIZE_BYTES`.
 */
#define TOP_ROM_CTRL_REGS_SIZE_BYTES 0x80
/**
 * Peripheral base address for cfg device on rv_core_ibex in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_RV_CORE_IBEX_CFG_BASE_ADDR 0x411F0000

/**
 * Peripheral size for cfg device on rv_core_ibex in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_RV_CORE_IBEX_CFG_BASE_ADDR and
 * `TOP_RV_CORE_IBEX_CFG_BASE_ADDR + TOP_RV_CORE_IBEX_CFG_SIZE_BYTES`.
 */
#define TOP_RV_CORE_IBEX_CFG_SIZE_BYTES 0x100

/**
 * MMIO Region
 *
 * MMIO region excludes any memory that is separate from the module
 * configuration space, i.e. ROM, main SRAM, and flash are excluded but
 * retention SRAM, spi_device memory, or usbdev memory are included.
 */
#define TOP_MMIO_BASE_ADDR 0x40000000
#define TOP_MMIO_SIZE_BYTES 0x10000000

#define TOP_NVM_BASE_ADDR TOP_FLASH_CTRL_MEM_BASE_ADDR
#define TOP_NVM_SIZE_BYTES TOP_FLASH_CTRL_MEM_SIZE_BYTES

#endif  // __ASSEMBLER__

#endif  // OPENTITAN_HW_TOP_ENGLISHBREAKFAST_SW_AUTOGEN_TOP_MEMORY_H_
