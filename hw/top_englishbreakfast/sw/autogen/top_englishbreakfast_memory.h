// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_TOP_ENGLISHBREAKFAST_SW_AUTOGEN_TOP_ENGLISHBREAKFAST_MEMORY_H_
#define OPENTITAN_HW_TOP_ENGLISHBREAKFAST_SW_AUTOGEN_TOP_ENGLISHBREAKFAST_MEMORY_H_

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
 * Memory base for flash_ctrl_eflash in top englishbreakfast.
 */
#define TOP_ENGLISHBREAKFAST_EFLASH_BASE_ADDR 0x20000000

/**
 * Memory size for flash_ctrl_eflash in top englishbreakfast.
 */
#define TOP_ENGLISHBREAKFAST_EFLASH_SIZE_BYTES 0x10000

/**
 * Memory base for sram_ctrl_main_ram_main in top englishbreakfast.
 */
#define TOP_ENGLISHBREAKFAST_RAM_MAIN_BASE_ADDR 0x10000000

/**
 * Memory size for sram_ctrl_main_ram_main in top englishbreakfast.
 */
#define TOP_ENGLISHBREAKFAST_RAM_MAIN_SIZE_BYTES 0x20000

/**
 * Memory base for rom_ctrl_rom in top englishbreakfast.
 */
#define TOP_ENGLISHBREAKFAST_ROM_BASE_ADDR 0x00008000

/**
 * Memory size for rom_ctrl_rom in top englishbreakfast.
 */
#define TOP_ENGLISHBREAKFAST_ROM_SIZE_BYTES 0x8000



/**
 * Peripheral base address for uart0 in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_UART0_BASE_ADDR 0x40000000

/**
 * Peripheral size for uart0 in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_UART0_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_UART0_BASE_ADDR + TOP_ENGLISHBREAKFAST_UART0_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_UART0_SIZE_BYTES 0x40
/**
 * Peripheral base address for uart1 in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_UART1_BASE_ADDR 0x40010000

/**
 * Peripheral size for uart1 in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_UART1_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_UART1_BASE_ADDR + TOP_ENGLISHBREAKFAST_UART1_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_UART1_SIZE_BYTES 0x40
/**
 * Peripheral base address for gpio in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_GPIO_BASE_ADDR 0x40040000

/**
 * Peripheral size for gpio in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_GPIO_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_GPIO_BASE_ADDR + TOP_ENGLISHBREAKFAST_GPIO_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_GPIO_SIZE_BYTES 0x40
/**
 * Peripheral base address for spi_device in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_SPI_DEVICE_BASE_ADDR 0x40050000

/**
 * Peripheral size for spi_device in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_SPI_DEVICE_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_SPI_DEVICE_BASE_ADDR + TOP_ENGLISHBREAKFAST_SPI_DEVICE_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_SPI_DEVICE_SIZE_BYTES 0x2000
/**
 * Peripheral base address for spi_host0 in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_SPI_HOST0_BASE_ADDR 0x40060000

/**
 * Peripheral size for spi_host0 in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_SPI_HOST0_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_SPI_HOST0_BASE_ADDR + TOP_ENGLISHBREAKFAST_SPI_HOST0_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_SPI_HOST0_SIZE_BYTES 0x40
/**
 * Peripheral base address for rv_timer in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_RV_TIMER_BASE_ADDR 0x40100000

/**
 * Peripheral size for rv_timer in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_RV_TIMER_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_RV_TIMER_BASE_ADDR + TOP_ENGLISHBREAKFAST_RV_TIMER_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_RV_TIMER_SIZE_BYTES 0x200
/**
 * Peripheral base address for usbdev in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_USBDEV_BASE_ADDR 0x40320000

/**
 * Peripheral size for usbdev in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_USBDEV_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_USBDEV_BASE_ADDR + TOP_ENGLISHBREAKFAST_USBDEV_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_USBDEV_SIZE_BYTES 0x1000
/**
 * Peripheral base address for pwrmgr_aon in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_PWRMGR_AON_BASE_ADDR 0x40400000

/**
 * Peripheral size for pwrmgr_aon in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_PWRMGR_AON_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_PWRMGR_AON_BASE_ADDR + TOP_ENGLISHBREAKFAST_PWRMGR_AON_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_PWRMGR_AON_SIZE_BYTES 0x80
/**
 * Peripheral base address for rstmgr_aon in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_RSTMGR_AON_BASE_ADDR 0x40410000

/**
 * Peripheral size for rstmgr_aon in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_RSTMGR_AON_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_RSTMGR_AON_BASE_ADDR + TOP_ENGLISHBREAKFAST_RSTMGR_AON_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_RSTMGR_AON_SIZE_BYTES 0x80
/**
 * Peripheral base address for clkmgr_aon in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_CLKMGR_AON_BASE_ADDR 0x40420000

/**
 * Peripheral size for clkmgr_aon in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_CLKMGR_AON_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_CLKMGR_AON_BASE_ADDR + TOP_ENGLISHBREAKFAST_CLKMGR_AON_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_CLKMGR_AON_SIZE_BYTES 0x80
/**
 * Peripheral base address for pinmux_aon in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_PINMUX_AON_BASE_ADDR 0x40460000

/**
 * Peripheral size for pinmux_aon in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_PINMUX_AON_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_PINMUX_AON_BASE_ADDR + TOP_ENGLISHBREAKFAST_PINMUX_AON_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_PINMUX_AON_SIZE_BYTES 0x1000
/**
 * Peripheral base address for aon_timer_aon in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_AON_TIMER_AON_BASE_ADDR 0x40470000

/**
 * Peripheral size for aon_timer_aon in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_AON_TIMER_AON_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_AON_TIMER_AON_BASE_ADDR + TOP_ENGLISHBREAKFAST_AON_TIMER_AON_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_AON_TIMER_AON_SIZE_BYTES 0x40
/**
 * Peripheral base address for ast in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_AST_BASE_ADDR 0x40480000

/**
 * Peripheral size for ast in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_AST_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_AST_BASE_ADDR + TOP_ENGLISHBREAKFAST_AST_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_AST_SIZE_BYTES 0x400
/**
 * Peripheral base address for core device on flash_ctrl in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_FLASH_CTRL_CORE_BASE_ADDR 0x41000000

/**
 * Peripheral size for core device on flash_ctrl in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_FLASH_CTRL_CORE_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_FLASH_CTRL_CORE_BASE_ADDR + TOP_ENGLISHBREAKFAST_FLASH_CTRL_CORE_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_FLASH_CTRL_CORE_SIZE_BYTES 0x200
/**
 * Peripheral base address for prim device on flash_ctrl in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_FLASH_CTRL_PRIM_BASE_ADDR 0x41008000

/**
 * Peripheral size for prim device on flash_ctrl in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_FLASH_CTRL_PRIM_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_FLASH_CTRL_PRIM_BASE_ADDR + TOP_ENGLISHBREAKFAST_FLASH_CTRL_PRIM_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_FLASH_CTRL_PRIM_SIZE_BYTES 0x80
/**
 * Peripheral base address for mem device on flash_ctrl in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_FLASH_CTRL_MEM_BASE_ADDR 0x20000000

/**
 * Peripheral size for mem device on flash_ctrl in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_FLASH_CTRL_MEM_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_FLASH_CTRL_MEM_BASE_ADDR + TOP_ENGLISHBREAKFAST_FLASH_CTRL_MEM_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_FLASH_CTRL_MEM_SIZE_BYTES 0x10000
/**
 * Peripheral base address for rv_plic in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_RV_PLIC_BASE_ADDR 0x48000000

/**
 * Peripheral size for rv_plic in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_RV_PLIC_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_RV_PLIC_BASE_ADDR + TOP_ENGLISHBREAKFAST_RV_PLIC_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_RV_PLIC_SIZE_BYTES 0x8000000
/**
 * Peripheral base address for aes in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_AES_BASE_ADDR 0x41100000

/**
 * Peripheral size for aes in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_AES_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_AES_BASE_ADDR + TOP_ENGLISHBREAKFAST_AES_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_AES_SIZE_BYTES 0x100
/**
 * Peripheral base address for regs device on sram_ctrl_main in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_SRAM_CTRL_MAIN_REGS_BASE_ADDR 0x411C0000

/**
 * Peripheral size for regs device on sram_ctrl_main in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_SRAM_CTRL_MAIN_REGS_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_SRAM_CTRL_MAIN_REGS_BASE_ADDR + TOP_ENGLISHBREAKFAST_SRAM_CTRL_MAIN_REGS_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_SRAM_CTRL_MAIN_REGS_SIZE_BYTES 0x40
/**
 * Peripheral base address for ram device on sram_ctrl_main in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_SRAM_CTRL_MAIN_RAM_BASE_ADDR 0x10000000

/**
 * Peripheral size for ram device on sram_ctrl_main in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_SRAM_CTRL_MAIN_RAM_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_SRAM_CTRL_MAIN_RAM_BASE_ADDR + TOP_ENGLISHBREAKFAST_SRAM_CTRL_MAIN_RAM_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_SRAM_CTRL_MAIN_RAM_SIZE_BYTES 0x20000
/**
 * Peripheral base address for regs device on rom_ctrl in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_ROM_CTRL_REGS_BASE_ADDR 0x411E0000

/**
 * Peripheral size for regs device on rom_ctrl in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_ROM_CTRL_REGS_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_ROM_CTRL_REGS_BASE_ADDR + TOP_ENGLISHBREAKFAST_ROM_CTRL_REGS_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_ROM_CTRL_REGS_SIZE_BYTES 0x80
/**
 * Peripheral base address for rom device on rom_ctrl in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_ROM_CTRL_ROM_BASE_ADDR 0x8000

/**
 * Peripheral size for rom device on rom_ctrl in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_ROM_CTRL_ROM_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_ROM_CTRL_ROM_BASE_ADDR + TOP_ENGLISHBREAKFAST_ROM_CTRL_ROM_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_ROM_CTRL_ROM_SIZE_BYTES 0x8000
/**
 * Peripheral base address for cfg device on rv_core_ibex in top englishbreakfast.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_ENGLISHBREAKFAST_RV_CORE_IBEX_CFG_BASE_ADDR 0x411F0000

/**
 * Peripheral size for cfg device on rv_core_ibex in top englishbreakfast.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_ENGLISHBREAKFAST_RV_CORE_IBEX_CFG_BASE_ADDR and
 * `TOP_ENGLISHBREAKFAST_RV_CORE_IBEX_CFG_BASE_ADDR + TOP_ENGLISHBREAKFAST_RV_CORE_IBEX_CFG_SIZE_BYTES`.
 */
#define TOP_ENGLISHBREAKFAST_RV_CORE_IBEX_CFG_SIZE_BYTES 0x100

/**
 * MMIO Region
 *
 * MMIO region excludes any memory that is separate from the module
 * configuration space, i.e. ROM, main SRAM, and flash are excluded but
 * retention SRAM, spi_device memory, or usbdev memory are included.
 */
#define TOP_ENGLISHBREAKFAST_MMIO_BASE_ADDR 0x40000000
#define TOP_ENGLISHBREAKFAST_MMIO_SIZE_BYTES 0x10000000

#endif  // __ASSEMBLER__

#endif  // OPENTITAN_HW_TOP_ENGLISHBREAKFAST_SW_AUTOGEN_TOP_ENGLISHBREAKFAST_MEMORY_H_
