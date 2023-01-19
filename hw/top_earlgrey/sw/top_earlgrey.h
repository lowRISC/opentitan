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
 * Peripheral base address for gpio in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_GPIO_BASE_ADDR 0xB0040000u

/**
 * Peripheral size for gpio in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_GPIO_BASE_ADDR and
 * `TOP_EARLGREY_GPIO_BASE_ADDR + TOP_EARLGREY_GPIO_SIZE_BYTES`.
 */
#define TOP_EARLGREY_GPIO_SIZE_BYTES 0x40u

/**
 * Peripheral base address for pattgen in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_PATTGEN_BASE_ADDR 0xB00E0000u

/**
 * Peripheral size for pattgen in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_PATTGEN_BASE_ADDR and
 * `TOP_EARLGREY_PATTGEN_BASE_ADDR + TOP_EARLGREY_PATTGEN_SIZE_BYTES`.
 */
#define TOP_EARLGREY_PATTGEN_SIZE_BYTES 0x40u

/**
 * Peripheral base address for rv_timer in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_RV_TIMER_BASE_ADDR 0xB0100000u

/**
 * Peripheral size for rv_timer in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_RV_TIMER_BASE_ADDR and
 * `TOP_EARLGREY_RV_TIMER_BASE_ADDR + TOP_EARLGREY_RV_TIMER_SIZE_BYTES`.
 */
#define TOP_EARLGREY_RV_TIMER_SIZE_BYTES 0x200u

/**
 * Peripheral base address for core device on otp_ctrl in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR 0xB0130000u

/**
 * Peripheral size for core device on otp_ctrl in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR and
 * `TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR + TOP_EARLGREY_OTP_CTRL_CORE_SIZE_BYTES`.
 */
#define TOP_EARLGREY_OTP_CTRL_CORE_SIZE_BYTES 0x2000u

/**
 * Peripheral base address for prim device on otp_ctrl in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_OTP_CTRL_PRIM_BASE_ADDR 0xB0132000u

/**
 * Peripheral size for prim device on otp_ctrl in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_OTP_CTRL_PRIM_BASE_ADDR and
 * `TOP_EARLGREY_OTP_CTRL_PRIM_BASE_ADDR + TOP_EARLGREY_OTP_CTRL_PRIM_SIZE_BYTES`.
 */
#define TOP_EARLGREY_OTP_CTRL_PRIM_SIZE_BYTES 0x20u

/**
 * Peripheral base address for lc_ctrl in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_LC_CTRL_BASE_ADDR 0xB0140000u

/**
 * Peripheral size for lc_ctrl in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_LC_CTRL_BASE_ADDR and
 * `TOP_EARLGREY_LC_CTRL_BASE_ADDR + TOP_EARLGREY_LC_CTRL_SIZE_BYTES`.
 */
#define TOP_EARLGREY_LC_CTRL_SIZE_BYTES 0x100u

/**
 * Peripheral base address for alert_handler in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR 0xB0150000u

/**
 * Peripheral size for alert_handler in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR and
 * `TOP_EARLGREY_ALERT_HANDLER_BASE_ADDR + TOP_EARLGREY_ALERT_HANDLER_SIZE_BYTES`.
 */
#define TOP_EARLGREY_ALERT_HANDLER_SIZE_BYTES 0x800u

/**
 * Peripheral base address for spi_host0 in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_SPI_HOST0_BASE_ADDR 0xC0300000u

/**
 * Peripheral size for spi_host0 in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_SPI_HOST0_BASE_ADDR and
 * `TOP_EARLGREY_SPI_HOST0_BASE_ADDR + TOP_EARLGREY_SPI_HOST0_SIZE_BYTES`.
 */
#define TOP_EARLGREY_SPI_HOST0_SIZE_BYTES 0x40u

/**
 * Peripheral base address for spi_host1 in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_SPI_HOST1_BASE_ADDR 0xC0310000u

/**
 * Peripheral size for spi_host1 in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_SPI_HOST1_BASE_ADDR and
 * `TOP_EARLGREY_SPI_HOST1_BASE_ADDR + TOP_EARLGREY_SPI_HOST1_SIZE_BYTES`.
 */
#define TOP_EARLGREY_SPI_HOST1_SIZE_BYTES 0x40u

/**
 * Peripheral base address for spi_device in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_SPI_DEVICE_BASE_ADDR 0xB0050000u

/**
 * Peripheral size for spi_device in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_SPI_DEVICE_BASE_ADDR and
 * `TOP_EARLGREY_SPI_DEVICE_BASE_ADDR + TOP_EARLGREY_SPI_DEVICE_SIZE_BYTES`.
 */
#define TOP_EARLGREY_SPI_DEVICE_SIZE_BYTES 0x2000u

/**
 * Peripheral base address for pwrmgr_aon in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_PWRMGR_AON_BASE_ADDR 0xB0400000u

/**
 * Peripheral size for pwrmgr_aon in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_PWRMGR_AON_BASE_ADDR and
 * `TOP_EARLGREY_PWRMGR_AON_BASE_ADDR + TOP_EARLGREY_PWRMGR_AON_SIZE_BYTES`.
 */
#define TOP_EARLGREY_PWRMGR_AON_SIZE_BYTES 0x80u

/**
 * Peripheral base address for rstmgr_aon in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_RSTMGR_AON_BASE_ADDR 0xB0410000u

/**
 * Peripheral size for rstmgr_aon in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_RSTMGR_AON_BASE_ADDR and
 * `TOP_EARLGREY_RSTMGR_AON_BASE_ADDR + TOP_EARLGREY_RSTMGR_AON_SIZE_BYTES`.
 */
#define TOP_EARLGREY_RSTMGR_AON_SIZE_BYTES 0x80u

/**
 * Peripheral base address for clkmgr_aon in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_CLKMGR_AON_BASE_ADDR 0xB0420000u

/**
 * Peripheral size for clkmgr_aon in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_CLKMGR_AON_BASE_ADDR and
 * `TOP_EARLGREY_CLKMGR_AON_BASE_ADDR + TOP_EARLGREY_CLKMGR_AON_SIZE_BYTES`.
 */
#define TOP_EARLGREY_CLKMGR_AON_SIZE_BYTES 0x80u

/**
 * Peripheral base address for sysrst_ctrl_aon in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_SYSRST_CTRL_AON_BASE_ADDR 0xB0430000u

/**
 * Peripheral size for sysrst_ctrl_aon in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_SYSRST_CTRL_AON_BASE_ADDR and
 * `TOP_EARLGREY_SYSRST_CTRL_AON_BASE_ADDR + TOP_EARLGREY_SYSRST_CTRL_AON_SIZE_BYTES`.
 */
#define TOP_EARLGREY_SYSRST_CTRL_AON_SIZE_BYTES 0x100u

/**
 * Peripheral base address for pinmux_aon in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_PINMUX_AON_BASE_ADDR 0xB0460000u

/**
 * Peripheral size for pinmux_aon in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_PINMUX_AON_BASE_ADDR and
 * `TOP_EARLGREY_PINMUX_AON_BASE_ADDR + TOP_EARLGREY_PINMUX_AON_SIZE_BYTES`.
 */
#define TOP_EARLGREY_PINMUX_AON_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for aon_timer_aon in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR 0xB0470000u

/**
 * Peripheral size for aon_timer_aon in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR and
 * `TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR + TOP_EARLGREY_AON_TIMER_AON_SIZE_BYTES`.
 */
#define TOP_EARLGREY_AON_TIMER_AON_SIZE_BYTES 0x40u

/**
 * Peripheral base address for ast in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_AST_BASE_ADDR 0xB0480000u

/**
 * Peripheral size for ast in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_AST_BASE_ADDR and
 * `TOP_EARLGREY_AST_BASE_ADDR + TOP_EARLGREY_AST_SIZE_BYTES`.
 */
#define TOP_EARLGREY_AST_SIZE_BYTES 0x400u

/**
 * Peripheral base address for regs device on sram_ctrl_ret_aon in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_BASE_ADDR 0xB0500000u

/**
 * Peripheral size for regs device on sram_ctrl_ret_aon in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_BASE_ADDR and
 * `TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_BASE_ADDR + TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_SIZE_BYTES`.
 */
#define TOP_EARLGREY_SRAM_CTRL_RET_AON_REGS_SIZE_BYTES 0x20u

/**
 * Peripheral base address for ram device on sram_ctrl_ret_aon in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR 0xB0600000u

/**
 * Peripheral size for ram device on sram_ctrl_ret_aon in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR and
 * `TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_BASE_ADDR + TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_SIZE_BYTES`.
 */
#define TOP_EARLGREY_SRAM_CTRL_RET_AON_RAM_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for core device on flash_ctrl in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR 0xC1000000u

/**
 * Peripheral size for core device on flash_ctrl in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR and
 * `TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR + TOP_EARLGREY_FLASH_CTRL_CORE_SIZE_BYTES`.
 */
#define TOP_EARLGREY_FLASH_CTRL_CORE_SIZE_BYTES 0x200u

/**
 * Peripheral base address for prim device on flash_ctrl in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_FLASH_CTRL_PRIM_BASE_ADDR 0xC1008000u

/**
 * Peripheral size for prim device on flash_ctrl in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_FLASH_CTRL_PRIM_BASE_ADDR and
 * `TOP_EARLGREY_FLASH_CTRL_PRIM_BASE_ADDR + TOP_EARLGREY_FLASH_CTRL_PRIM_SIZE_BYTES`.
 */
#define TOP_EARLGREY_FLASH_CTRL_PRIM_SIZE_BYTES 0x80u

/**
 * Peripheral base address for mem device on flash_ctrl in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR 0xF0000000u

/**
 * Peripheral size for mem device on flash_ctrl in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR and
 * `TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR + TOP_EARLGREY_FLASH_CTRL_MEM_SIZE_BYTES`.
 */
#define TOP_EARLGREY_FLASH_CTRL_MEM_SIZE_BYTES 0x100000u

/**
 * Peripheral base address for regs device on rv_dm in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_RV_DM_REGS_BASE_ADDR 0xC1200000u

/**
 * Peripheral size for regs device on rv_dm in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_RV_DM_REGS_BASE_ADDR and
 * `TOP_EARLGREY_RV_DM_REGS_BASE_ADDR + TOP_EARLGREY_RV_DM_REGS_SIZE_BYTES`.
 */
#define TOP_EARLGREY_RV_DM_REGS_SIZE_BYTES 0x4u

/**
 * Peripheral base address for mem device on rv_dm in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_RV_DM_MEM_BASE_ADDR 0x0u

/**
 * Peripheral size for mem device on rv_dm in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_RV_DM_MEM_BASE_ADDR and
 * `TOP_EARLGREY_RV_DM_MEM_BASE_ADDR + TOP_EARLGREY_RV_DM_MEM_SIZE_BYTES`.
 */
#define TOP_EARLGREY_RV_DM_MEM_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for tlul2axi in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_TLUL2AXI_BASE_ADDR 0x10000u

/**
 * Peripheral size for tlul2axi in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_TLUL2AXI_BASE_ADDR and
 * `TOP_EARLGREY_TLUL2AXI_BASE_ADDR + TOP_EARLGREY_TLUL2AXI_SIZE_BYTES`.
 */
#define TOP_EARLGREY_TLUL2AXI_SIZE_BYTES 0x10u

/**
 * Peripheral base address for rv_plic in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_RV_PLIC_BASE_ADDR 0xC8000000u

/**
 * Peripheral size for rv_plic in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_RV_PLIC_BASE_ADDR and
 * `TOP_EARLGREY_RV_PLIC_BASE_ADDR + TOP_EARLGREY_RV_PLIC_SIZE_BYTES`.
 */
#define TOP_EARLGREY_RV_PLIC_SIZE_BYTES 0x8000000u

/**
 * Peripheral base address for aes in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_AES_BASE_ADDR 0xC1100000u

/**
 * Peripheral size for aes in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_AES_BASE_ADDR and
 * `TOP_EARLGREY_AES_BASE_ADDR + TOP_EARLGREY_AES_SIZE_BYTES`.
 */
#define TOP_EARLGREY_AES_SIZE_BYTES 0x100u

/**
 * Peripheral base address for hmac in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_HMAC_BASE_ADDR 0xC1110000u

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
#define TOP_EARLGREY_KMAC_BASE_ADDR 0xC1120000u

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
 * Peripheral base address for otbn in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_OTBN_BASE_ADDR 0xC1130000u

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
 * Peripheral base address for keymgr in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_KEYMGR_BASE_ADDR 0xC1140000u

/**
 * Peripheral size for keymgr in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_KEYMGR_BASE_ADDR and
 * `TOP_EARLGREY_KEYMGR_BASE_ADDR + TOP_EARLGREY_KEYMGR_SIZE_BYTES`.
 */
#define TOP_EARLGREY_KEYMGR_SIZE_BYTES 0x100u

/**
 * Peripheral base address for csrng in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_CSRNG_BASE_ADDR 0xC1150000u

/**
 * Peripheral size for csrng in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_CSRNG_BASE_ADDR and
 * `TOP_EARLGREY_CSRNG_BASE_ADDR + TOP_EARLGREY_CSRNG_SIZE_BYTES`.
 */
#define TOP_EARLGREY_CSRNG_SIZE_BYTES 0x80u

/**
 * Peripheral base address for entropy_src in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR 0xC1160000u

/**
 * Peripheral size for entropy_src in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR and
 * `TOP_EARLGREY_ENTROPY_SRC_BASE_ADDR + TOP_EARLGREY_ENTROPY_SRC_SIZE_BYTES`.
 */
#define TOP_EARLGREY_ENTROPY_SRC_SIZE_BYTES 0x100u

/**
 * Peripheral base address for edn0 in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_EDN0_BASE_ADDR 0xC1170000u

/**
 * Peripheral size for edn0 in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_EDN0_BASE_ADDR and
 * `TOP_EARLGREY_EDN0_BASE_ADDR + TOP_EARLGREY_EDN0_SIZE_BYTES`.
 */
#define TOP_EARLGREY_EDN0_SIZE_BYTES 0x80u

/**
 * Peripheral base address for edn1 in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_EDN1_BASE_ADDR 0xC1180000u

/**
 * Peripheral size for edn1 in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_EDN1_BASE_ADDR and
 * `TOP_EARLGREY_EDN1_BASE_ADDR + TOP_EARLGREY_EDN1_SIZE_BYTES`.
 */
#define TOP_EARLGREY_EDN1_SIZE_BYTES 0x80u

/**
 * Peripheral base address for regs device on sram_ctrl_main in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR 0xC11C0000u

/**
 * Peripheral size for regs device on sram_ctrl_main in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR and
 * `TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR + TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_SIZE_BYTES`.
 */
#define TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_SIZE_BYTES 0x20u

/**
 * Peripheral base address for ram device on sram_ctrl_main in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_BASE_ADDR 0xE0000000u

/**
 * Peripheral size for ram device on sram_ctrl_main in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_BASE_ADDR and
 * `TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_BASE_ADDR + TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_SIZE_BYTES`.
 */
#define TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_SIZE_BYTES 0x20000u

/**
 * Peripheral base address for regs device on rom_ctrl in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_ROM_CTRL_REGS_BASE_ADDR 0xC11E0000u

/**
 * Peripheral size for regs device on rom_ctrl in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_ROM_CTRL_REGS_BASE_ADDR and
 * `TOP_EARLGREY_ROM_CTRL_REGS_BASE_ADDR + TOP_EARLGREY_ROM_CTRL_REGS_SIZE_BYTES`.
 */
#define TOP_EARLGREY_ROM_CTRL_REGS_SIZE_BYTES 0x80u

/**
 * Peripheral base address for rom device on rom_ctrl in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_ROM_CTRL_ROM_BASE_ADDR 0xD0008000u

/**
 * Peripheral size for rom device on rom_ctrl in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_ROM_CTRL_ROM_BASE_ADDR and
 * `TOP_EARLGREY_ROM_CTRL_ROM_BASE_ADDR + TOP_EARLGREY_ROM_CTRL_ROM_SIZE_BYTES`.
 */
#define TOP_EARLGREY_ROM_CTRL_ROM_SIZE_BYTES 0x8000u

/**
 * Peripheral base address for cfg device on rv_core_ibex in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR 0xC11F0000u

/**
 * Peripheral size for cfg device on rv_core_ibex in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR and
 * `TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR + TOP_EARLGREY_RV_CORE_IBEX_CFG_SIZE_BYTES`.
 */
#define TOP_EARLGREY_RV_CORE_IBEX_CFG_SIZE_BYTES 0x100u


/**
 * Memory base address for ram_ret_aon in top earlgrey.
 */
#define TOP_EARLGREY_RAM_RET_AON_BASE_ADDR 0xB0600000u

/**
 * Memory size for ram_ret_aon in top earlgrey.
 */
#define TOP_EARLGREY_RAM_RET_AON_SIZE_BYTES 0x1000u

/**
 * Memory base address for eflash in top earlgrey.
 */
#define TOP_EARLGREY_EFLASH_BASE_ADDR 0xF0000000u

/**
 * Memory size for eflash in top earlgrey.
 */
#define TOP_EARLGREY_EFLASH_SIZE_BYTES 0x100000u

/**
 * Memory base address for ram_main in top earlgrey.
 */
#define TOP_EARLGREY_RAM_MAIN_BASE_ADDR 0xE0000000u

/**
 * Memory size for ram_main in top earlgrey.
 */
#define TOP_EARLGREY_RAM_MAIN_SIZE_BYTES 0x20000u

/**
 * Memory base address for rom in top earlgrey.
 */
#define TOP_EARLGREY_ROM_BASE_ADDR 0xD0008000u

/**
 * Memory size for rom in top earlgrey.
 */
#define TOP_EARLGREY_ROM_SIZE_BYTES 0x8000u


/**
 * PLIC Interrupt Source Peripheral.
 *
 * Enumeration used to determine which peripheral asserted the corresponding
 * interrupt.
 */
typedef enum top_earlgrey_plic_peripheral {
  kTopEarlgreyPlicPeripheralUnknown = 0, /**< Unknown Peripheral */
  kTopEarlgreyPlicPeripheralGpio = 1, /**< gpio */
  kTopEarlgreyPlicPeripheralPattgen = 2, /**< pattgen */
  kTopEarlgreyPlicPeripheralRvTimer = 3, /**< rv_timer */
  kTopEarlgreyPlicPeripheralOtpCtrl = 4, /**< otp_ctrl */
  kTopEarlgreyPlicPeripheralAlertHandler = 5, /**< alert_handler */
  kTopEarlgreyPlicPeripheralSpiHost0 = 6, /**< spi_host0 */
  kTopEarlgreyPlicPeripheralSpiHost1 = 7, /**< spi_host1 */
  kTopEarlgreyPlicPeripheralSpiDevice = 8, /**< spi_device */
  kTopEarlgreyPlicPeripheralPwrmgrAon = 9, /**< pwrmgr_aon */
  kTopEarlgreyPlicPeripheralSysrstCtrlAon = 10, /**< sysrst_ctrl_aon */
  kTopEarlgreyPlicPeripheralAonTimerAon = 11, /**< aon_timer_aon */
  kTopEarlgreyPlicPeripheralFlashCtrl = 12, /**< flash_ctrl */
  kTopEarlgreyPlicPeripheralTlul2axi = 13, /**< tlul2axi */
  kTopEarlgreyPlicPeripheralHmac = 14, /**< hmac */
  kTopEarlgreyPlicPeripheralKmac = 15, /**< kmac */
  kTopEarlgreyPlicPeripheralOtbn = 16, /**< otbn */
  kTopEarlgreyPlicPeripheralKeymgr = 17, /**< keymgr */
  kTopEarlgreyPlicPeripheralCsrng = 18, /**< csrng */
  kTopEarlgreyPlicPeripheralEntropySrc = 19, /**< entropy_src */
  kTopEarlgreyPlicPeripheralEdn0 = 20, /**< edn0 */
  kTopEarlgreyPlicPeripheralEdn1 = 21, /**< edn1 */
  kTopEarlgreyPlicPeripheralLast = 21, /**< \internal Final PLIC peripheral */
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
  kTopEarlgreyPlicIrqIdPattgenDoneCh0 = 33, /**< pattgen_done_ch0 */
  kTopEarlgreyPlicIrqIdPattgenDoneCh1 = 34, /**< pattgen_done_ch1 */
  kTopEarlgreyPlicIrqIdRvTimerTimerExpiredHart0Timer0 = 35, /**< rv_timer_timer_expired_hart0_timer0 */
  kTopEarlgreyPlicIrqIdOtpCtrlOtpOperationDone = 36, /**< otp_ctrl_otp_operation_done */
  kTopEarlgreyPlicIrqIdOtpCtrlOtpError = 37, /**< otp_ctrl_otp_error */
  kTopEarlgreyPlicIrqIdAlertHandlerClassa = 38, /**< alert_handler_classa */
  kTopEarlgreyPlicIrqIdAlertHandlerClassb = 39, /**< alert_handler_classb */
  kTopEarlgreyPlicIrqIdAlertHandlerClassc = 40, /**< alert_handler_classc */
  kTopEarlgreyPlicIrqIdAlertHandlerClassd = 41, /**< alert_handler_classd */
  kTopEarlgreyPlicIrqIdSpiHost0Error = 42, /**< spi_host0_error */
  kTopEarlgreyPlicIrqIdSpiHost0SpiEvent = 43, /**< spi_host0_spi_event */
  kTopEarlgreyPlicIrqIdSpiHost1Error = 44, /**< spi_host1_error */
  kTopEarlgreyPlicIrqIdSpiHost1SpiEvent = 45, /**< spi_host1_spi_event */
  kTopEarlgreyPlicIrqIdSpiDeviceGenericRxFull = 46, /**< spi_device_generic_rx_full */
  kTopEarlgreyPlicIrqIdSpiDeviceGenericRxWatermark = 47, /**< spi_device_generic_rx_watermark */
  kTopEarlgreyPlicIrqIdSpiDeviceGenericTxWatermark = 48, /**< spi_device_generic_tx_watermark */
  kTopEarlgreyPlicIrqIdSpiDeviceGenericRxError = 49, /**< spi_device_generic_rx_error */
  kTopEarlgreyPlicIrqIdSpiDeviceGenericRxOverflow = 50, /**< spi_device_generic_rx_overflow */
  kTopEarlgreyPlicIrqIdSpiDeviceGenericTxUnderflow = 51, /**< spi_device_generic_tx_underflow */
  kTopEarlgreyPlicIrqIdSpiDeviceUploadCmdfifoNotEmpty = 52, /**< spi_device_upload_cmdfifo_not_empty */
  kTopEarlgreyPlicIrqIdSpiDeviceUploadPayloadNotEmpty = 53, /**< spi_device_upload_payload_not_empty */
  kTopEarlgreyPlicIrqIdSpiDeviceUploadPayloadOverflow = 54, /**< spi_device_upload_payload_overflow */
  kTopEarlgreyPlicIrqIdSpiDeviceReadbufWatermark = 55, /**< spi_device_readbuf_watermark */
  kTopEarlgreyPlicIrqIdSpiDeviceReadbufFlip = 56, /**< spi_device_readbuf_flip */
  kTopEarlgreyPlicIrqIdSpiDeviceTpmHeaderNotEmpty = 57, /**< spi_device_tpm_header_not_empty */
  kTopEarlgreyPlicIrqIdPwrmgrAonWakeup = 58, /**< pwrmgr_aon_wakeup */
  kTopEarlgreyPlicIrqIdSysrstCtrlAonEventDetected = 59, /**< sysrst_ctrl_aon_event_detected */
  kTopEarlgreyPlicIrqIdAonTimerAonWkupTimerExpired = 60, /**< aon_timer_aon_wkup_timer_expired */
  kTopEarlgreyPlicIrqIdAonTimerAonWdogTimerBark = 61, /**< aon_timer_aon_wdog_timer_bark */
  kTopEarlgreyPlicIrqIdFlashCtrlProgEmpty = 62, /**< flash_ctrl_prog_empty */
  kTopEarlgreyPlicIrqIdFlashCtrlProgLvl = 63, /**< flash_ctrl_prog_lvl */
  kTopEarlgreyPlicIrqIdFlashCtrlRdFull = 64, /**< flash_ctrl_rd_full */
  kTopEarlgreyPlicIrqIdFlashCtrlRdLvl = 65, /**< flash_ctrl_rd_lvl */
  kTopEarlgreyPlicIrqIdFlashCtrlOpDone = 66, /**< flash_ctrl_op_done */
  kTopEarlgreyPlicIrqIdFlashCtrlCorrErr = 67, /**< flash_ctrl_corr_err */
  kTopEarlgreyPlicIrqIdTlul2axiMboxIrq = 68, /**< tlul2axi_mbox_irq */
  kTopEarlgreyPlicIrqIdHmacHmacDone = 69, /**< hmac_hmac_done */
  kTopEarlgreyPlicIrqIdHmacFifoEmpty = 70, /**< hmac_fifo_empty */
  kTopEarlgreyPlicIrqIdHmacHmacErr = 71, /**< hmac_hmac_err */
  kTopEarlgreyPlicIrqIdKmacKmacDone = 72, /**< kmac_kmac_done */
  kTopEarlgreyPlicIrqIdKmacFifoEmpty = 73, /**< kmac_fifo_empty */
  kTopEarlgreyPlicIrqIdKmacKmacErr = 74, /**< kmac_kmac_err */
  kTopEarlgreyPlicIrqIdOtbnDone = 75, /**< otbn_done */
  kTopEarlgreyPlicIrqIdKeymgrOpDone = 76, /**< keymgr_op_done */
  kTopEarlgreyPlicIrqIdCsrngCsCmdReqDone = 77, /**< csrng_cs_cmd_req_done */
  kTopEarlgreyPlicIrqIdCsrngCsEntropyReq = 78, /**< csrng_cs_entropy_req */
  kTopEarlgreyPlicIrqIdCsrngCsHwInstExc = 79, /**< csrng_cs_hw_inst_exc */
  kTopEarlgreyPlicIrqIdCsrngCsFatalErr = 80, /**< csrng_cs_fatal_err */
  kTopEarlgreyPlicIrqIdEntropySrcEsEntropyValid = 81, /**< entropy_src_es_entropy_valid */
  kTopEarlgreyPlicIrqIdEntropySrcEsHealthTestFailed = 82, /**< entropy_src_es_health_test_failed */
  kTopEarlgreyPlicIrqIdEntropySrcEsObserveFifoReady = 83, /**< entropy_src_es_observe_fifo_ready */
  kTopEarlgreyPlicIrqIdEntropySrcEsFatalErr = 84, /**< entropy_src_es_fatal_err */
  kTopEarlgreyPlicIrqIdEdn0EdnCmdReqDone = 85, /**< edn0_edn_cmd_req_done */
  kTopEarlgreyPlicIrqIdEdn0EdnFatalErr = 86, /**< edn0_edn_fatal_err */
  kTopEarlgreyPlicIrqIdEdn1EdnCmdReqDone = 87, /**< edn1_edn_cmd_req_done */
  kTopEarlgreyPlicIrqIdEdn1EdnFatalErr = 88, /**< edn1_edn_fatal_err */
  kTopEarlgreyPlicIrqIdLast = 88, /**< \internal The Last Valid Interrupt ID. */
} top_earlgrey_plic_irq_id_t;

/**
 * PLIC Interrupt Source to Peripheral Map
 *
 * This array is a mapping from `top_earlgrey_plic_irq_id_t` to
 * `top_earlgrey_plic_peripheral_t`.
 */
extern const top_earlgrey_plic_peripheral_t
    top_earlgrey_plic_interrupt_for_peripheral[89];

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
  kTopEarlgreyAlertPeripheralGpio = 0, /**< gpio */
  kTopEarlgreyAlertPeripheralPattgen = 1, /**< pattgen */
  kTopEarlgreyAlertPeripheralRvTimer = 2, /**< rv_timer */
  kTopEarlgreyAlertPeripheralOtpCtrl = 3, /**< otp_ctrl */
  kTopEarlgreyAlertPeripheralLcCtrl = 4, /**< lc_ctrl */
  kTopEarlgreyAlertPeripheralSpiHost0 = 5, /**< spi_host0 */
  kTopEarlgreyAlertPeripheralSpiHost1 = 6, /**< spi_host1 */
  kTopEarlgreyAlertPeripheralSpiDevice = 7, /**< spi_device */
  kTopEarlgreyAlertPeripheralPwrmgrAon = 8, /**< pwrmgr_aon */
  kTopEarlgreyAlertPeripheralRstmgrAon = 9, /**< rstmgr_aon */
  kTopEarlgreyAlertPeripheralClkmgrAon = 10, /**< clkmgr_aon */
  kTopEarlgreyAlertPeripheralSysrstCtrlAon = 11, /**< sysrst_ctrl_aon */
  kTopEarlgreyAlertPeripheralPinmuxAon = 12, /**< pinmux_aon */
  kTopEarlgreyAlertPeripheralAonTimerAon = 13, /**< aon_timer_aon */
  kTopEarlgreyAlertPeripheralSramCtrlRetAon = 14, /**< sram_ctrl_ret_aon */
  kTopEarlgreyAlertPeripheralFlashCtrl = 15, /**< flash_ctrl */
  kTopEarlgreyAlertPeripheralRvDm = 16, /**< rv_dm */
  kTopEarlgreyAlertPeripheralRvPlic = 17, /**< rv_plic */
  kTopEarlgreyAlertPeripheralAes = 18, /**< aes */
  kTopEarlgreyAlertPeripheralHmac = 19, /**< hmac */
  kTopEarlgreyAlertPeripheralKmac = 20, /**< kmac */
  kTopEarlgreyAlertPeripheralOtbn = 21, /**< otbn */
  kTopEarlgreyAlertPeripheralKeymgr = 22, /**< keymgr */
  kTopEarlgreyAlertPeripheralCsrng = 23, /**< csrng */
  kTopEarlgreyAlertPeripheralEntropySrc = 24, /**< entropy_src */
  kTopEarlgreyAlertPeripheralEdn0 = 25, /**< edn0 */
  kTopEarlgreyAlertPeripheralEdn1 = 26, /**< edn1 */
  kTopEarlgreyAlertPeripheralSramCtrlMain = 27, /**< sram_ctrl_main */
  kTopEarlgreyAlertPeripheralRomCtrl = 28, /**< rom_ctrl */
  kTopEarlgreyAlertPeripheralRvCoreIbex = 29, /**< rv_core_ibex */
  kTopEarlgreyAlertPeripheralLast = 29, /**< \internal Final Alert peripheral */
} top_earlgrey_alert_peripheral_t;

/**
 * Alert Handler Alert Source.
 *
 * Enumeration of all Alert Handler Alert Sources. The alert sources belonging to
 * the same peripheral are guaranteed to be consecutive.
 */
typedef enum top_earlgrey_alert_id {
  kTopEarlgreyAlertIdGpioFatalFault = 0, /**< gpio_fatal_fault */
  kTopEarlgreyAlertIdPattgenFatalFault = 1, /**< pattgen_fatal_fault */
  kTopEarlgreyAlertIdRvTimerFatalFault = 2, /**< rv_timer_fatal_fault */
  kTopEarlgreyAlertIdOtpCtrlFatalMacroError = 3, /**< otp_ctrl_fatal_macro_error */
  kTopEarlgreyAlertIdOtpCtrlFatalCheckError = 4, /**< otp_ctrl_fatal_check_error */
  kTopEarlgreyAlertIdOtpCtrlFatalBusIntegError = 5, /**< otp_ctrl_fatal_bus_integ_error */
  kTopEarlgreyAlertIdOtpCtrlFatalPrimOtpAlert = 6, /**< otp_ctrl_fatal_prim_otp_alert */
  kTopEarlgreyAlertIdOtpCtrlRecovPrimOtpAlert = 7, /**< otp_ctrl_recov_prim_otp_alert */
  kTopEarlgreyAlertIdLcCtrlFatalProgError = 8, /**< lc_ctrl_fatal_prog_error */
  kTopEarlgreyAlertIdLcCtrlFatalStateError = 9, /**< lc_ctrl_fatal_state_error */
  kTopEarlgreyAlertIdLcCtrlFatalBusIntegError = 10, /**< lc_ctrl_fatal_bus_integ_error */
  kTopEarlgreyAlertIdSpiHost0FatalFault = 11, /**< spi_host0_fatal_fault */
  kTopEarlgreyAlertIdSpiHost1FatalFault = 12, /**< spi_host1_fatal_fault */
  kTopEarlgreyAlertIdSpiDeviceFatalFault = 13, /**< spi_device_fatal_fault */
  kTopEarlgreyAlertIdPwrmgrAonFatalFault = 14, /**< pwrmgr_aon_fatal_fault */
  kTopEarlgreyAlertIdRstmgrAonFatalFault = 15, /**< rstmgr_aon_fatal_fault */
  kTopEarlgreyAlertIdRstmgrAonFatalCnstyFault = 16, /**< rstmgr_aon_fatal_cnsty_fault */
  kTopEarlgreyAlertIdClkmgrAonRecovFault = 17, /**< clkmgr_aon_recov_fault */
  kTopEarlgreyAlertIdClkmgrAonFatalFault = 18, /**< clkmgr_aon_fatal_fault */
  kTopEarlgreyAlertIdSysrstCtrlAonFatalFault = 19, /**< sysrst_ctrl_aon_fatal_fault */
  kTopEarlgreyAlertIdPinmuxAonFatalFault = 20, /**< pinmux_aon_fatal_fault */
  kTopEarlgreyAlertIdAonTimerAonFatalFault = 21, /**< aon_timer_aon_fatal_fault */
  kTopEarlgreyAlertIdSramCtrlRetAonFatalError = 22, /**< sram_ctrl_ret_aon_fatal_error */
  kTopEarlgreyAlertIdFlashCtrlRecovErr = 23, /**< flash_ctrl_recov_err */
  kTopEarlgreyAlertIdFlashCtrlFatalStdErr = 24, /**< flash_ctrl_fatal_std_err */
  kTopEarlgreyAlertIdFlashCtrlFatalErr = 25, /**< flash_ctrl_fatal_err */
  kTopEarlgreyAlertIdFlashCtrlFatalPrimFlashAlert = 26, /**< flash_ctrl_fatal_prim_flash_alert */
  kTopEarlgreyAlertIdFlashCtrlRecovPrimFlashAlert = 27, /**< flash_ctrl_recov_prim_flash_alert */
  kTopEarlgreyAlertIdRvDmFatalFault = 28, /**< rv_dm_fatal_fault */
  kTopEarlgreyAlertIdRvPlicFatalFault = 29, /**< rv_plic_fatal_fault */
  kTopEarlgreyAlertIdAesRecovCtrlUpdateErr = 30, /**< aes_recov_ctrl_update_err */
  kTopEarlgreyAlertIdAesFatalFault = 31, /**< aes_fatal_fault */
  kTopEarlgreyAlertIdHmacFatalFault = 32, /**< hmac_fatal_fault */
  kTopEarlgreyAlertIdKmacRecovOperationErr = 33, /**< kmac_recov_operation_err */
  kTopEarlgreyAlertIdKmacFatalFaultErr = 34, /**< kmac_fatal_fault_err */
  kTopEarlgreyAlertIdOtbnFatal = 35, /**< otbn_fatal */
  kTopEarlgreyAlertIdOtbnRecov = 36, /**< otbn_recov */
  kTopEarlgreyAlertIdKeymgrRecovOperationErr = 37, /**< keymgr_recov_operation_err */
  kTopEarlgreyAlertIdKeymgrFatalFaultErr = 38, /**< keymgr_fatal_fault_err */
  kTopEarlgreyAlertIdCsrngRecovAlert = 39, /**< csrng_recov_alert */
  kTopEarlgreyAlertIdCsrngFatalAlert = 40, /**< csrng_fatal_alert */
  kTopEarlgreyAlertIdEntropySrcRecovAlert = 41, /**< entropy_src_recov_alert */
  kTopEarlgreyAlertIdEntropySrcFatalAlert = 42, /**< entropy_src_fatal_alert */
  kTopEarlgreyAlertIdEdn0RecovAlert = 43, /**< edn0_recov_alert */
  kTopEarlgreyAlertIdEdn0FatalAlert = 44, /**< edn0_fatal_alert */
  kTopEarlgreyAlertIdEdn1RecovAlert = 45, /**< edn1_recov_alert */
  kTopEarlgreyAlertIdEdn1FatalAlert = 46, /**< edn1_fatal_alert */
  kTopEarlgreyAlertIdSramCtrlMainFatalError = 47, /**< sram_ctrl_main_fatal_error */
  kTopEarlgreyAlertIdRomCtrlFatal = 48, /**< rom_ctrl_fatal */
  kTopEarlgreyAlertIdRvCoreIbexFatalSwErr = 49, /**< rv_core_ibex_fatal_sw_err */
  kTopEarlgreyAlertIdRvCoreIbexRecovSwErr = 50, /**< rv_core_ibex_recov_sw_err */
  kTopEarlgreyAlertIdRvCoreIbexFatalHwErr = 51, /**< rv_core_ibex_fatal_hw_err */
  kTopEarlgreyAlertIdRvCoreIbexRecovHwErr = 52, /**< rv_core_ibex_recov_hw_err */
  kTopEarlgreyAlertIdLast = 52, /**< \internal The Last Valid Alert ID. */
} top_earlgrey_alert_id_t;

/**
 * Alert Handler Alert Source to Peripheral Map
 *
 * This array is a mapping from `top_earlgrey_alert_id_t` to
 * `top_earlgrey_alert_peripheral_t`.
 */
extern const top_earlgrey_alert_peripheral_t
    top_earlgrey_alert_for_peripheral[53];

#define PINMUX_MIO_PERIPH_INSEL_IDX_OFFSET 2

// PERIPH_INSEL ranges from 0 to NUM_MIO_PADS + 2 -1}
//  0 and 1 are tied to value 0 and 1
#define NUM_MIO_PADS 47
#define NUM_DIO_PADS 14

#define PINMUX_PERIPH_OUTSEL_IDX_OFFSET 3

/**
 * Pinmux Peripheral Input.
 */
typedef enum top_earlgrey_pinmux_peripheral_in {
  kTopEarlgreyPinmuxPeripheralInGpioGpio0 = 0, /**< Peripheral Input 0 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio1 = 1, /**< Peripheral Input 1 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio2 = 2, /**< Peripheral Input 2 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio3 = 3, /**< Peripheral Input 3 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio4 = 4, /**< Peripheral Input 4 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio5 = 5, /**< Peripheral Input 5 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio6 = 6, /**< Peripheral Input 6 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio7 = 7, /**< Peripheral Input 7 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio8 = 8, /**< Peripheral Input 8 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio9 = 9, /**< Peripheral Input 9 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio10 = 10, /**< Peripheral Input 10 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio11 = 11, /**< Peripheral Input 11 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio12 = 12, /**< Peripheral Input 12 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio13 = 13, /**< Peripheral Input 13 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio14 = 14, /**< Peripheral Input 14 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio15 = 15, /**< Peripheral Input 15 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio16 = 16, /**< Peripheral Input 16 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio17 = 17, /**< Peripheral Input 17 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio18 = 18, /**< Peripheral Input 18 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio19 = 19, /**< Peripheral Input 19 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio20 = 20, /**< Peripheral Input 20 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio21 = 21, /**< Peripheral Input 21 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio22 = 22, /**< Peripheral Input 22 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio23 = 23, /**< Peripheral Input 23 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio24 = 24, /**< Peripheral Input 24 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio25 = 25, /**< Peripheral Input 25 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio26 = 26, /**< Peripheral Input 26 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio27 = 27, /**< Peripheral Input 27 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio28 = 28, /**< Peripheral Input 28 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio29 = 29, /**< Peripheral Input 29 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio30 = 30, /**< Peripheral Input 30 */
  kTopEarlgreyPinmuxPeripheralInGpioGpio31 = 31, /**< Peripheral Input 31 */
  kTopEarlgreyPinmuxPeripheralInSpiHost1Sd0 = 32, /**< Peripheral Input 32 */
  kTopEarlgreyPinmuxPeripheralInSpiHost1Sd1 = 33, /**< Peripheral Input 33 */
  kTopEarlgreyPinmuxPeripheralInSpiHost1Sd2 = 34, /**< Peripheral Input 34 */
  kTopEarlgreyPinmuxPeripheralInSpiHost1Sd3 = 35, /**< Peripheral Input 35 */
  kTopEarlgreyPinmuxPeripheralInSpiDeviceTpmCsb = 36, /**< Peripheral Input 36 */
  kTopEarlgreyPinmuxPeripheralInFlashCtrlTck = 37, /**< Peripheral Input 37 */
  kTopEarlgreyPinmuxPeripheralInFlashCtrlTms = 38, /**< Peripheral Input 38 */
  kTopEarlgreyPinmuxPeripheralInFlashCtrlTdi = 39, /**< Peripheral Input 39 */
  kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonAcPresent = 40, /**< Peripheral Input 40 */
  kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonKey0In = 41, /**< Peripheral Input 41 */
  kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonKey1In = 42, /**< Peripheral Input 42 */
  kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonKey2In = 43, /**< Peripheral Input 43 */
  kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonPwrbIn = 44, /**< Peripheral Input 44 */
  kTopEarlgreyPinmuxPeripheralInSysrstCtrlAonLidOpen = 45, /**< Peripheral Input 45 */
  kTopEarlgreyPinmuxPeripheralInLast = 45, /**< \internal Last valid peripheral input */
} top_earlgrey_pinmux_peripheral_in_t;

/**
 * Pinmux MIO Input Selector.
 */
typedef enum top_earlgrey_pinmux_insel {
  kTopEarlgreyPinmuxInselConstantZero = 0, /**< Tie constantly to zero */
  kTopEarlgreyPinmuxInselConstantOne = 1, /**< Tie constantly to one */
  kTopEarlgreyPinmuxInselIoa0 = 2, /**< MIO Pad 0 */
  kTopEarlgreyPinmuxInselIoa1 = 3, /**< MIO Pad 1 */
  kTopEarlgreyPinmuxInselIoa2 = 4, /**< MIO Pad 2 */
  kTopEarlgreyPinmuxInselIoa3 = 5, /**< MIO Pad 3 */
  kTopEarlgreyPinmuxInselIoa4 = 6, /**< MIO Pad 4 */
  kTopEarlgreyPinmuxInselIoa5 = 7, /**< MIO Pad 5 */
  kTopEarlgreyPinmuxInselIoa6 = 8, /**< MIO Pad 6 */
  kTopEarlgreyPinmuxInselIoa7 = 9, /**< MIO Pad 7 */
  kTopEarlgreyPinmuxInselIoa8 = 10, /**< MIO Pad 8 */
  kTopEarlgreyPinmuxInselIob0 = 11, /**< MIO Pad 9 */
  kTopEarlgreyPinmuxInselIob1 = 12, /**< MIO Pad 10 */
  kTopEarlgreyPinmuxInselIob2 = 13, /**< MIO Pad 11 */
  kTopEarlgreyPinmuxInselIob3 = 14, /**< MIO Pad 12 */
  kTopEarlgreyPinmuxInselIob4 = 15, /**< MIO Pad 13 */
  kTopEarlgreyPinmuxInselIob5 = 16, /**< MIO Pad 14 */
  kTopEarlgreyPinmuxInselIob6 = 17, /**< MIO Pad 15 */
  kTopEarlgreyPinmuxInselIob7 = 18, /**< MIO Pad 16 */
  kTopEarlgreyPinmuxInselIob8 = 19, /**< MIO Pad 17 */
  kTopEarlgreyPinmuxInselIob9 = 20, /**< MIO Pad 18 */
  kTopEarlgreyPinmuxInselIob10 = 21, /**< MIO Pad 19 */
  kTopEarlgreyPinmuxInselIob11 = 22, /**< MIO Pad 20 */
  kTopEarlgreyPinmuxInselIob12 = 23, /**< MIO Pad 21 */
  kTopEarlgreyPinmuxInselIoc0 = 24, /**< MIO Pad 22 */
  kTopEarlgreyPinmuxInselIoc1 = 25, /**< MIO Pad 23 */
  kTopEarlgreyPinmuxInselIoc2 = 26, /**< MIO Pad 24 */
  kTopEarlgreyPinmuxInselIoc3 = 27, /**< MIO Pad 25 */
  kTopEarlgreyPinmuxInselIoc4 = 28, /**< MIO Pad 26 */
  kTopEarlgreyPinmuxInselIoc5 = 29, /**< MIO Pad 27 */
  kTopEarlgreyPinmuxInselIoc6 = 30, /**< MIO Pad 28 */
  kTopEarlgreyPinmuxInselIoc7 = 31, /**< MIO Pad 29 */
  kTopEarlgreyPinmuxInselIoc8 = 32, /**< MIO Pad 30 */
  kTopEarlgreyPinmuxInselIoc9 = 33, /**< MIO Pad 31 */
  kTopEarlgreyPinmuxInselIoc10 = 34, /**< MIO Pad 32 */
  kTopEarlgreyPinmuxInselIoc11 = 35, /**< MIO Pad 33 */
  kTopEarlgreyPinmuxInselIoc12 = 36, /**< MIO Pad 34 */
  kTopEarlgreyPinmuxInselIor0 = 37, /**< MIO Pad 35 */
  kTopEarlgreyPinmuxInselIor1 = 38, /**< MIO Pad 36 */
  kTopEarlgreyPinmuxInselIor2 = 39, /**< MIO Pad 37 */
  kTopEarlgreyPinmuxInselIor3 = 40, /**< MIO Pad 38 */
  kTopEarlgreyPinmuxInselIor4 = 41, /**< MIO Pad 39 */
  kTopEarlgreyPinmuxInselIor5 = 42, /**< MIO Pad 40 */
  kTopEarlgreyPinmuxInselIor6 = 43, /**< MIO Pad 41 */
  kTopEarlgreyPinmuxInselIor7 = 44, /**< MIO Pad 42 */
  kTopEarlgreyPinmuxInselIor10 = 45, /**< MIO Pad 43 */
  kTopEarlgreyPinmuxInselIor11 = 46, /**< MIO Pad 44 */
  kTopEarlgreyPinmuxInselIor12 = 47, /**< MIO Pad 45 */
  kTopEarlgreyPinmuxInselIor13 = 48, /**< MIO Pad 46 */
  kTopEarlgreyPinmuxInselLast = 48, /**< \internal Last valid insel value */
} top_earlgrey_pinmux_insel_t;

/**
 * Pinmux MIO Output.
 */
typedef enum top_earlgrey_pinmux_mio_out {
  kTopEarlgreyPinmuxMioOutIoa0 = 0, /**< MIO Pad 0 */
  kTopEarlgreyPinmuxMioOutIoa1 = 1, /**< MIO Pad 1 */
  kTopEarlgreyPinmuxMioOutIoa2 = 2, /**< MIO Pad 2 */
  kTopEarlgreyPinmuxMioOutIoa3 = 3, /**< MIO Pad 3 */
  kTopEarlgreyPinmuxMioOutIoa4 = 4, /**< MIO Pad 4 */
  kTopEarlgreyPinmuxMioOutIoa5 = 5, /**< MIO Pad 5 */
  kTopEarlgreyPinmuxMioOutIoa6 = 6, /**< MIO Pad 6 */
  kTopEarlgreyPinmuxMioOutIoa7 = 7, /**< MIO Pad 7 */
  kTopEarlgreyPinmuxMioOutIoa8 = 8, /**< MIO Pad 8 */
  kTopEarlgreyPinmuxMioOutIob0 = 9, /**< MIO Pad 9 */
  kTopEarlgreyPinmuxMioOutIob1 = 10, /**< MIO Pad 10 */
  kTopEarlgreyPinmuxMioOutIob2 = 11, /**< MIO Pad 11 */
  kTopEarlgreyPinmuxMioOutIob3 = 12, /**< MIO Pad 12 */
  kTopEarlgreyPinmuxMioOutIob4 = 13, /**< MIO Pad 13 */
  kTopEarlgreyPinmuxMioOutIob5 = 14, /**< MIO Pad 14 */
  kTopEarlgreyPinmuxMioOutIob6 = 15, /**< MIO Pad 15 */
  kTopEarlgreyPinmuxMioOutIob7 = 16, /**< MIO Pad 16 */
  kTopEarlgreyPinmuxMioOutIob8 = 17, /**< MIO Pad 17 */
  kTopEarlgreyPinmuxMioOutIob9 = 18, /**< MIO Pad 18 */
  kTopEarlgreyPinmuxMioOutIob10 = 19, /**< MIO Pad 19 */
  kTopEarlgreyPinmuxMioOutIob11 = 20, /**< MIO Pad 20 */
  kTopEarlgreyPinmuxMioOutIob12 = 21, /**< MIO Pad 21 */
  kTopEarlgreyPinmuxMioOutIoc0 = 22, /**< MIO Pad 22 */
  kTopEarlgreyPinmuxMioOutIoc1 = 23, /**< MIO Pad 23 */
  kTopEarlgreyPinmuxMioOutIoc2 = 24, /**< MIO Pad 24 */
  kTopEarlgreyPinmuxMioOutIoc3 = 25, /**< MIO Pad 25 */
  kTopEarlgreyPinmuxMioOutIoc4 = 26, /**< MIO Pad 26 */
  kTopEarlgreyPinmuxMioOutIoc5 = 27, /**< MIO Pad 27 */
  kTopEarlgreyPinmuxMioOutIoc6 = 28, /**< MIO Pad 28 */
  kTopEarlgreyPinmuxMioOutIoc7 = 29, /**< MIO Pad 29 */
  kTopEarlgreyPinmuxMioOutIoc8 = 30, /**< MIO Pad 30 */
  kTopEarlgreyPinmuxMioOutIoc9 = 31, /**< MIO Pad 31 */
  kTopEarlgreyPinmuxMioOutIoc10 = 32, /**< MIO Pad 32 */
  kTopEarlgreyPinmuxMioOutIoc11 = 33, /**< MIO Pad 33 */
  kTopEarlgreyPinmuxMioOutIoc12 = 34, /**< MIO Pad 34 */
  kTopEarlgreyPinmuxMioOutIor0 = 35, /**< MIO Pad 35 */
  kTopEarlgreyPinmuxMioOutIor1 = 36, /**< MIO Pad 36 */
  kTopEarlgreyPinmuxMioOutIor2 = 37, /**< MIO Pad 37 */
  kTopEarlgreyPinmuxMioOutIor3 = 38, /**< MIO Pad 38 */
  kTopEarlgreyPinmuxMioOutIor4 = 39, /**< MIO Pad 39 */
  kTopEarlgreyPinmuxMioOutIor5 = 40, /**< MIO Pad 40 */
  kTopEarlgreyPinmuxMioOutIor6 = 41, /**< MIO Pad 41 */
  kTopEarlgreyPinmuxMioOutIor7 = 42, /**< MIO Pad 42 */
  kTopEarlgreyPinmuxMioOutIor10 = 43, /**< MIO Pad 43 */
  kTopEarlgreyPinmuxMioOutIor11 = 44, /**< MIO Pad 44 */
  kTopEarlgreyPinmuxMioOutIor12 = 45, /**< MIO Pad 45 */
  kTopEarlgreyPinmuxMioOutIor13 = 46, /**< MIO Pad 46 */
  kTopEarlgreyPinmuxMioOutLast = 46, /**< \internal Last valid mio output */
} top_earlgrey_pinmux_mio_out_t;

/**
 * Pinmux Peripheral Output Selector.
 */
typedef enum top_earlgrey_pinmux_outsel {
  kTopEarlgreyPinmuxOutselConstantZero = 0, /**< Tie constantly to zero */
  kTopEarlgreyPinmuxOutselConstantOne = 1, /**< Tie constantly to one */
  kTopEarlgreyPinmuxOutselConstantHighZ = 2, /**< Tie constantly to high-Z */
  kTopEarlgreyPinmuxOutselGpioGpio0 = 3, /**< Peripheral Output 0 */
  kTopEarlgreyPinmuxOutselGpioGpio1 = 4, /**< Peripheral Output 1 */
  kTopEarlgreyPinmuxOutselGpioGpio2 = 5, /**< Peripheral Output 2 */
  kTopEarlgreyPinmuxOutselGpioGpio3 = 6, /**< Peripheral Output 3 */
  kTopEarlgreyPinmuxOutselGpioGpio4 = 7, /**< Peripheral Output 4 */
  kTopEarlgreyPinmuxOutselGpioGpio5 = 8, /**< Peripheral Output 5 */
  kTopEarlgreyPinmuxOutselGpioGpio6 = 9, /**< Peripheral Output 6 */
  kTopEarlgreyPinmuxOutselGpioGpio7 = 10, /**< Peripheral Output 7 */
  kTopEarlgreyPinmuxOutselGpioGpio8 = 11, /**< Peripheral Output 8 */
  kTopEarlgreyPinmuxOutselGpioGpio9 = 12, /**< Peripheral Output 9 */
  kTopEarlgreyPinmuxOutselGpioGpio10 = 13, /**< Peripheral Output 10 */
  kTopEarlgreyPinmuxOutselGpioGpio11 = 14, /**< Peripheral Output 11 */
  kTopEarlgreyPinmuxOutselGpioGpio12 = 15, /**< Peripheral Output 12 */
  kTopEarlgreyPinmuxOutselGpioGpio13 = 16, /**< Peripheral Output 13 */
  kTopEarlgreyPinmuxOutselGpioGpio14 = 17, /**< Peripheral Output 14 */
  kTopEarlgreyPinmuxOutselGpioGpio15 = 18, /**< Peripheral Output 15 */
  kTopEarlgreyPinmuxOutselGpioGpio16 = 19, /**< Peripheral Output 16 */
  kTopEarlgreyPinmuxOutselGpioGpio17 = 20, /**< Peripheral Output 17 */
  kTopEarlgreyPinmuxOutselGpioGpio18 = 21, /**< Peripheral Output 18 */
  kTopEarlgreyPinmuxOutselGpioGpio19 = 22, /**< Peripheral Output 19 */
  kTopEarlgreyPinmuxOutselGpioGpio20 = 23, /**< Peripheral Output 20 */
  kTopEarlgreyPinmuxOutselGpioGpio21 = 24, /**< Peripheral Output 21 */
  kTopEarlgreyPinmuxOutselGpioGpio22 = 25, /**< Peripheral Output 22 */
  kTopEarlgreyPinmuxOutselGpioGpio23 = 26, /**< Peripheral Output 23 */
  kTopEarlgreyPinmuxOutselGpioGpio24 = 27, /**< Peripheral Output 24 */
  kTopEarlgreyPinmuxOutselGpioGpio25 = 28, /**< Peripheral Output 25 */
  kTopEarlgreyPinmuxOutselGpioGpio26 = 29, /**< Peripheral Output 26 */
  kTopEarlgreyPinmuxOutselGpioGpio27 = 30, /**< Peripheral Output 27 */
  kTopEarlgreyPinmuxOutselGpioGpio28 = 31, /**< Peripheral Output 28 */
  kTopEarlgreyPinmuxOutselGpioGpio29 = 32, /**< Peripheral Output 29 */
  kTopEarlgreyPinmuxOutselGpioGpio30 = 33, /**< Peripheral Output 30 */
  kTopEarlgreyPinmuxOutselGpioGpio31 = 34, /**< Peripheral Output 31 */
  kTopEarlgreyPinmuxOutselSpiHost1Sd0 = 35, /**< Peripheral Output 32 */
  kTopEarlgreyPinmuxOutselSpiHost1Sd1 = 36, /**< Peripheral Output 33 */
  kTopEarlgreyPinmuxOutselSpiHost1Sd2 = 37, /**< Peripheral Output 34 */
  kTopEarlgreyPinmuxOutselSpiHost1Sd3 = 38, /**< Peripheral Output 35 */
  kTopEarlgreyPinmuxOutselPattgenPda0Tx = 39, /**< Peripheral Output 36 */
  kTopEarlgreyPinmuxOutselPattgenPcl0Tx = 40, /**< Peripheral Output 37 */
  kTopEarlgreyPinmuxOutselPattgenPda1Tx = 41, /**< Peripheral Output 38 */
  kTopEarlgreyPinmuxOutselPattgenPcl1Tx = 42, /**< Peripheral Output 39 */
  kTopEarlgreyPinmuxOutselSpiHost1Sck = 43, /**< Peripheral Output 40 */
  kTopEarlgreyPinmuxOutselSpiHost1Csb = 44, /**< Peripheral Output 41 */
  kTopEarlgreyPinmuxOutselFlashCtrlTdo = 45, /**< Peripheral Output 42 */
  kTopEarlgreyPinmuxOutselOtpCtrlTest0 = 46, /**< Peripheral Output 43 */
  kTopEarlgreyPinmuxOutselSysrstCtrlAonBatDisable = 47, /**< Peripheral Output 44 */
  kTopEarlgreyPinmuxOutselSysrstCtrlAonKey0Out = 48, /**< Peripheral Output 45 */
  kTopEarlgreyPinmuxOutselSysrstCtrlAonKey1Out = 49, /**< Peripheral Output 46 */
  kTopEarlgreyPinmuxOutselSysrstCtrlAonKey2Out = 50, /**< Peripheral Output 47 */
  kTopEarlgreyPinmuxOutselSysrstCtrlAonPwrbOut = 51, /**< Peripheral Output 48 */
  kTopEarlgreyPinmuxOutselSysrstCtrlAonZ3Wakeup = 52, /**< Peripheral Output 49 */
  kTopEarlgreyPinmuxOutselLast = 52, /**< \internal Last valid outsel value */
} top_earlgrey_pinmux_outsel_t;

/**
 * Dedicated Pad Selects
 */
typedef enum top_earlgrey_direct_pads {
  kTopEarlgreyDirectPadsSpiHost0Sd0 = 0, /**<  */
  kTopEarlgreyDirectPadsSpiHost0Sd1 = 1, /**<  */
  kTopEarlgreyDirectPadsSpiHost0Sd2 = 2, /**<  */
  kTopEarlgreyDirectPadsSpiHost0Sd3 = 3, /**<  */
  kTopEarlgreyDirectPadsSpiDeviceSd0 = 4, /**<  */
  kTopEarlgreyDirectPadsSpiDeviceSd1 = 5, /**<  */
  kTopEarlgreyDirectPadsSpiDeviceSd2 = 6, /**<  */
  kTopEarlgreyDirectPadsSpiDeviceSd3 = 7, /**<  */
  kTopEarlgreyDirectPadsSysrstCtrlAonEcRstL = 8, /**<  */
  kTopEarlgreyDirectPadsSysrstCtrlAonFlashWpL = 9, /**<  */
  kTopEarlgreyDirectPadsSpiDeviceSck = 10, /**<  */
  kTopEarlgreyDirectPadsSpiDeviceCsb = 11, /**<  */
  kTopEarlgreyDirectPadsSpiHost0Sck = 12, /**<  */
  kTopEarlgreyDirectPadsSpiHost0Csb = 13, /**<  */
  kTopEarlgreyDirectPadsLast = 13, /**< \internal Last valid direct pad */
} top_earlgrey_direct_pads_t;

/**
 * Muxed Pad Selects
 */
typedef enum top_earlgrey_muxed_pads {
  kTopEarlgreyMuxedPadsIoa0 = 0, /**<  */
  kTopEarlgreyMuxedPadsIoa1 = 1, /**<  */
  kTopEarlgreyMuxedPadsIoa2 = 2, /**<  */
  kTopEarlgreyMuxedPadsIoa3 = 3, /**<  */
  kTopEarlgreyMuxedPadsIoa4 = 4, /**<  */
  kTopEarlgreyMuxedPadsIoa5 = 5, /**<  */
  kTopEarlgreyMuxedPadsIoa6 = 6, /**<  */
  kTopEarlgreyMuxedPadsIoa7 = 7, /**<  */
  kTopEarlgreyMuxedPadsIoa8 = 8, /**<  */
  kTopEarlgreyMuxedPadsIob0 = 9, /**<  */
  kTopEarlgreyMuxedPadsIob1 = 10, /**<  */
  kTopEarlgreyMuxedPadsIob2 = 11, /**<  */
  kTopEarlgreyMuxedPadsIob3 = 12, /**<  */
  kTopEarlgreyMuxedPadsIob4 = 13, /**<  */
  kTopEarlgreyMuxedPadsIob5 = 14, /**<  */
  kTopEarlgreyMuxedPadsIob6 = 15, /**<  */
  kTopEarlgreyMuxedPadsIob7 = 16, /**<  */
  kTopEarlgreyMuxedPadsIob8 = 17, /**<  */
  kTopEarlgreyMuxedPadsIob9 = 18, /**<  */
  kTopEarlgreyMuxedPadsIob10 = 19, /**<  */
  kTopEarlgreyMuxedPadsIob11 = 20, /**<  */
  kTopEarlgreyMuxedPadsIob12 = 21, /**<  */
  kTopEarlgreyMuxedPadsIoc0 = 22, /**<  */
  kTopEarlgreyMuxedPadsIoc1 = 23, /**<  */
  kTopEarlgreyMuxedPadsIoc2 = 24, /**<  */
  kTopEarlgreyMuxedPadsIoc3 = 25, /**<  */
  kTopEarlgreyMuxedPadsIoc4 = 26, /**<  */
  kTopEarlgreyMuxedPadsIoc5 = 27, /**<  */
  kTopEarlgreyMuxedPadsIoc6 = 28, /**<  */
  kTopEarlgreyMuxedPadsIoc7 = 29, /**<  */
  kTopEarlgreyMuxedPadsIoc8 = 30, /**<  */
  kTopEarlgreyMuxedPadsIoc9 = 31, /**<  */
  kTopEarlgreyMuxedPadsIoc10 = 32, /**<  */
  kTopEarlgreyMuxedPadsIoc11 = 33, /**<  */
  kTopEarlgreyMuxedPadsIoc12 = 34, /**<  */
  kTopEarlgreyMuxedPadsIor0 = 35, /**<  */
  kTopEarlgreyMuxedPadsIor1 = 36, /**<  */
  kTopEarlgreyMuxedPadsIor2 = 37, /**<  */
  kTopEarlgreyMuxedPadsIor3 = 38, /**<  */
  kTopEarlgreyMuxedPadsIor4 = 39, /**<  */
  kTopEarlgreyMuxedPadsIor5 = 40, /**<  */
  kTopEarlgreyMuxedPadsIor6 = 41, /**<  */
  kTopEarlgreyMuxedPadsIor7 = 42, /**<  */
  kTopEarlgreyMuxedPadsIor10 = 43, /**<  */
  kTopEarlgreyMuxedPadsIor11 = 44, /**<  */
  kTopEarlgreyMuxedPadsIor12 = 45, /**<  */
  kTopEarlgreyMuxedPadsIor13 = 46, /**<  */
  kTopEarlgreyMuxedPadsLast = 46, /**< \internal Last valid muxed pad */
} top_earlgrey_muxed_pads_t;

/**
 * Power Manager Wakeup Signals
 */
typedef enum top_earlgrey_power_manager_wake_ups {
  kTopEarlgreyPowerManagerWakeUpsSysrstCtrlAonWkupReq = 0, /**<  */
  kTopEarlgreyPowerManagerWakeUpsPinmuxAonPinWkupReq = 1, /**<  */
  kTopEarlgreyPowerManagerWakeUpsPinmuxAonUsbWkupReq = 2, /**<  */
  kTopEarlgreyPowerManagerWakeUpsAonTimerAonWkupReq = 3, /**<  */
  kTopEarlgreyPowerManagerWakeUpsLast = 3, /**< \internal Last valid pwrmgr wakeup signal */
} top_earlgrey_power_manager_wake_ups_t;

/**
 * Reset Manager Software Controlled Resets
 */
typedef enum top_earlgrey_reset_manager_sw_resets {
  kTopEarlgreyResetManagerSwResetsSpiDevice = 0, /**<  */
  kTopEarlgreyResetManagerSwResetsSpiHost0 = 1, /**<  */
  kTopEarlgreyResetManagerSwResetsSpiHost1 = 2, /**<  */
  kTopEarlgreyResetManagerSwResetsUsb = 3, /**<  */
  kTopEarlgreyResetManagerSwResetsUsbAon = 4, /**<  */
  kTopEarlgreyResetManagerSwResetsI2c0 = 5, /**<  */
  kTopEarlgreyResetManagerSwResetsI2c1 = 6, /**<  */
  kTopEarlgreyResetManagerSwResetsI2c2 = 7, /**<  */
  kTopEarlgreyResetManagerSwResetsLast = 7, /**< \internal Last valid rstmgr software reset request */
} top_earlgrey_reset_manager_sw_resets_t;

/**
 * Power Manager Reset Request Signals
 */
typedef enum top_earlgrey_power_manager_reset_requests {
  kTopEarlgreyPowerManagerResetRequestsSysrstCtrlAonRstReq = 0, /**<  */
  kTopEarlgreyPowerManagerResetRequestsAonTimerAonAonTimerRstReq = 1, /**<  */
  kTopEarlgreyPowerManagerResetRequestsLast = 1, /**< \internal Last valid pwrmgr reset_request signal */
} top_earlgrey_power_manager_reset_requests_t;

/**
 * Clock Manager Software-Controlled ("Gated") Clocks.
 *
 * The Software has full control over these clocks.
 */
typedef enum top_earlgrey_gateable_clocks {
  kTopEarlgreyGateableClocksIoDiv4Peri = 0, /**< Clock clk_io_div4_peri in group peri */
  kTopEarlgreyGateableClocksIoPeri = 1, /**< Clock clk_io_peri in group peri */
  kTopEarlgreyGateableClocksIoDiv2Peri = 2, /**< Clock clk_io_div2_peri in group peri */
  kTopEarlgreyGateableClocksUsbPeri = 3, /**< Clock clk_usb_peri in group peri */
  kTopEarlgreyGateableClocksLast = 3, /**< \internal Last Valid Gateable Clock */
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

/**
 * MMIO Region
 *
 * MMIO region excludes any memory that is separate from the module
 * configuration space, i.e. ROM, main SRAM, and flash are excluded but
 * retention SRAM, spi_device memory, or usbdev memory are included.
 */
#define TOP_EARLGREY_MMIO_BASE_ADDR 0x10000u
#define TOP_EARLGREY_MMIO_SIZE_BYTES 0xCFFF0000u

// Header Extern Guard
#ifdef __cplusplus
}  // extern "C"
#endif

#endif  // OPENTITAN_HW_TOP_EARLGREY_SW_AUTOGEN_TOP_EARLGREY_H_
