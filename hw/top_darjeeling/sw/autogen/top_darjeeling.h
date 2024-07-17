// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_TOP_DARJEELING_SW_AUTOGEN_TOP_DARJEELING_H_
#define OPENTITAN_HW_TOP_DARJEELING_SW_AUTOGEN_TOP_DARJEELING_H_

#include "top_darjeeling_flash_ctrl_dummy.h"
#include "top_darjeeling_keymgr_dummy.h"

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
 * Peripheral base address for uart0 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_UART0_BASE_ADDR 0x30010000u

/**
 * Peripheral size for uart0 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_UART0_BASE_ADDR and
 * `TOP_DARJEELING_UART0_BASE_ADDR + TOP_DARJEELING_UART0_SIZE_BYTES`.
 */
#define TOP_DARJEELING_UART0_SIZE_BYTES 0x40u

/**
 * Peripheral base address for gpio in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_GPIO_BASE_ADDR 0x30000000u

/**
 * Peripheral size for gpio in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_GPIO_BASE_ADDR and
 * `TOP_DARJEELING_GPIO_BASE_ADDR + TOP_DARJEELING_GPIO_SIZE_BYTES`.
 */
#define TOP_DARJEELING_GPIO_SIZE_BYTES 0x80u

/**
 * Peripheral base address for spi_device in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_SPI_DEVICE_BASE_ADDR 0x30310000u

/**
 * Peripheral size for spi_device in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_SPI_DEVICE_BASE_ADDR and
 * `TOP_DARJEELING_SPI_DEVICE_BASE_ADDR + TOP_DARJEELING_SPI_DEVICE_SIZE_BYTES`.
 */
#define TOP_DARJEELING_SPI_DEVICE_SIZE_BYTES 0x2000u

/**
 * Peripheral base address for i2c0 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_I2C0_BASE_ADDR 0x30080000u

/**
 * Peripheral size for i2c0 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_I2C0_BASE_ADDR and
 * `TOP_DARJEELING_I2C0_BASE_ADDR + TOP_DARJEELING_I2C0_SIZE_BYTES`.
 */
#define TOP_DARJEELING_I2C0_SIZE_BYTES 0x80u

/**
 * Peripheral base address for rv_timer in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_RV_TIMER_BASE_ADDR 0x30100000u

/**
 * Peripheral size for rv_timer in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_RV_TIMER_BASE_ADDR and
 * `TOP_DARJEELING_RV_TIMER_BASE_ADDR + TOP_DARJEELING_RV_TIMER_SIZE_BYTES`.
 */
#define TOP_DARJEELING_RV_TIMER_SIZE_BYTES 0x200u

/**
 * Peripheral base address for core device on otp_ctrl in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_OTP_CTRL_CORE_BASE_ADDR 0x30130000u

/**
 * Peripheral size for core device on otp_ctrl in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_OTP_CTRL_CORE_BASE_ADDR and
 * `TOP_DARJEELING_OTP_CTRL_CORE_BASE_ADDR + TOP_DARJEELING_OTP_CTRL_CORE_SIZE_BYTES`.
 */
#define TOP_DARJEELING_OTP_CTRL_CORE_SIZE_BYTES 0x8000u

/**
 * Peripheral base address for prim device on otp_ctrl in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_OTP_CTRL_PRIM_BASE_ADDR 0x30138000u

/**
 * Peripheral size for prim device on otp_ctrl in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_OTP_CTRL_PRIM_BASE_ADDR and
 * `TOP_DARJEELING_OTP_CTRL_PRIM_BASE_ADDR + TOP_DARJEELING_OTP_CTRL_PRIM_SIZE_BYTES`.
 */
#define TOP_DARJEELING_OTP_CTRL_PRIM_SIZE_BYTES 0x20u

/**
 * Peripheral base address for regs device on lc_ctrl in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_LC_CTRL_REGS_BASE_ADDR 0x30140000u

/**
 * Peripheral size for regs device on lc_ctrl in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_LC_CTRL_REGS_BASE_ADDR and
 * `TOP_DARJEELING_LC_CTRL_REGS_BASE_ADDR + TOP_DARJEELING_LC_CTRL_REGS_SIZE_BYTES`.
 */
#define TOP_DARJEELING_LC_CTRL_REGS_SIZE_BYTES 0x100u

/**
 * Peripheral base address for alert_handler in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_ALERT_HANDLER_BASE_ADDR 0x30150000u

/**
 * Peripheral size for alert_handler in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_ALERT_HANDLER_BASE_ADDR and
 * `TOP_DARJEELING_ALERT_HANDLER_BASE_ADDR + TOP_DARJEELING_ALERT_HANDLER_SIZE_BYTES`.
 */
#define TOP_DARJEELING_ALERT_HANDLER_SIZE_BYTES 0x800u

/**
 * Peripheral base address for spi_host0 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_SPI_HOST0_BASE_ADDR 0x30300000u

/**
 * Peripheral size for spi_host0 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_SPI_HOST0_BASE_ADDR and
 * `TOP_DARJEELING_SPI_HOST0_BASE_ADDR + TOP_DARJEELING_SPI_HOST0_SIZE_BYTES`.
 */
#define TOP_DARJEELING_SPI_HOST0_SIZE_BYTES 0x40u

/**
 * Peripheral base address for pwrmgr_aon in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_PWRMGR_AON_BASE_ADDR 0x30400000u

/**
 * Peripheral size for pwrmgr_aon in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_PWRMGR_AON_BASE_ADDR and
 * `TOP_DARJEELING_PWRMGR_AON_BASE_ADDR + TOP_DARJEELING_PWRMGR_AON_SIZE_BYTES`.
 */
#define TOP_DARJEELING_PWRMGR_AON_SIZE_BYTES 0x80u

/**
 * Peripheral base address for rstmgr_aon in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_RSTMGR_AON_BASE_ADDR 0x30410000u

/**
 * Peripheral size for rstmgr_aon in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_RSTMGR_AON_BASE_ADDR and
 * `TOP_DARJEELING_RSTMGR_AON_BASE_ADDR + TOP_DARJEELING_RSTMGR_AON_SIZE_BYTES`.
 */
#define TOP_DARJEELING_RSTMGR_AON_SIZE_BYTES 0x80u

/**
 * Peripheral base address for clkmgr_aon in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_CLKMGR_AON_BASE_ADDR 0x30420000u

/**
 * Peripheral size for clkmgr_aon in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_CLKMGR_AON_BASE_ADDR and
 * `TOP_DARJEELING_CLKMGR_AON_BASE_ADDR + TOP_DARJEELING_CLKMGR_AON_SIZE_BYTES`.
 */
#define TOP_DARJEELING_CLKMGR_AON_SIZE_BYTES 0x80u

/**
 * Peripheral base address for pinmux_aon in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_PINMUX_AON_BASE_ADDR 0x30460000u

/**
 * Peripheral size for pinmux_aon in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_PINMUX_AON_BASE_ADDR and
 * `TOP_DARJEELING_PINMUX_AON_BASE_ADDR + TOP_DARJEELING_PINMUX_AON_SIZE_BYTES`.
 */
#define TOP_DARJEELING_PINMUX_AON_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for aon_timer_aon in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_AON_TIMER_AON_BASE_ADDR 0x30470000u

/**
 * Peripheral size for aon_timer_aon in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_AON_TIMER_AON_BASE_ADDR and
 * `TOP_DARJEELING_AON_TIMER_AON_BASE_ADDR + TOP_DARJEELING_AON_TIMER_AON_SIZE_BYTES`.
 */
#define TOP_DARJEELING_AON_TIMER_AON_SIZE_BYTES 0x40u

/**
 * Peripheral base address for ast in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_AST_BASE_ADDR 0x30480000u

/**
 * Peripheral size for ast in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_AST_BASE_ADDR and
 * `TOP_DARJEELING_AST_BASE_ADDR + TOP_DARJEELING_AST_SIZE_BYTES`.
 */
#define TOP_DARJEELING_AST_SIZE_BYTES 0x400u

/**
 * Peripheral base address for sensor_ctrl in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_SENSOR_CTRL_BASE_ADDR 0x30020000u

/**
 * Peripheral size for sensor_ctrl in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_SENSOR_CTRL_BASE_ADDR and
 * `TOP_DARJEELING_SENSOR_CTRL_BASE_ADDR + TOP_DARJEELING_SENSOR_CTRL_SIZE_BYTES`.
 */
#define TOP_DARJEELING_SENSOR_CTRL_SIZE_BYTES 0x40u

/**
 * Peripheral base address for core device on soc_proxy in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_SOC_PROXY_CORE_BASE_ADDR 0x22030000u

/**
 * Peripheral size for core device on soc_proxy in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_SOC_PROXY_CORE_BASE_ADDR and
 * `TOP_DARJEELING_SOC_PROXY_CORE_BASE_ADDR + TOP_DARJEELING_SOC_PROXY_CORE_SIZE_BYTES`.
 */
#define TOP_DARJEELING_SOC_PROXY_CORE_SIZE_BYTES 0x10u

/**
 * Peripheral base address for ctn device on soc_proxy in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_SOC_PROXY_CTN_BASE_ADDR 0x40000000u

/**
 * Peripheral size for ctn device on soc_proxy in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_SOC_PROXY_CTN_BASE_ADDR and
 * `TOP_DARJEELING_SOC_PROXY_CTN_BASE_ADDR + TOP_DARJEELING_SOC_PROXY_CTN_SIZE_BYTES`.
 */
#define TOP_DARJEELING_SOC_PROXY_CTN_SIZE_BYTES 0x40000000u

/**
 * Peripheral base address for regs device on sram_ctrl_ret_aon in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_SRAM_CTRL_RET_AON_REGS_BASE_ADDR 0x30500000u

/**
 * Peripheral size for regs device on sram_ctrl_ret_aon in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_SRAM_CTRL_RET_AON_REGS_BASE_ADDR and
 * `TOP_DARJEELING_SRAM_CTRL_RET_AON_REGS_BASE_ADDR + TOP_DARJEELING_SRAM_CTRL_RET_AON_REGS_SIZE_BYTES`.
 */
#define TOP_DARJEELING_SRAM_CTRL_RET_AON_REGS_SIZE_BYTES 0x20u

/**
 * Peripheral base address for ram device on sram_ctrl_ret_aon in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_SRAM_CTRL_RET_AON_RAM_BASE_ADDR 0x30600000u

/**
 * Peripheral size for ram device on sram_ctrl_ret_aon in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_SRAM_CTRL_RET_AON_RAM_BASE_ADDR and
 * `TOP_DARJEELING_SRAM_CTRL_RET_AON_RAM_BASE_ADDR + TOP_DARJEELING_SRAM_CTRL_RET_AON_RAM_SIZE_BYTES`.
 */
#define TOP_DARJEELING_SRAM_CTRL_RET_AON_RAM_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for regs device on rv_dm in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_RV_DM_REGS_BASE_ADDR 0x21200000u

/**
 * Peripheral size for regs device on rv_dm in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_RV_DM_REGS_BASE_ADDR and
 * `TOP_DARJEELING_RV_DM_REGS_BASE_ADDR + TOP_DARJEELING_RV_DM_REGS_SIZE_BYTES`.
 */
#define TOP_DARJEELING_RV_DM_REGS_SIZE_BYTES 0x4u

/**
 * Peripheral base address for mem device on rv_dm in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_RV_DM_MEM_BASE_ADDR 0x40000u

/**
 * Peripheral size for mem device on rv_dm in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_RV_DM_MEM_BASE_ADDR and
 * `TOP_DARJEELING_RV_DM_MEM_BASE_ADDR + TOP_DARJEELING_RV_DM_MEM_SIZE_BYTES`.
 */
#define TOP_DARJEELING_RV_DM_MEM_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for rv_plic in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_RV_PLIC_BASE_ADDR 0x28000000u

/**
 * Peripheral size for rv_plic in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_RV_PLIC_BASE_ADDR and
 * `TOP_DARJEELING_RV_PLIC_BASE_ADDR + TOP_DARJEELING_RV_PLIC_SIZE_BYTES`.
 */
#define TOP_DARJEELING_RV_PLIC_SIZE_BYTES 0x8000000u

/**
 * Peripheral base address for aes in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_AES_BASE_ADDR 0x21100000u

/**
 * Peripheral size for aes in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_AES_BASE_ADDR and
 * `TOP_DARJEELING_AES_BASE_ADDR + TOP_DARJEELING_AES_SIZE_BYTES`.
 */
#define TOP_DARJEELING_AES_SIZE_BYTES 0x100u

/**
 * Peripheral base address for hmac in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_HMAC_BASE_ADDR 0x21110000u

/**
 * Peripheral size for hmac in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_HMAC_BASE_ADDR and
 * `TOP_DARJEELING_HMAC_BASE_ADDR + TOP_DARJEELING_HMAC_SIZE_BYTES`.
 */
#define TOP_DARJEELING_HMAC_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for kmac in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_KMAC_BASE_ADDR 0x21120000u

/**
 * Peripheral size for kmac in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_KMAC_BASE_ADDR and
 * `TOP_DARJEELING_KMAC_BASE_ADDR + TOP_DARJEELING_KMAC_SIZE_BYTES`.
 */
#define TOP_DARJEELING_KMAC_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for otbn in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_OTBN_BASE_ADDR 0x21130000u

/**
 * Peripheral size for otbn in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_OTBN_BASE_ADDR and
 * `TOP_DARJEELING_OTBN_BASE_ADDR + TOP_DARJEELING_OTBN_SIZE_BYTES`.
 */
#define TOP_DARJEELING_OTBN_SIZE_BYTES 0x10000u

/**
 * Peripheral base address for keymgr_dpe in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_KEYMGR_DPE_BASE_ADDR 0x21140000u

/**
 * Peripheral size for keymgr_dpe in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_KEYMGR_DPE_BASE_ADDR and
 * `TOP_DARJEELING_KEYMGR_DPE_BASE_ADDR + TOP_DARJEELING_KEYMGR_DPE_SIZE_BYTES`.
 */
#define TOP_DARJEELING_KEYMGR_DPE_SIZE_BYTES 0x100u

/**
 * Peripheral base address for csrng in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_CSRNG_BASE_ADDR 0x21150000u

/**
 * Peripheral size for csrng in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_CSRNG_BASE_ADDR and
 * `TOP_DARJEELING_CSRNG_BASE_ADDR + TOP_DARJEELING_CSRNG_SIZE_BYTES`.
 */
#define TOP_DARJEELING_CSRNG_SIZE_BYTES 0x80u

/**
 * Peripheral base address for edn0 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_EDN0_BASE_ADDR 0x21170000u

/**
 * Peripheral size for edn0 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_EDN0_BASE_ADDR and
 * `TOP_DARJEELING_EDN0_BASE_ADDR + TOP_DARJEELING_EDN0_SIZE_BYTES`.
 */
#define TOP_DARJEELING_EDN0_SIZE_BYTES 0x80u

/**
 * Peripheral base address for edn1 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_EDN1_BASE_ADDR 0x21180000u

/**
 * Peripheral size for edn1 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_EDN1_BASE_ADDR and
 * `TOP_DARJEELING_EDN1_BASE_ADDR + TOP_DARJEELING_EDN1_SIZE_BYTES`.
 */
#define TOP_DARJEELING_EDN1_SIZE_BYTES 0x80u

/**
 * Peripheral base address for regs device on sram_ctrl_main in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_SRAM_CTRL_MAIN_REGS_BASE_ADDR 0x211C0000u

/**
 * Peripheral size for regs device on sram_ctrl_main in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_SRAM_CTRL_MAIN_REGS_BASE_ADDR and
 * `TOP_DARJEELING_SRAM_CTRL_MAIN_REGS_BASE_ADDR + TOP_DARJEELING_SRAM_CTRL_MAIN_REGS_SIZE_BYTES`.
 */
#define TOP_DARJEELING_SRAM_CTRL_MAIN_REGS_SIZE_BYTES 0x20u

/**
 * Peripheral base address for ram device on sram_ctrl_main in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_SRAM_CTRL_MAIN_RAM_BASE_ADDR 0x10000000u

/**
 * Peripheral size for ram device on sram_ctrl_main in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_SRAM_CTRL_MAIN_RAM_BASE_ADDR and
 * `TOP_DARJEELING_SRAM_CTRL_MAIN_RAM_BASE_ADDR + TOP_DARJEELING_SRAM_CTRL_MAIN_RAM_SIZE_BYTES`.
 */
#define TOP_DARJEELING_SRAM_CTRL_MAIN_RAM_SIZE_BYTES 0x10000u

/**
 * Peripheral base address for regs device on sram_ctrl_mbox in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_SRAM_CTRL_MBOX_REGS_BASE_ADDR 0x211D0000u

/**
 * Peripheral size for regs device on sram_ctrl_mbox in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_SRAM_CTRL_MBOX_REGS_BASE_ADDR and
 * `TOP_DARJEELING_SRAM_CTRL_MBOX_REGS_BASE_ADDR + TOP_DARJEELING_SRAM_CTRL_MBOX_REGS_SIZE_BYTES`.
 */
#define TOP_DARJEELING_SRAM_CTRL_MBOX_REGS_SIZE_BYTES 0x20u

/**
 * Peripheral base address for ram device on sram_ctrl_mbox in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_SRAM_CTRL_MBOX_RAM_BASE_ADDR 0x11000000u

/**
 * Peripheral size for ram device on sram_ctrl_mbox in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_SRAM_CTRL_MBOX_RAM_BASE_ADDR and
 * `TOP_DARJEELING_SRAM_CTRL_MBOX_RAM_BASE_ADDR + TOP_DARJEELING_SRAM_CTRL_MBOX_RAM_SIZE_BYTES`.
 */
#define TOP_DARJEELING_SRAM_CTRL_MBOX_RAM_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for regs device on rom_ctrl0 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_ROM_CTRL0_REGS_BASE_ADDR 0x211E0000u

/**
 * Peripheral size for regs device on rom_ctrl0 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_ROM_CTRL0_REGS_BASE_ADDR and
 * `TOP_DARJEELING_ROM_CTRL0_REGS_BASE_ADDR + TOP_DARJEELING_ROM_CTRL0_REGS_SIZE_BYTES`.
 */
#define TOP_DARJEELING_ROM_CTRL0_REGS_SIZE_BYTES 0x80u

/**
 * Peripheral base address for rom device on rom_ctrl0 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_ROM_CTRL0_ROM_BASE_ADDR 0x8000u

/**
 * Peripheral size for rom device on rom_ctrl0 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_ROM_CTRL0_ROM_BASE_ADDR and
 * `TOP_DARJEELING_ROM_CTRL0_ROM_BASE_ADDR + TOP_DARJEELING_ROM_CTRL0_ROM_SIZE_BYTES`.
 */
#define TOP_DARJEELING_ROM_CTRL0_ROM_SIZE_BYTES 0x8000u

/**
 * Peripheral base address for regs device on rom_ctrl1 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_ROM_CTRL1_REGS_BASE_ADDR 0x211E1000u

/**
 * Peripheral size for regs device on rom_ctrl1 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_ROM_CTRL1_REGS_BASE_ADDR and
 * `TOP_DARJEELING_ROM_CTRL1_REGS_BASE_ADDR + TOP_DARJEELING_ROM_CTRL1_REGS_SIZE_BYTES`.
 */
#define TOP_DARJEELING_ROM_CTRL1_REGS_SIZE_BYTES 0x80u

/**
 * Peripheral base address for rom device on rom_ctrl1 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_ROM_CTRL1_ROM_BASE_ADDR 0x20000u

/**
 * Peripheral size for rom device on rom_ctrl1 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_ROM_CTRL1_ROM_BASE_ADDR and
 * `TOP_DARJEELING_ROM_CTRL1_ROM_BASE_ADDR + TOP_DARJEELING_ROM_CTRL1_ROM_SIZE_BYTES`.
 */
#define TOP_DARJEELING_ROM_CTRL1_ROM_SIZE_BYTES 0x10000u

/**
 * Peripheral base address for dma in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_DMA_BASE_ADDR 0x22010000u

/**
 * Peripheral size for dma in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_DMA_BASE_ADDR and
 * `TOP_DARJEELING_DMA_BASE_ADDR + TOP_DARJEELING_DMA_SIZE_BYTES`.
 */
#define TOP_DARJEELING_DMA_SIZE_BYTES 0x200u

/**
 * Peripheral base address for core device on mbx0 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_MBX0_CORE_BASE_ADDR 0x22000000u

/**
 * Peripheral size for core device on mbx0 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_MBX0_CORE_BASE_ADDR and
 * `TOP_DARJEELING_MBX0_CORE_BASE_ADDR + TOP_DARJEELING_MBX0_CORE_SIZE_BYTES`.
 */
#define TOP_DARJEELING_MBX0_CORE_SIZE_BYTES 0x80u

/**
 * Peripheral base address for core device on mbx1 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_MBX1_CORE_BASE_ADDR 0x22000100u

/**
 * Peripheral size for core device on mbx1 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_MBX1_CORE_BASE_ADDR and
 * `TOP_DARJEELING_MBX1_CORE_BASE_ADDR + TOP_DARJEELING_MBX1_CORE_SIZE_BYTES`.
 */
#define TOP_DARJEELING_MBX1_CORE_SIZE_BYTES 0x80u

/**
 * Peripheral base address for core device on mbx2 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_MBX2_CORE_BASE_ADDR 0x22000200u

/**
 * Peripheral size for core device on mbx2 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_MBX2_CORE_BASE_ADDR and
 * `TOP_DARJEELING_MBX2_CORE_BASE_ADDR + TOP_DARJEELING_MBX2_CORE_SIZE_BYTES`.
 */
#define TOP_DARJEELING_MBX2_CORE_SIZE_BYTES 0x80u

/**
 * Peripheral base address for core device on mbx3 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_MBX3_CORE_BASE_ADDR 0x22000300u

/**
 * Peripheral size for core device on mbx3 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_MBX3_CORE_BASE_ADDR and
 * `TOP_DARJEELING_MBX3_CORE_BASE_ADDR + TOP_DARJEELING_MBX3_CORE_SIZE_BYTES`.
 */
#define TOP_DARJEELING_MBX3_CORE_SIZE_BYTES 0x80u

/**
 * Peripheral base address for core device on mbx4 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_MBX4_CORE_BASE_ADDR 0x22000400u

/**
 * Peripheral size for core device on mbx4 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_MBX4_CORE_BASE_ADDR and
 * `TOP_DARJEELING_MBX4_CORE_BASE_ADDR + TOP_DARJEELING_MBX4_CORE_SIZE_BYTES`.
 */
#define TOP_DARJEELING_MBX4_CORE_SIZE_BYTES 0x80u

/**
 * Peripheral base address for core device on mbx5 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_MBX5_CORE_BASE_ADDR 0x22000500u

/**
 * Peripheral size for core device on mbx5 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_MBX5_CORE_BASE_ADDR and
 * `TOP_DARJEELING_MBX5_CORE_BASE_ADDR + TOP_DARJEELING_MBX5_CORE_SIZE_BYTES`.
 */
#define TOP_DARJEELING_MBX5_CORE_SIZE_BYTES 0x80u

/**
 * Peripheral base address for core device on mbx6 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_MBX6_CORE_BASE_ADDR 0x22000600u

/**
 * Peripheral size for core device on mbx6 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_MBX6_CORE_BASE_ADDR and
 * `TOP_DARJEELING_MBX6_CORE_BASE_ADDR + TOP_DARJEELING_MBX6_CORE_SIZE_BYTES`.
 */
#define TOP_DARJEELING_MBX6_CORE_SIZE_BYTES 0x80u

/**
 * Peripheral base address for core device on mbx_jtag in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_MBX_JTAG_CORE_BASE_ADDR 0x22000800u

/**
 * Peripheral size for core device on mbx_jtag in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_MBX_JTAG_CORE_BASE_ADDR and
 * `TOP_DARJEELING_MBX_JTAG_CORE_BASE_ADDR + TOP_DARJEELING_MBX_JTAG_CORE_SIZE_BYTES`.
 */
#define TOP_DARJEELING_MBX_JTAG_CORE_SIZE_BYTES 0x80u

/**
 * Peripheral base address for core device on mbx_pcie0 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_MBX_PCIE0_CORE_BASE_ADDR 0x22040000u

/**
 * Peripheral size for core device on mbx_pcie0 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_MBX_PCIE0_CORE_BASE_ADDR and
 * `TOP_DARJEELING_MBX_PCIE0_CORE_BASE_ADDR + TOP_DARJEELING_MBX_PCIE0_CORE_SIZE_BYTES`.
 */
#define TOP_DARJEELING_MBX_PCIE0_CORE_SIZE_BYTES 0x80u

/**
 * Peripheral base address for core device on mbx_pcie1 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_MBX_PCIE1_CORE_BASE_ADDR 0x22040100u

/**
 * Peripheral size for core device on mbx_pcie1 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_MBX_PCIE1_CORE_BASE_ADDR and
 * `TOP_DARJEELING_MBX_PCIE1_CORE_BASE_ADDR + TOP_DARJEELING_MBX_PCIE1_CORE_SIZE_BYTES`.
 */
#define TOP_DARJEELING_MBX_PCIE1_CORE_SIZE_BYTES 0x80u

/**
 * Peripheral base address for cfg device on rv_core_ibex in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_RV_CORE_IBEX_CFG_BASE_ADDR 0x211F0000u

/**
 * Peripheral size for cfg device on rv_core_ibex in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_RV_CORE_IBEX_CFG_BASE_ADDR and
 * `TOP_DARJEELING_RV_CORE_IBEX_CFG_BASE_ADDR + TOP_DARJEELING_RV_CORE_IBEX_CFG_SIZE_BYTES`.
 */
#define TOP_DARJEELING_RV_CORE_IBEX_CFG_SIZE_BYTES 0x800u


/**
 * Memory base address for ctn in top darjeeling.
 */
#define TOP_DARJEELING_CTN_BASE_ADDR 0x40000000u

/**
 * Memory size for ctn in top darjeeling.
 */
#define TOP_DARJEELING_CTN_SIZE_BYTES 0x40000000u

/**
 * Memory base address for ram_ctn in top darjeeling.
 */
#define TOP_DARJEELING_RAM_CTN_BASE_ADDR 0x41000000u

/**
 * Memory size for ram_ctn in top darjeeling.
 */
#define TOP_DARJEELING_RAM_CTN_SIZE_BYTES 0x100000u
/**
 * Memory base address for ram_ret_aon in top darjeeling.
 */
#define TOP_DARJEELING_RAM_RET_AON_BASE_ADDR 0x30600000u

/**
 * Memory size for ram_ret_aon in top darjeeling.
 */
#define TOP_DARJEELING_RAM_RET_AON_SIZE_BYTES 0x1000u

/**
 * Memory base address for ram_main in top darjeeling.
 */
#define TOP_DARJEELING_RAM_MAIN_BASE_ADDR 0x10000000u

/**
 * Memory size for ram_main in top darjeeling.
 */
#define TOP_DARJEELING_RAM_MAIN_SIZE_BYTES 0x10000u

/**
 * Memory base address for ram_mbox in top darjeeling.
 */
#define TOP_DARJEELING_RAM_MBOX_BASE_ADDR 0x11000000u

/**
 * Memory size for ram_mbox in top darjeeling.
 */
#define TOP_DARJEELING_RAM_MBOX_SIZE_BYTES 0x1000u

/**
 * Memory base address for rom0 in top darjeeling.
 */
#define TOP_DARJEELING_ROM0_BASE_ADDR 0x8000u

/**
 * Memory size for rom0 in top darjeeling.
 */
#define TOP_DARJEELING_ROM0_SIZE_BYTES 0x8000u

/**
 * Memory base address for rom1 in top darjeeling.
 */
#define TOP_DARJEELING_ROM1_BASE_ADDR 0x20000u

/**
 * Memory size for rom1 in top darjeeling.
 */
#define TOP_DARJEELING_ROM1_SIZE_BYTES 0x10000u


/**
 * PLIC Interrupt Source Peripheral.
 *
 * Enumeration used to determine which peripheral asserted the corresponding
 * interrupt.
 */
typedef enum top_darjeeling_plic_peripheral {
  kTopDarjeelingPlicPeripheralUnknown = 0, /**< Unknown Peripheral */
  kTopDarjeelingPlicPeripheralUart0 = 1, /**< uart0 */
  kTopDarjeelingPlicPeripheralGpio = 2, /**< gpio */
  kTopDarjeelingPlicPeripheralSpiDevice = 3, /**< spi_device */
  kTopDarjeelingPlicPeripheralI2c0 = 4, /**< i2c0 */
  kTopDarjeelingPlicPeripheralRvTimer = 5, /**< rv_timer */
  kTopDarjeelingPlicPeripheralOtpCtrl = 6, /**< otp_ctrl */
  kTopDarjeelingPlicPeripheralAlertHandler = 7, /**< alert_handler */
  kTopDarjeelingPlicPeripheralSpiHost0 = 8, /**< spi_host0 */
  kTopDarjeelingPlicPeripheralPwrmgrAon = 9, /**< pwrmgr_aon */
  kTopDarjeelingPlicPeripheralAonTimerAon = 10, /**< aon_timer_aon */
  kTopDarjeelingPlicPeripheralSensorCtrl = 11, /**< sensor_ctrl */
  kTopDarjeelingPlicPeripheralSocProxy = 12, /**< soc_proxy */
  kTopDarjeelingPlicPeripheralHmac = 13, /**< hmac */
  kTopDarjeelingPlicPeripheralKmac = 14, /**< kmac */
  kTopDarjeelingPlicPeripheralOtbn = 15, /**< otbn */
  kTopDarjeelingPlicPeripheralKeymgrDpe = 16, /**< keymgr_dpe */
  kTopDarjeelingPlicPeripheralCsrng = 17, /**< csrng */
  kTopDarjeelingPlicPeripheralEdn0 = 18, /**< edn0 */
  kTopDarjeelingPlicPeripheralEdn1 = 19, /**< edn1 */
  kTopDarjeelingPlicPeripheralDma = 20, /**< dma */
  kTopDarjeelingPlicPeripheralMbx0 = 21, /**< mbx0 */
  kTopDarjeelingPlicPeripheralMbx1 = 22, /**< mbx1 */
  kTopDarjeelingPlicPeripheralMbx2 = 23, /**< mbx2 */
  kTopDarjeelingPlicPeripheralMbx3 = 24, /**< mbx3 */
  kTopDarjeelingPlicPeripheralMbx4 = 25, /**< mbx4 */
  kTopDarjeelingPlicPeripheralMbx5 = 26, /**< mbx5 */
  kTopDarjeelingPlicPeripheralMbx6 = 27, /**< mbx6 */
  kTopDarjeelingPlicPeripheralMbxJtag = 28, /**< mbx_jtag */
  kTopDarjeelingPlicPeripheralMbxPcie0 = 29, /**< mbx_pcie0 */
  kTopDarjeelingPlicPeripheralMbxPcie1 = 30, /**< mbx_pcie1 */
  kTopDarjeelingPlicPeripheralLast = 30, /**< \internal Final PLIC peripheral */
} top_darjeeling_plic_peripheral_t;

/**
 * PLIC Interrupt Source.
 *
 * Enumeration of all PLIC interrupt sources. The interrupt sources belonging to
 * the same peripheral are guaranteed to be consecutive.
 */
typedef enum top_darjeeling_plic_irq_id {
  kTopDarjeelingPlicIrqIdNone = 0, /**< No Interrupt */
  kTopDarjeelingPlicIrqIdUart0TxWatermark = 1, /**< uart0_tx_watermark */
  kTopDarjeelingPlicIrqIdUart0RxWatermark = 2, /**< uart0_rx_watermark */
  kTopDarjeelingPlicIrqIdUart0TxEmpty = 3, /**< uart0_tx_empty */
  kTopDarjeelingPlicIrqIdUart0RxOverflow = 4, /**< uart0_rx_overflow */
  kTopDarjeelingPlicIrqIdUart0RxFrameErr = 5, /**< uart0_rx_frame_err */
  kTopDarjeelingPlicIrqIdUart0RxBreakErr = 6, /**< uart0_rx_break_err */
  kTopDarjeelingPlicIrqIdUart0RxTimeout = 7, /**< uart0_rx_timeout */
  kTopDarjeelingPlicIrqIdUart0RxParityErr = 8, /**< uart0_rx_parity_err */
  kTopDarjeelingPlicIrqIdGpioGpio0 = 9, /**< gpio_gpio 0 */
  kTopDarjeelingPlicIrqIdGpioGpio1 = 10, /**< gpio_gpio 1 */
  kTopDarjeelingPlicIrqIdGpioGpio2 = 11, /**< gpio_gpio 2 */
  kTopDarjeelingPlicIrqIdGpioGpio3 = 12, /**< gpio_gpio 3 */
  kTopDarjeelingPlicIrqIdGpioGpio4 = 13, /**< gpio_gpio 4 */
  kTopDarjeelingPlicIrqIdGpioGpio5 = 14, /**< gpio_gpio 5 */
  kTopDarjeelingPlicIrqIdGpioGpio6 = 15, /**< gpio_gpio 6 */
  kTopDarjeelingPlicIrqIdGpioGpio7 = 16, /**< gpio_gpio 7 */
  kTopDarjeelingPlicIrqIdGpioGpio8 = 17, /**< gpio_gpio 8 */
  kTopDarjeelingPlicIrqIdGpioGpio9 = 18, /**< gpio_gpio 9 */
  kTopDarjeelingPlicIrqIdGpioGpio10 = 19, /**< gpio_gpio 10 */
  kTopDarjeelingPlicIrqIdGpioGpio11 = 20, /**< gpio_gpio 11 */
  kTopDarjeelingPlicIrqIdGpioGpio12 = 21, /**< gpio_gpio 12 */
  kTopDarjeelingPlicIrqIdGpioGpio13 = 22, /**< gpio_gpio 13 */
  kTopDarjeelingPlicIrqIdGpioGpio14 = 23, /**< gpio_gpio 14 */
  kTopDarjeelingPlicIrqIdGpioGpio15 = 24, /**< gpio_gpio 15 */
  kTopDarjeelingPlicIrqIdGpioGpio16 = 25, /**< gpio_gpio 16 */
  kTopDarjeelingPlicIrqIdGpioGpio17 = 26, /**< gpio_gpio 17 */
  kTopDarjeelingPlicIrqIdGpioGpio18 = 27, /**< gpio_gpio 18 */
  kTopDarjeelingPlicIrqIdGpioGpio19 = 28, /**< gpio_gpio 19 */
  kTopDarjeelingPlicIrqIdGpioGpio20 = 29, /**< gpio_gpio 20 */
  kTopDarjeelingPlicIrqIdGpioGpio21 = 30, /**< gpio_gpio 21 */
  kTopDarjeelingPlicIrqIdGpioGpio22 = 31, /**< gpio_gpio 22 */
  kTopDarjeelingPlicIrqIdGpioGpio23 = 32, /**< gpio_gpio 23 */
  kTopDarjeelingPlicIrqIdGpioGpio24 = 33, /**< gpio_gpio 24 */
  kTopDarjeelingPlicIrqIdGpioGpio25 = 34, /**< gpio_gpio 25 */
  kTopDarjeelingPlicIrqIdGpioGpio26 = 35, /**< gpio_gpio 26 */
  kTopDarjeelingPlicIrqIdGpioGpio27 = 36, /**< gpio_gpio 27 */
  kTopDarjeelingPlicIrqIdGpioGpio28 = 37, /**< gpio_gpio 28 */
  kTopDarjeelingPlicIrqIdGpioGpio29 = 38, /**< gpio_gpio 29 */
  kTopDarjeelingPlicIrqIdGpioGpio30 = 39, /**< gpio_gpio 30 */
  kTopDarjeelingPlicIrqIdGpioGpio31 = 40, /**< gpio_gpio 31 */
  kTopDarjeelingPlicIrqIdSpiDeviceGenericRxFull = 41, /**< spi_device_generic_rx_full */
  kTopDarjeelingPlicIrqIdSpiDeviceGenericRxWatermark = 42, /**< spi_device_generic_rx_watermark */
  kTopDarjeelingPlicIrqIdSpiDeviceGenericTxWatermark = 43, /**< spi_device_generic_tx_watermark */
  kTopDarjeelingPlicIrqIdSpiDeviceGenericRxError = 44, /**< spi_device_generic_rx_error */
  kTopDarjeelingPlicIrqIdSpiDeviceGenericRxOverflow = 45, /**< spi_device_generic_rx_overflow */
  kTopDarjeelingPlicIrqIdSpiDeviceGenericTxUnderflow = 46, /**< spi_device_generic_tx_underflow */
  kTopDarjeelingPlicIrqIdSpiDeviceUploadCmdfifoNotEmpty = 47, /**< spi_device_upload_cmdfifo_not_empty */
  kTopDarjeelingPlicIrqIdSpiDeviceUploadPayloadNotEmpty = 48, /**< spi_device_upload_payload_not_empty */
  kTopDarjeelingPlicIrqIdSpiDeviceUploadPayloadOverflow = 49, /**< spi_device_upload_payload_overflow */
  kTopDarjeelingPlicIrqIdSpiDeviceReadbufWatermark = 50, /**< spi_device_readbuf_watermark */
  kTopDarjeelingPlicIrqIdSpiDeviceReadbufFlip = 51, /**< spi_device_readbuf_flip */
  kTopDarjeelingPlicIrqIdSpiDeviceTpmHeaderNotEmpty = 52, /**< spi_device_tpm_header_not_empty */
  kTopDarjeelingPlicIrqIdI2c0FmtThreshold = 53, /**< i2c0_fmt_threshold */
  kTopDarjeelingPlicIrqIdI2c0RxThreshold = 54, /**< i2c0_rx_threshold */
  kTopDarjeelingPlicIrqIdI2c0FmtOverflow = 55, /**< i2c0_fmt_overflow */
  kTopDarjeelingPlicIrqIdI2c0RxOverflow = 56, /**< i2c0_rx_overflow */
  kTopDarjeelingPlicIrqIdI2c0Nak = 57, /**< i2c0_nak */
  kTopDarjeelingPlicIrqIdI2c0SclInterference = 58, /**< i2c0_scl_interference */
  kTopDarjeelingPlicIrqIdI2c0SdaInterference = 59, /**< i2c0_sda_interference */
  kTopDarjeelingPlicIrqIdI2c0StretchTimeout = 60, /**< i2c0_stretch_timeout */
  kTopDarjeelingPlicIrqIdI2c0SdaUnstable = 61, /**< i2c0_sda_unstable */
  kTopDarjeelingPlicIrqIdI2c0CmdComplete = 62, /**< i2c0_cmd_complete */
  kTopDarjeelingPlicIrqIdI2c0TxStretch = 63, /**< i2c0_tx_stretch */
  kTopDarjeelingPlicIrqIdI2c0TxOverflow = 64, /**< i2c0_tx_overflow */
  kTopDarjeelingPlicIrqIdI2c0AcqFull = 65, /**< i2c0_acq_full */
  kTopDarjeelingPlicIrqIdI2c0UnexpStop = 66, /**< i2c0_unexp_stop */
  kTopDarjeelingPlicIrqIdI2c0HostTimeout = 67, /**< i2c0_host_timeout */
  kTopDarjeelingPlicIrqIdRvTimerTimerExpiredHart0Timer0 = 68, /**< rv_timer_timer_expired_hart0_timer0 */
  kTopDarjeelingPlicIrqIdOtpCtrlOtpOperationDone = 69, /**< otp_ctrl_otp_operation_done */
  kTopDarjeelingPlicIrqIdOtpCtrlOtpError = 70, /**< otp_ctrl_otp_error */
  kTopDarjeelingPlicIrqIdAlertHandlerClassa = 71, /**< alert_handler_classa */
  kTopDarjeelingPlicIrqIdAlertHandlerClassb = 72, /**< alert_handler_classb */
  kTopDarjeelingPlicIrqIdAlertHandlerClassc = 73, /**< alert_handler_classc */
  kTopDarjeelingPlicIrqIdAlertHandlerClassd = 74, /**< alert_handler_classd */
  kTopDarjeelingPlicIrqIdSpiHost0Error = 75, /**< spi_host0_error */
  kTopDarjeelingPlicIrqIdSpiHost0SpiEvent = 76, /**< spi_host0_spi_event */
  kTopDarjeelingPlicIrqIdPwrmgrAonWakeup = 77, /**< pwrmgr_aon_wakeup */
  kTopDarjeelingPlicIrqIdAonTimerAonWkupTimerExpired = 78, /**< aon_timer_aon_wkup_timer_expired */
  kTopDarjeelingPlicIrqIdAonTimerAonWdogTimerBark = 79, /**< aon_timer_aon_wdog_timer_bark */
  kTopDarjeelingPlicIrqIdSensorCtrlIoStatusChange = 80, /**< sensor_ctrl_io_status_change */
  kTopDarjeelingPlicIrqIdSensorCtrlInitStatusChange = 81, /**< sensor_ctrl_init_status_change */
  kTopDarjeelingPlicIrqIdSocProxyExternal0 = 82, /**< soc_proxy_external 0 */
  kTopDarjeelingPlicIrqIdSocProxyExternal1 = 83, /**< soc_proxy_external 1 */
  kTopDarjeelingPlicIrqIdSocProxyExternal2 = 84, /**< soc_proxy_external 2 */
  kTopDarjeelingPlicIrqIdSocProxyExternal3 = 85, /**< soc_proxy_external 3 */
  kTopDarjeelingPlicIrqIdSocProxyExternal4 = 86, /**< soc_proxy_external 4 */
  kTopDarjeelingPlicIrqIdSocProxyExternal5 = 87, /**< soc_proxy_external 5 */
  kTopDarjeelingPlicIrqIdSocProxyExternal6 = 88, /**< soc_proxy_external 6 */
  kTopDarjeelingPlicIrqIdSocProxyExternal7 = 89, /**< soc_proxy_external 7 */
  kTopDarjeelingPlicIrqIdSocProxyExternal8 = 90, /**< soc_proxy_external 8 */
  kTopDarjeelingPlicIrqIdSocProxyExternal9 = 91, /**< soc_proxy_external 9 */
  kTopDarjeelingPlicIrqIdSocProxyExternal10 = 92, /**< soc_proxy_external 10 */
  kTopDarjeelingPlicIrqIdSocProxyExternal11 = 93, /**< soc_proxy_external 11 */
  kTopDarjeelingPlicIrqIdSocProxyExternal12 = 94, /**< soc_proxy_external 12 */
  kTopDarjeelingPlicIrqIdSocProxyExternal13 = 95, /**< soc_proxy_external 13 */
  kTopDarjeelingPlicIrqIdSocProxyExternal14 = 96, /**< soc_proxy_external 14 */
  kTopDarjeelingPlicIrqIdSocProxyExternal15 = 97, /**< soc_proxy_external 15 */
  kTopDarjeelingPlicIrqIdSocProxyExternal16 = 98, /**< soc_proxy_external 16 */
  kTopDarjeelingPlicIrqIdSocProxyExternal17 = 99, /**< soc_proxy_external 17 */
  kTopDarjeelingPlicIrqIdSocProxyExternal18 = 100, /**< soc_proxy_external 18 */
  kTopDarjeelingPlicIrqIdSocProxyExternal19 = 101, /**< soc_proxy_external 19 */
  kTopDarjeelingPlicIrqIdSocProxyExternal20 = 102, /**< soc_proxy_external 20 */
  kTopDarjeelingPlicIrqIdSocProxyExternal21 = 103, /**< soc_proxy_external 21 */
  kTopDarjeelingPlicIrqIdSocProxyExternal22 = 104, /**< soc_proxy_external 22 */
  kTopDarjeelingPlicIrqIdSocProxyExternal23 = 105, /**< soc_proxy_external 23 */
  kTopDarjeelingPlicIrqIdSocProxyExternal24 = 106, /**< soc_proxy_external 24 */
  kTopDarjeelingPlicIrqIdSocProxyExternal25 = 107, /**< soc_proxy_external 25 */
  kTopDarjeelingPlicIrqIdSocProxyExternal26 = 108, /**< soc_proxy_external 26 */
  kTopDarjeelingPlicIrqIdSocProxyExternal27 = 109, /**< soc_proxy_external 27 */
  kTopDarjeelingPlicIrqIdSocProxyExternal28 = 110, /**< soc_proxy_external 28 */
  kTopDarjeelingPlicIrqIdSocProxyExternal29 = 111, /**< soc_proxy_external 29 */
  kTopDarjeelingPlicIrqIdSocProxyExternal30 = 112, /**< soc_proxy_external 30 */
  kTopDarjeelingPlicIrqIdSocProxyExternal31 = 113, /**< soc_proxy_external 31 */
  kTopDarjeelingPlicIrqIdHmacHmacDone = 114, /**< hmac_hmac_done */
  kTopDarjeelingPlicIrqIdHmacFifoEmpty = 115, /**< hmac_fifo_empty */
  kTopDarjeelingPlicIrqIdHmacHmacErr = 116, /**< hmac_hmac_err */
  kTopDarjeelingPlicIrqIdKmacKmacDone = 117, /**< kmac_kmac_done */
  kTopDarjeelingPlicIrqIdKmacFifoEmpty = 118, /**< kmac_fifo_empty */
  kTopDarjeelingPlicIrqIdKmacKmacErr = 119, /**< kmac_kmac_err */
  kTopDarjeelingPlicIrqIdOtbnDone = 120, /**< otbn_done */
  kTopDarjeelingPlicIrqIdKeymgrDpeOpDone = 121, /**< keymgr_dpe_op_done */
  kTopDarjeelingPlicIrqIdCsrngCsCmdReqDone = 122, /**< csrng_cs_cmd_req_done */
  kTopDarjeelingPlicIrqIdCsrngCsEntropyReq = 123, /**< csrng_cs_entropy_req */
  kTopDarjeelingPlicIrqIdCsrngCsHwInstExc = 124, /**< csrng_cs_hw_inst_exc */
  kTopDarjeelingPlicIrqIdCsrngCsFatalErr = 125, /**< csrng_cs_fatal_err */
  kTopDarjeelingPlicIrqIdEdn0EdnCmdReqDone = 126, /**< edn0_edn_cmd_req_done */
  kTopDarjeelingPlicIrqIdEdn0EdnFatalErr = 127, /**< edn0_edn_fatal_err */
  kTopDarjeelingPlicIrqIdEdn1EdnCmdReqDone = 128, /**< edn1_edn_cmd_req_done */
  kTopDarjeelingPlicIrqIdEdn1EdnFatalErr = 129, /**< edn1_edn_fatal_err */
  kTopDarjeelingPlicIrqIdDmaDmaDone = 130, /**< dma_dma_done */
  kTopDarjeelingPlicIrqIdDmaDmaError = 131, /**< dma_dma_error */
  kTopDarjeelingPlicIrqIdMbx0MbxReady = 132, /**< mbx0_mbx_ready */
  kTopDarjeelingPlicIrqIdMbx0MbxAbort = 133, /**< mbx0_mbx_abort */
  kTopDarjeelingPlicIrqIdMbx0MbxError = 134, /**< mbx0_mbx_error */
  kTopDarjeelingPlicIrqIdMbx1MbxReady = 135, /**< mbx1_mbx_ready */
  kTopDarjeelingPlicIrqIdMbx1MbxAbort = 136, /**< mbx1_mbx_abort */
  kTopDarjeelingPlicIrqIdMbx1MbxError = 137, /**< mbx1_mbx_error */
  kTopDarjeelingPlicIrqIdMbx2MbxReady = 138, /**< mbx2_mbx_ready */
  kTopDarjeelingPlicIrqIdMbx2MbxAbort = 139, /**< mbx2_mbx_abort */
  kTopDarjeelingPlicIrqIdMbx2MbxError = 140, /**< mbx2_mbx_error */
  kTopDarjeelingPlicIrqIdMbx3MbxReady = 141, /**< mbx3_mbx_ready */
  kTopDarjeelingPlicIrqIdMbx3MbxAbort = 142, /**< mbx3_mbx_abort */
  kTopDarjeelingPlicIrqIdMbx3MbxError = 143, /**< mbx3_mbx_error */
  kTopDarjeelingPlicIrqIdMbx4MbxReady = 144, /**< mbx4_mbx_ready */
  kTopDarjeelingPlicIrqIdMbx4MbxAbort = 145, /**< mbx4_mbx_abort */
  kTopDarjeelingPlicIrqIdMbx4MbxError = 146, /**< mbx4_mbx_error */
  kTopDarjeelingPlicIrqIdMbx5MbxReady = 147, /**< mbx5_mbx_ready */
  kTopDarjeelingPlicIrqIdMbx5MbxAbort = 148, /**< mbx5_mbx_abort */
  kTopDarjeelingPlicIrqIdMbx5MbxError = 149, /**< mbx5_mbx_error */
  kTopDarjeelingPlicIrqIdMbx6MbxReady = 150, /**< mbx6_mbx_ready */
  kTopDarjeelingPlicIrqIdMbx6MbxAbort = 151, /**< mbx6_mbx_abort */
  kTopDarjeelingPlicIrqIdMbx6MbxError = 152, /**< mbx6_mbx_error */
  kTopDarjeelingPlicIrqIdMbxJtagMbxReady = 153, /**< mbx_jtag_mbx_ready */
  kTopDarjeelingPlicIrqIdMbxJtagMbxAbort = 154, /**< mbx_jtag_mbx_abort */
  kTopDarjeelingPlicIrqIdMbxJtagMbxError = 155, /**< mbx_jtag_mbx_error */
  kTopDarjeelingPlicIrqIdMbxPcie0MbxReady = 156, /**< mbx_pcie0_mbx_ready */
  kTopDarjeelingPlicIrqIdMbxPcie0MbxAbort = 157, /**< mbx_pcie0_mbx_abort */
  kTopDarjeelingPlicIrqIdMbxPcie0MbxError = 158, /**< mbx_pcie0_mbx_error */
  kTopDarjeelingPlicIrqIdMbxPcie1MbxReady = 159, /**< mbx_pcie1_mbx_ready */
  kTopDarjeelingPlicIrqIdMbxPcie1MbxAbort = 160, /**< mbx_pcie1_mbx_abort */
  kTopDarjeelingPlicIrqIdMbxPcie1MbxError = 161, /**< mbx_pcie1_mbx_error */
  kTopDarjeelingPlicIrqIdLast = 161, /**< \internal The Last Valid Interrupt ID. */
} top_darjeeling_plic_irq_id_t;

/**
 * PLIC Interrupt Source to Peripheral Map
 *
 * This array is a mapping from `top_darjeeling_plic_irq_id_t` to
 * `top_darjeeling_plic_peripheral_t`.
 */
extern const top_darjeeling_plic_peripheral_t
    top_darjeeling_plic_interrupt_for_peripheral[162];

/**
 * PLIC Interrupt Target.
 *
 * Enumeration used to determine which set of IE, CC, threshold registers to
 * access for a given interrupt target.
 */
typedef enum top_darjeeling_plic_target {
  kTopDarjeelingPlicTargetIbex0 = 0, /**< Ibex Core 0 */
  kTopDarjeelingPlicTargetLast = 0, /**< \internal Final PLIC target */
} top_darjeeling_plic_target_t;

/**
 * Alert Handler Source Peripheral.
 *
 * Enumeration used to determine which peripheral asserted the corresponding
 * alert.
 */
typedef enum top_darjeeling_alert_peripheral {
  kTopDarjeelingAlertPeripheralUart0 = 0, /**< uart0 */
  kTopDarjeelingAlertPeripheralGpio = 1, /**< gpio */
  kTopDarjeelingAlertPeripheralSpiDevice = 2, /**< spi_device */
  kTopDarjeelingAlertPeripheralI2c0 = 3, /**< i2c0 */
  kTopDarjeelingAlertPeripheralRvTimer = 4, /**< rv_timer */
  kTopDarjeelingAlertPeripheralOtpCtrl = 5, /**< otp_ctrl */
  kTopDarjeelingAlertPeripheralLcCtrl = 6, /**< lc_ctrl */
  kTopDarjeelingAlertPeripheralSpiHost0 = 7, /**< spi_host0 */
  kTopDarjeelingAlertPeripheralPwrmgrAon = 8, /**< pwrmgr_aon */
  kTopDarjeelingAlertPeripheralRstmgrAon = 9, /**< rstmgr_aon */
  kTopDarjeelingAlertPeripheralClkmgrAon = 10, /**< clkmgr_aon */
  kTopDarjeelingAlertPeripheralPinmuxAon = 11, /**< pinmux_aon */
  kTopDarjeelingAlertPeripheralAonTimerAon = 12, /**< aon_timer_aon */
  kTopDarjeelingAlertPeripheralSensorCtrl = 13, /**< sensor_ctrl */
  kTopDarjeelingAlertPeripheralSocProxy = 14, /**< soc_proxy */
  kTopDarjeelingAlertPeripheralSramCtrlRetAon = 15, /**< sram_ctrl_ret_aon */
  kTopDarjeelingAlertPeripheralRvDm = 16, /**< rv_dm */
  kTopDarjeelingAlertPeripheralRvPlic = 17, /**< rv_plic */
  kTopDarjeelingAlertPeripheralAes = 18, /**< aes */
  kTopDarjeelingAlertPeripheralHmac = 19, /**< hmac */
  kTopDarjeelingAlertPeripheralKmac = 20, /**< kmac */
  kTopDarjeelingAlertPeripheralOtbn = 21, /**< otbn */
  kTopDarjeelingAlertPeripheralKeymgrDpe = 22, /**< keymgr_dpe */
  kTopDarjeelingAlertPeripheralCsrng = 23, /**< csrng */
  kTopDarjeelingAlertPeripheralEdn0 = 24, /**< edn0 */
  kTopDarjeelingAlertPeripheralEdn1 = 25, /**< edn1 */
  kTopDarjeelingAlertPeripheralSramCtrlMain = 26, /**< sram_ctrl_main */
  kTopDarjeelingAlertPeripheralSramCtrlMbox = 27, /**< sram_ctrl_mbox */
  kTopDarjeelingAlertPeripheralRomCtrl0 = 28, /**< rom_ctrl0 */
  kTopDarjeelingAlertPeripheralRomCtrl1 = 29, /**< rom_ctrl1 */
  kTopDarjeelingAlertPeripheralDma = 30, /**< dma */
  kTopDarjeelingAlertPeripheralMbx0 = 31, /**< mbx0 */
  kTopDarjeelingAlertPeripheralMbx1 = 32, /**< mbx1 */
  kTopDarjeelingAlertPeripheralMbx2 = 33, /**< mbx2 */
  kTopDarjeelingAlertPeripheralMbx3 = 34, /**< mbx3 */
  kTopDarjeelingAlertPeripheralMbx4 = 35, /**< mbx4 */
  kTopDarjeelingAlertPeripheralMbx5 = 36, /**< mbx5 */
  kTopDarjeelingAlertPeripheralMbx6 = 37, /**< mbx6 */
  kTopDarjeelingAlertPeripheralMbxJtag = 38, /**< mbx_jtag */
  kTopDarjeelingAlertPeripheralMbxPcie0 = 39, /**< mbx_pcie0 */
  kTopDarjeelingAlertPeripheralMbxPcie1 = 40, /**< mbx_pcie1 */
  kTopDarjeelingAlertPeripheralRvCoreIbex = 41, /**< rv_core_ibex */
  kTopDarjeelingAlertPeripheralLast = 41, /**< \internal Final Alert peripheral */
} top_darjeeling_alert_peripheral_t;

/**
 * Alert Handler Alert Source.
 *
 * Enumeration of all Alert Handler Alert Sources. The alert sources belonging to
 * the same peripheral are guaranteed to be consecutive.
 */
typedef enum top_darjeeling_alert_id {
  kTopDarjeelingAlertIdUart0FatalFault = 0, /**< uart0_fatal_fault */
  kTopDarjeelingAlertIdGpioFatalFault = 1, /**< gpio_fatal_fault */
  kTopDarjeelingAlertIdSpiDeviceFatalFault = 2, /**< spi_device_fatal_fault */
  kTopDarjeelingAlertIdI2c0FatalFault = 3, /**< i2c0_fatal_fault */
  kTopDarjeelingAlertIdRvTimerFatalFault = 4, /**< rv_timer_fatal_fault */
  kTopDarjeelingAlertIdOtpCtrlFatalMacroError = 5, /**< otp_ctrl_fatal_macro_error */
  kTopDarjeelingAlertIdOtpCtrlFatalCheckError = 6, /**< otp_ctrl_fatal_check_error */
  kTopDarjeelingAlertIdOtpCtrlFatalBusIntegError = 7, /**< otp_ctrl_fatal_bus_integ_error */
  kTopDarjeelingAlertIdOtpCtrlFatalPrimOtpAlert = 8, /**< otp_ctrl_fatal_prim_otp_alert */
  kTopDarjeelingAlertIdOtpCtrlRecovPrimOtpAlert = 9, /**< otp_ctrl_recov_prim_otp_alert */
  kTopDarjeelingAlertIdLcCtrlFatalProgError = 10, /**< lc_ctrl_fatal_prog_error */
  kTopDarjeelingAlertIdLcCtrlFatalStateError = 11, /**< lc_ctrl_fatal_state_error */
  kTopDarjeelingAlertIdLcCtrlFatalBusIntegError = 12, /**< lc_ctrl_fatal_bus_integ_error */
  kTopDarjeelingAlertIdSpiHost0FatalFault = 13, /**< spi_host0_fatal_fault */
  kTopDarjeelingAlertIdPwrmgrAonFatalFault = 14, /**< pwrmgr_aon_fatal_fault */
  kTopDarjeelingAlertIdRstmgrAonFatalFault = 15, /**< rstmgr_aon_fatal_fault */
  kTopDarjeelingAlertIdRstmgrAonFatalCnstyFault = 16, /**< rstmgr_aon_fatal_cnsty_fault */
  kTopDarjeelingAlertIdClkmgrAonRecovFault = 17, /**< clkmgr_aon_recov_fault */
  kTopDarjeelingAlertIdClkmgrAonFatalFault = 18, /**< clkmgr_aon_fatal_fault */
  kTopDarjeelingAlertIdPinmuxAonFatalFault = 19, /**< pinmux_aon_fatal_fault */
  kTopDarjeelingAlertIdAonTimerAonFatalFault = 20, /**< aon_timer_aon_fatal_fault */
  kTopDarjeelingAlertIdSensorCtrlRecovAlert = 21, /**< sensor_ctrl_recov_alert */
  kTopDarjeelingAlertIdSensorCtrlFatalAlert = 22, /**< sensor_ctrl_fatal_alert */
  kTopDarjeelingAlertIdSocProxyFatalAlertIntg = 23, /**< soc_proxy_fatal_alert_intg */
  kTopDarjeelingAlertIdSocProxyFatalAlertExternal0 = 24, /**< soc_proxy_fatal_alert_external_0 */
  kTopDarjeelingAlertIdSocProxyFatalAlertExternal1 = 25, /**< soc_proxy_fatal_alert_external_1 */
  kTopDarjeelingAlertIdSocProxyFatalAlertExternal2 = 26, /**< soc_proxy_fatal_alert_external_2 */
  kTopDarjeelingAlertIdSocProxyFatalAlertExternal3 = 27, /**< soc_proxy_fatal_alert_external_3 */
  kTopDarjeelingAlertIdSocProxyFatalAlertExternal4 = 28, /**< soc_proxy_fatal_alert_external_4 */
  kTopDarjeelingAlertIdSocProxyFatalAlertExternal5 = 29, /**< soc_proxy_fatal_alert_external_5 */
  kTopDarjeelingAlertIdSocProxyFatalAlertExternal6 = 30, /**< soc_proxy_fatal_alert_external_6 */
  kTopDarjeelingAlertIdSocProxyFatalAlertExternal7 = 31, /**< soc_proxy_fatal_alert_external_7 */
  kTopDarjeelingAlertIdSocProxyFatalAlertExternal8 = 32, /**< soc_proxy_fatal_alert_external_8 */
  kTopDarjeelingAlertIdSocProxyFatalAlertExternal9 = 33, /**< soc_proxy_fatal_alert_external_9 */
  kTopDarjeelingAlertIdSocProxyFatalAlertExternal10 = 34, /**< soc_proxy_fatal_alert_external_10 */
  kTopDarjeelingAlertIdSocProxyFatalAlertExternal11 = 35, /**< soc_proxy_fatal_alert_external_11 */
  kTopDarjeelingAlertIdSocProxyFatalAlertExternal12 = 36, /**< soc_proxy_fatal_alert_external_12 */
  kTopDarjeelingAlertIdSocProxyFatalAlertExternal13 = 37, /**< soc_proxy_fatal_alert_external_13 */
  kTopDarjeelingAlertIdSocProxyFatalAlertExternal14 = 38, /**< soc_proxy_fatal_alert_external_14 */
  kTopDarjeelingAlertIdSocProxyFatalAlertExternal15 = 39, /**< soc_proxy_fatal_alert_external_15 */
  kTopDarjeelingAlertIdSocProxyFatalAlertExternal16 = 40, /**< soc_proxy_fatal_alert_external_16 */
  kTopDarjeelingAlertIdSocProxyFatalAlertExternal17 = 41, /**< soc_proxy_fatal_alert_external_17 */
  kTopDarjeelingAlertIdSocProxyFatalAlertExternal18 = 42, /**< soc_proxy_fatal_alert_external_18 */
  kTopDarjeelingAlertIdSocProxyFatalAlertExternal19 = 43, /**< soc_proxy_fatal_alert_external_19 */
  kTopDarjeelingAlertIdSocProxyFatalAlertExternal20 = 44, /**< soc_proxy_fatal_alert_external_20 */
  kTopDarjeelingAlertIdSocProxyFatalAlertExternal21 = 45, /**< soc_proxy_fatal_alert_external_21 */
  kTopDarjeelingAlertIdSocProxyFatalAlertExternal22 = 46, /**< soc_proxy_fatal_alert_external_22 */
  kTopDarjeelingAlertIdSocProxyFatalAlertExternal23 = 47, /**< soc_proxy_fatal_alert_external_23 */
  kTopDarjeelingAlertIdSocProxyRecovAlertExternal0 = 48, /**< soc_proxy_recov_alert_external_0 */
  kTopDarjeelingAlertIdSocProxyRecovAlertExternal1 = 49, /**< soc_proxy_recov_alert_external_1 */
  kTopDarjeelingAlertIdSocProxyRecovAlertExternal2 = 50, /**< soc_proxy_recov_alert_external_2 */
  kTopDarjeelingAlertIdSocProxyRecovAlertExternal3 = 51, /**< soc_proxy_recov_alert_external_3 */
  kTopDarjeelingAlertIdSramCtrlRetAonFatalError = 52, /**< sram_ctrl_ret_aon_fatal_error */
  kTopDarjeelingAlertIdRvDmFatalFault = 53, /**< rv_dm_fatal_fault */
  kTopDarjeelingAlertIdRvPlicFatalFault = 54, /**< rv_plic_fatal_fault */
  kTopDarjeelingAlertIdAesRecovCtrlUpdateErr = 55, /**< aes_recov_ctrl_update_err */
  kTopDarjeelingAlertIdAesFatalFault = 56, /**< aes_fatal_fault */
  kTopDarjeelingAlertIdHmacFatalFault = 57, /**< hmac_fatal_fault */
  kTopDarjeelingAlertIdKmacRecovOperationErr = 58, /**< kmac_recov_operation_err */
  kTopDarjeelingAlertIdKmacFatalFaultErr = 59, /**< kmac_fatal_fault_err */
  kTopDarjeelingAlertIdOtbnFatal = 60, /**< otbn_fatal */
  kTopDarjeelingAlertIdOtbnRecov = 61, /**< otbn_recov */
  kTopDarjeelingAlertIdKeymgrDpeRecovOperationErr = 62, /**< keymgr_dpe_recov_operation_err */
  kTopDarjeelingAlertIdKeymgrDpeFatalFaultErr = 63, /**< keymgr_dpe_fatal_fault_err */
  kTopDarjeelingAlertIdCsrngRecovAlert = 64, /**< csrng_recov_alert */
  kTopDarjeelingAlertIdCsrngFatalAlert = 65, /**< csrng_fatal_alert */
  kTopDarjeelingAlertIdEdn0RecovAlert = 66, /**< edn0_recov_alert */
  kTopDarjeelingAlertIdEdn0FatalAlert = 67, /**< edn0_fatal_alert */
  kTopDarjeelingAlertIdEdn1RecovAlert = 68, /**< edn1_recov_alert */
  kTopDarjeelingAlertIdEdn1FatalAlert = 69, /**< edn1_fatal_alert */
  kTopDarjeelingAlertIdSramCtrlMainFatalError = 70, /**< sram_ctrl_main_fatal_error */
  kTopDarjeelingAlertIdSramCtrlMboxFatalError = 71, /**< sram_ctrl_mbox_fatal_error */
  kTopDarjeelingAlertIdRomCtrl0Fatal = 72, /**< rom_ctrl0_fatal */
  kTopDarjeelingAlertIdRomCtrl1Fatal = 73, /**< rom_ctrl1_fatal */
  kTopDarjeelingAlertIdDmaFatalFault = 74, /**< dma_fatal_fault */
  kTopDarjeelingAlertIdMbx0FatalFault = 75, /**< mbx0_fatal_fault */
  kTopDarjeelingAlertIdMbx0RecovFault = 76, /**< mbx0_recov_fault */
  kTopDarjeelingAlertIdMbx1FatalFault = 77, /**< mbx1_fatal_fault */
  kTopDarjeelingAlertIdMbx1RecovFault = 78, /**< mbx1_recov_fault */
  kTopDarjeelingAlertIdMbx2FatalFault = 79, /**< mbx2_fatal_fault */
  kTopDarjeelingAlertIdMbx2RecovFault = 80, /**< mbx2_recov_fault */
  kTopDarjeelingAlertIdMbx3FatalFault = 81, /**< mbx3_fatal_fault */
  kTopDarjeelingAlertIdMbx3RecovFault = 82, /**< mbx3_recov_fault */
  kTopDarjeelingAlertIdMbx4FatalFault = 83, /**< mbx4_fatal_fault */
  kTopDarjeelingAlertIdMbx4RecovFault = 84, /**< mbx4_recov_fault */
  kTopDarjeelingAlertIdMbx5FatalFault = 85, /**< mbx5_fatal_fault */
  kTopDarjeelingAlertIdMbx5RecovFault = 86, /**< mbx5_recov_fault */
  kTopDarjeelingAlertIdMbx6FatalFault = 87, /**< mbx6_fatal_fault */
  kTopDarjeelingAlertIdMbx6RecovFault = 88, /**< mbx6_recov_fault */
  kTopDarjeelingAlertIdMbxJtagFatalFault = 89, /**< mbx_jtag_fatal_fault */
  kTopDarjeelingAlertIdMbxJtagRecovFault = 90, /**< mbx_jtag_recov_fault */
  kTopDarjeelingAlertIdMbxPcie0FatalFault = 91, /**< mbx_pcie0_fatal_fault */
  kTopDarjeelingAlertIdMbxPcie0RecovFault = 92, /**< mbx_pcie0_recov_fault */
  kTopDarjeelingAlertIdMbxPcie1FatalFault = 93, /**< mbx_pcie1_fatal_fault */
  kTopDarjeelingAlertIdMbxPcie1RecovFault = 94, /**< mbx_pcie1_recov_fault */
  kTopDarjeelingAlertIdRvCoreIbexFatalSwErr = 95, /**< rv_core_ibex_fatal_sw_err */
  kTopDarjeelingAlertIdRvCoreIbexRecovSwErr = 96, /**< rv_core_ibex_recov_sw_err */
  kTopDarjeelingAlertIdRvCoreIbexFatalHwErr = 97, /**< rv_core_ibex_fatal_hw_err */
  kTopDarjeelingAlertIdRvCoreIbexRecovHwErr = 98, /**< rv_core_ibex_recov_hw_err */
  kTopDarjeelingAlertIdLast = 98, /**< \internal The Last Valid Alert ID. */
} top_darjeeling_alert_id_t;

/**
 * Alert Handler Alert Source to Peripheral Map
 *
 * This array is a mapping from `top_darjeeling_alert_id_t` to
 * `top_darjeeling_alert_peripheral_t`.
 */
extern const top_darjeeling_alert_peripheral_t
    top_darjeeling_alert_for_peripheral[99];

// PERIPH_INSEL ranges from 0 to TOP_DARJEELING_NUM_MIO_PADS + 2 -1}
//  0 and 1 are tied to value 0 and 1
#define TOP_DARJEELING_NUM_MIO_PADS 12
#define TOP_DARJEELING_NUM_DIO_PADS 73

#define TOP_DARJEELING_PINMUX_MIO_PERIPH_INSEL_IDX_OFFSET 2
#define TOP_DARJEELING_PINMUX_PERIPH_OUTSEL_IDX_OFFSET 3

/**
 * Pinmux Peripheral Input.
 */
typedef enum top_darjeeling_pinmux_peripheral_in {
  kTopDarjeelingPinmuxPeripheralInSocProxySocGpi12 = 0, /**< Peripheral Input 0 */
  kTopDarjeelingPinmuxPeripheralInSocProxySocGpi13 = 1, /**< Peripheral Input 1 */
  kTopDarjeelingPinmuxPeripheralInSocProxySocGpi14 = 2, /**< Peripheral Input 2 */
  kTopDarjeelingPinmuxPeripheralInSocProxySocGpi15 = 3, /**< Peripheral Input 3 */
  kTopDarjeelingPinmuxPeripheralInLast = 3, /**< \internal Last valid peripheral input */
} top_darjeeling_pinmux_peripheral_in_t;

/**
 * Pinmux MIO Input Selector.
 */
typedef enum top_darjeeling_pinmux_insel {
  kTopDarjeelingPinmuxInselConstantZero = 0, /**< Tie constantly to zero */
  kTopDarjeelingPinmuxInselConstantOne = 1, /**< Tie constantly to one */
  kTopDarjeelingPinmuxInselMio0 = 2, /**< MIO Pad 0 */
  kTopDarjeelingPinmuxInselMio1 = 3, /**< MIO Pad 1 */
  kTopDarjeelingPinmuxInselMio2 = 4, /**< MIO Pad 2 */
  kTopDarjeelingPinmuxInselMio3 = 5, /**< MIO Pad 3 */
  kTopDarjeelingPinmuxInselMio4 = 6, /**< MIO Pad 4 */
  kTopDarjeelingPinmuxInselMio5 = 7, /**< MIO Pad 5 */
  kTopDarjeelingPinmuxInselMio6 = 8, /**< MIO Pad 6 */
  kTopDarjeelingPinmuxInselMio7 = 9, /**< MIO Pad 7 */
  kTopDarjeelingPinmuxInselMio8 = 10, /**< MIO Pad 8 */
  kTopDarjeelingPinmuxInselMio9 = 11, /**< MIO Pad 9 */
  kTopDarjeelingPinmuxInselMio10 = 12, /**< MIO Pad 10 */
  kTopDarjeelingPinmuxInselMio11 = 13, /**< MIO Pad 11 */
  kTopDarjeelingPinmuxInselLast = 13, /**< \internal Last valid insel value */
} top_darjeeling_pinmux_insel_t;

/**
 * Pinmux MIO Output.
 */
typedef enum top_darjeeling_pinmux_mio_out {
  kTopDarjeelingPinmuxMioOutMio0 = 0, /**< MIO Pad 0 */
  kTopDarjeelingPinmuxMioOutMio1 = 1, /**< MIO Pad 1 */
  kTopDarjeelingPinmuxMioOutMio2 = 2, /**< MIO Pad 2 */
  kTopDarjeelingPinmuxMioOutMio3 = 3, /**< MIO Pad 3 */
  kTopDarjeelingPinmuxMioOutMio4 = 4, /**< MIO Pad 4 */
  kTopDarjeelingPinmuxMioOutMio5 = 5, /**< MIO Pad 5 */
  kTopDarjeelingPinmuxMioOutMio6 = 6, /**< MIO Pad 6 */
  kTopDarjeelingPinmuxMioOutMio7 = 7, /**< MIO Pad 7 */
  kTopDarjeelingPinmuxMioOutMio8 = 8, /**< MIO Pad 8 */
  kTopDarjeelingPinmuxMioOutMio9 = 9, /**< MIO Pad 9 */
  kTopDarjeelingPinmuxMioOutMio10 = 10, /**< MIO Pad 10 */
  kTopDarjeelingPinmuxMioOutMio11 = 11, /**< MIO Pad 11 */
  kTopDarjeelingPinmuxMioOutLast = 11, /**< \internal Last valid mio output */
} top_darjeeling_pinmux_mio_out_t;

/**
 * Pinmux Peripheral Output Selector.
 */
typedef enum top_darjeeling_pinmux_outsel {
  kTopDarjeelingPinmuxOutselConstantZero = 0, /**< Tie constantly to zero */
  kTopDarjeelingPinmuxOutselConstantOne = 1, /**< Tie constantly to one */
  kTopDarjeelingPinmuxOutselConstantHighZ = 2, /**< Tie constantly to high-Z */
  kTopDarjeelingPinmuxOutselSocProxySocGpo12 = 3, /**< Peripheral Output 0 */
  kTopDarjeelingPinmuxOutselSocProxySocGpo13 = 4, /**< Peripheral Output 1 */
  kTopDarjeelingPinmuxOutselSocProxySocGpo14 = 5, /**< Peripheral Output 2 */
  kTopDarjeelingPinmuxOutselSocProxySocGpo15 = 6, /**< Peripheral Output 3 */
  kTopDarjeelingPinmuxOutselOtpCtrlTest0 = 7, /**< Peripheral Output 4 */
  kTopDarjeelingPinmuxOutselLast = 7, /**< \internal Last valid outsel value */
} top_darjeeling_pinmux_outsel_t;

/**
 * Dedicated Pad Selects
 */
typedef enum top_darjeeling_direct_pads {
  kTopDarjeelingDirectPadsSpiHost0Sd0 = 0, /**<  */
  kTopDarjeelingDirectPadsSpiHost0Sd1 = 1, /**<  */
  kTopDarjeelingDirectPadsSpiHost0Sd2 = 2, /**<  */
  kTopDarjeelingDirectPadsSpiHost0Sd3 = 3, /**<  */
  kTopDarjeelingDirectPadsSpiDeviceSd0 = 4, /**<  */
  kTopDarjeelingDirectPadsSpiDeviceSd1 = 5, /**<  */
  kTopDarjeelingDirectPadsSpiDeviceSd2 = 6, /**<  */
  kTopDarjeelingDirectPadsSpiDeviceSd3 = 7, /**<  */
  kTopDarjeelingDirectPadsI2c0Scl = 8, /**<  */
  kTopDarjeelingDirectPadsI2c0Sda = 9, /**<  */
  kTopDarjeelingDirectPadsGpioGpio0 = 10, /**<  */
  kTopDarjeelingDirectPadsGpioGpio1 = 11, /**<  */
  kTopDarjeelingDirectPadsGpioGpio2 = 12, /**<  */
  kTopDarjeelingDirectPadsGpioGpio3 = 13, /**<  */
  kTopDarjeelingDirectPadsGpioGpio4 = 14, /**<  */
  kTopDarjeelingDirectPadsGpioGpio5 = 15, /**<  */
  kTopDarjeelingDirectPadsGpioGpio6 = 16, /**<  */
  kTopDarjeelingDirectPadsGpioGpio7 = 17, /**<  */
  kTopDarjeelingDirectPadsGpioGpio8 = 18, /**<  */
  kTopDarjeelingDirectPadsGpioGpio9 = 19, /**<  */
  kTopDarjeelingDirectPadsGpioGpio10 = 20, /**<  */
  kTopDarjeelingDirectPadsGpioGpio11 = 21, /**<  */
  kTopDarjeelingDirectPadsGpioGpio12 = 22, /**<  */
  kTopDarjeelingDirectPadsGpioGpio13 = 23, /**<  */
  kTopDarjeelingDirectPadsGpioGpio14 = 24, /**<  */
  kTopDarjeelingDirectPadsGpioGpio15 = 25, /**<  */
  kTopDarjeelingDirectPadsGpioGpio16 = 26, /**<  */
  kTopDarjeelingDirectPadsGpioGpio17 = 27, /**<  */
  kTopDarjeelingDirectPadsGpioGpio18 = 28, /**<  */
  kTopDarjeelingDirectPadsGpioGpio19 = 29, /**<  */
  kTopDarjeelingDirectPadsGpioGpio20 = 30, /**<  */
  kTopDarjeelingDirectPadsGpioGpio21 = 31, /**<  */
  kTopDarjeelingDirectPadsGpioGpio22 = 32, /**<  */
  kTopDarjeelingDirectPadsGpioGpio23 = 33, /**<  */
  kTopDarjeelingDirectPadsGpioGpio24 = 34, /**<  */
  kTopDarjeelingDirectPadsGpioGpio25 = 35, /**<  */
  kTopDarjeelingDirectPadsGpioGpio26 = 36, /**<  */
  kTopDarjeelingDirectPadsGpioGpio27 = 37, /**<  */
  kTopDarjeelingDirectPadsGpioGpio28 = 38, /**<  */
  kTopDarjeelingDirectPadsGpioGpio29 = 39, /**<  */
  kTopDarjeelingDirectPadsGpioGpio30 = 40, /**<  */
  kTopDarjeelingDirectPadsGpioGpio31 = 41, /**<  */
  kTopDarjeelingDirectPadsSpiDeviceSck = 42, /**<  */
  kTopDarjeelingDirectPadsSpiDeviceCsb = 43, /**<  */
  kTopDarjeelingDirectPadsSpiDeviceTpmCsb = 44, /**<  */
  kTopDarjeelingDirectPadsUart0Rx = 45, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpi0 = 46, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpi1 = 47, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpi2 = 48, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpi3 = 49, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpi4 = 50, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpi5 = 51, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpi6 = 52, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpi7 = 53, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpi8 = 54, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpi9 = 55, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpi10 = 56, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpi11 = 57, /**<  */
  kTopDarjeelingDirectPadsSpiHost0Sck = 58, /**<  */
  kTopDarjeelingDirectPadsSpiHost0Csb = 59, /**<  */
  kTopDarjeelingDirectPadsUart0Tx = 60, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpo0 = 61, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpo1 = 62, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpo2 = 63, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpo3 = 64, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpo4 = 65, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpo5 = 66, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpo6 = 67, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpo7 = 68, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpo8 = 69, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpo9 = 70, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpo10 = 71, /**<  */
  kTopDarjeelingDirectPadsSocProxySocGpo11 = 72, /**<  */
  kTopDarjeelingDirectPadsLast = 72, /**< \internal Last valid direct pad */
} top_darjeeling_direct_pads_t;

/**
 * Muxed Pad Selects
 */
typedef enum top_darjeeling_muxed_pads {
  kTopDarjeelingMuxedPadsMio0 = 0, /**<  */
  kTopDarjeelingMuxedPadsMio1 = 1, /**<  */
  kTopDarjeelingMuxedPadsMio2 = 2, /**<  */
  kTopDarjeelingMuxedPadsMio3 = 3, /**<  */
  kTopDarjeelingMuxedPadsMio4 = 4, /**<  */
  kTopDarjeelingMuxedPadsMio5 = 5, /**<  */
  kTopDarjeelingMuxedPadsMio6 = 6, /**<  */
  kTopDarjeelingMuxedPadsMio7 = 7, /**<  */
  kTopDarjeelingMuxedPadsMio8 = 8, /**<  */
  kTopDarjeelingMuxedPadsMio9 = 9, /**<  */
  kTopDarjeelingMuxedPadsMio10 = 10, /**<  */
  kTopDarjeelingMuxedPadsMio11 = 11, /**<  */
  kTopDarjeelingMuxedPadsLast = 11, /**< \internal Last valid muxed pad */
} top_darjeeling_muxed_pads_t;

/**
 * Power Manager Wakeup Signals
 */
typedef enum top_darjeeling_power_manager_wake_ups {
  kTopDarjeelingPowerManagerWakeUpsPinmuxAonPinWkupReq = 0, /**<  */
  kTopDarjeelingPowerManagerWakeUpsPinmuxAonUsbWkupReq = 1, /**<  */
  kTopDarjeelingPowerManagerWakeUpsAonTimerAonWkupReq = 2, /**<  */
  kTopDarjeelingPowerManagerWakeUpsSensorCtrlWkupReq = 3, /**<  */
  kTopDarjeelingPowerManagerWakeUpsSocProxyWkupInternalReq = 4, /**<  */
  kTopDarjeelingPowerManagerWakeUpsSocProxyWkupExternalReq = 5, /**<  */
  kTopDarjeelingPowerManagerWakeUpsLast = 5, /**< \internal Last valid pwrmgr wakeup signal */
} top_darjeeling_power_manager_wake_ups_t;

/**
 * Reset Manager Software Controlled Resets
 */
typedef enum top_darjeeling_reset_manager_sw_resets {
  kTopDarjeelingResetManagerSwResetsSpiDevice = 0, /**<  */
  kTopDarjeelingResetManagerSwResetsSpiHost0 = 1, /**<  */
  kTopDarjeelingResetManagerSwResetsI2c0 = 2, /**<  */
  kTopDarjeelingResetManagerSwResetsLast = 2, /**< \internal Last valid rstmgr software reset request */
} top_darjeeling_reset_manager_sw_resets_t;

/**
 * Power Manager Reset Request Signals
 */
typedef enum top_darjeeling_power_manager_reset_requests {
  kTopDarjeelingPowerManagerResetRequestsAonTimerAonAonTimerRstReq = 0, /**<  */
  kTopDarjeelingPowerManagerResetRequestsSocProxyRstReqExternal = 1, /**<  */
  kTopDarjeelingPowerManagerResetRequestsLast = 1, /**< \internal Last valid pwrmgr reset_request signal */
} top_darjeeling_power_manager_reset_requests_t;

/**
 * Clock Manager Software-Controlled ("Gated") Clocks.
 *
 * The Software has full control over these clocks.
 */
typedef enum top_darjeeling_gateable_clocks {
  kTopDarjeelingGateableClocksIoDiv4Peri = 0, /**< Clock clk_io_div4_peri in group peri */
  kTopDarjeelingGateableClocksIoDiv2Peri = 1, /**< Clock clk_io_div2_peri in group peri */
  kTopDarjeelingGateableClocksIoPeri = 2, /**< Clock clk_io_peri in group peri */
  kTopDarjeelingGateableClocksUsbPeri = 3, /**< Clock clk_usb_peri in group peri */
  kTopDarjeelingGateableClocksLast = 3, /**< \internal Last Valid Gateable Clock */
} top_darjeeling_gateable_clocks_t;

/**
 * Clock Manager Software-Hinted Clocks.
 *
 * The Software has partial control over these clocks. It can ask them to stop,
 * but the clock manager is in control of whether the clock actually is stopped.
 */
typedef enum top_darjeeling_hintable_clocks {
  kTopDarjeelingHintableClocksMainAes = 0, /**< Clock clk_main_aes in group trans */
  kTopDarjeelingHintableClocksMainHmac = 1, /**< Clock clk_main_hmac in group trans */
  kTopDarjeelingHintableClocksMainKmac = 2, /**< Clock clk_main_kmac in group trans */
  kTopDarjeelingHintableClocksMainOtbn = 3, /**< Clock clk_main_otbn in group trans */
  kTopDarjeelingHintableClocksLast = 3, /**< \internal Last Valid Hintable Clock */
} top_darjeeling_hintable_clocks_t;

/**
 * MMIO Region
 *
 * MMIO region excludes any memory that is separate from the module
 * configuration space, i.e. ROM, main SRAM, and flash are excluded but
 * retention SRAM, spi_device memory, or usbdev memory are included.
 */
#define TOP_DARJEELING_MMIO_BASE_ADDR 0x21100000u
#define TOP_DARJEELING_MMIO_SIZE_BYTES 0xF501000u

// Header Extern Guard
#ifdef __cplusplus
}  // extern "C"
#endif

#endif  // OPENTITAN_HW_TOP_DARJEELING_SW_AUTOGEN_TOP_DARJEELING_H_
