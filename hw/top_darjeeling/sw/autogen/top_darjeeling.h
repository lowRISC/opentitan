// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_TOP_DARJEELING_SW_AUTOGEN_TOP_DARJEELING_H_
#define OPENTITAN_HW_TOP_DARJEELING_SW_AUTOGEN_TOP_DARJEELING_H_

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
#define TOP_DARJEELING_GPIO_SIZE_BYTES 0x40u

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
 * Peripheral base address for i2c1 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_I2C1_BASE_ADDR 0x31030000u

/**
 * Peripheral size for i2c1 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_I2C1_BASE_ADDR and
 * `TOP_DARJEELING_I2C1_BASE_ADDR + TOP_DARJEELING_I2C1_SIZE_BYTES`.
 */
#define TOP_DARJEELING_I2C1_SIZE_BYTES 0x80u

/**
 * Peripheral base address for i2c2 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_I2C2_BASE_ADDR 0x31040000u

/**
 * Peripheral size for i2c2 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_I2C2_BASE_ADDR and
 * `TOP_DARJEELING_I2C2_BASE_ADDR + TOP_DARJEELING_I2C2_SIZE_BYTES`.
 */
#define TOP_DARJEELING_I2C2_SIZE_BYTES 0x80u

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
 * Peripheral base address for lc_ctrl in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_LC_CTRL_BASE_ADDR 0x30140000u

/**
 * Peripheral size for lc_ctrl in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_LC_CTRL_BASE_ADDR and
 * `TOP_DARJEELING_LC_CTRL_BASE_ADDR + TOP_DARJEELING_LC_CTRL_SIZE_BYTES`.
 */
#define TOP_DARJEELING_LC_CTRL_SIZE_BYTES 0x100u

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
 * Peripheral base address for spi_host1 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_SPI_HOST1_BASE_ADDR 0x32000000u

/**
 * Peripheral size for spi_host1 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_SPI_HOST1_BASE_ADDR and
 * `TOP_DARJEELING_SPI_HOST1_BASE_ADDR + TOP_DARJEELING_SPI_HOST1_SIZE_BYTES`.
 */
#define TOP_DARJEELING_SPI_HOST1_SIZE_BYTES 0x40u

/**
 * Peripheral base address for usbdev in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_USBDEV_BASE_ADDR 0x32010000u

/**
 * Peripheral size for usbdev in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_USBDEV_BASE_ADDR and
 * `TOP_DARJEELING_USBDEV_BASE_ADDR + TOP_DARJEELING_USBDEV_SIZE_BYTES`.
 */
#define TOP_DARJEELING_USBDEV_SIZE_BYTES 0x1000u

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
 * Peripheral base address for sysrst_ctrl_aon in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_SYSRST_CTRL_AON_BASE_ADDR 0x31060000u

/**
 * Peripheral size for sysrst_ctrl_aon in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_SYSRST_CTRL_AON_BASE_ADDR and
 * `TOP_DARJEELING_SYSRST_CTRL_AON_BASE_ADDR + TOP_DARJEELING_SYSRST_CTRL_AON_SIZE_BYTES`.
 */
#define TOP_DARJEELING_SYSRST_CTRL_AON_SIZE_BYTES 0x100u

/**
 * Peripheral base address for adc_ctrl_aon in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_ADC_CTRL_AON_BASE_ADDR 0x31070000u

/**
 * Peripheral size for adc_ctrl_aon in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_ADC_CTRL_AON_BASE_ADDR and
 * `TOP_DARJEELING_ADC_CTRL_AON_BASE_ADDR + TOP_DARJEELING_ADC_CTRL_AON_SIZE_BYTES`.
 */
#define TOP_DARJEELING_ADC_CTRL_AON_SIZE_BYTES 0x80u

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
 * Peripheral base address for core device on flash_ctrl in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_FLASH_CTRL_CORE_BASE_ADDR 0x33000000u

/**
 * Peripheral size for core device on flash_ctrl in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_FLASH_CTRL_CORE_BASE_ADDR and
 * `TOP_DARJEELING_FLASH_CTRL_CORE_BASE_ADDR + TOP_DARJEELING_FLASH_CTRL_CORE_SIZE_BYTES`.
 */
#define TOP_DARJEELING_FLASH_CTRL_CORE_SIZE_BYTES 0x200u

/**
 * Peripheral base address for prim device on flash_ctrl in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_FLASH_CTRL_PRIM_BASE_ADDR 0x33008000u

/**
 * Peripheral size for prim device on flash_ctrl in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_FLASH_CTRL_PRIM_BASE_ADDR and
 * `TOP_DARJEELING_FLASH_CTRL_PRIM_BASE_ADDR + TOP_DARJEELING_FLASH_CTRL_PRIM_SIZE_BYTES`.
 */
#define TOP_DARJEELING_FLASH_CTRL_PRIM_SIZE_BYTES 0x80u

/**
 * Peripheral base address for mem device on flash_ctrl in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_FLASH_CTRL_MEM_BASE_ADDR 0x34000000u

/**
 * Peripheral size for mem device on flash_ctrl in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_FLASH_CTRL_MEM_BASE_ADDR and
 * `TOP_DARJEELING_FLASH_CTRL_MEM_BASE_ADDR + TOP_DARJEELING_FLASH_CTRL_MEM_SIZE_BYTES`.
 */
#define TOP_DARJEELING_FLASH_CTRL_MEM_SIZE_BYTES 0x100000u

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
 * Peripheral base address for keymgr in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_KEYMGR_BASE_ADDR 0x21140000u

/**
 * Peripheral size for keymgr in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_KEYMGR_BASE_ADDR and
 * `TOP_DARJEELING_KEYMGR_BASE_ADDR + TOP_DARJEELING_KEYMGR_SIZE_BYTES`.
 */
#define TOP_DARJEELING_KEYMGR_SIZE_BYTES 0x100u

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
#define TOP_DARJEELING_DMA_SIZE_BYTES 0x100u

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
 * Memory base address for eflash in top darjeeling.
 */
#define TOP_DARJEELING_EFLASH_BASE_ADDR 0x34000000u

/**
 * Memory size for eflash in top darjeeling.
 */
#define TOP_DARJEELING_EFLASH_SIZE_BYTES 0x100000u

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
  kTopDarjeelingPlicPeripheralI2c1 = 5, /**< i2c1 */
  kTopDarjeelingPlicPeripheralI2c2 = 6, /**< i2c2 */
  kTopDarjeelingPlicPeripheralRvTimer = 7, /**< rv_timer */
  kTopDarjeelingPlicPeripheralOtpCtrl = 8, /**< otp_ctrl */
  kTopDarjeelingPlicPeripheralAlertHandler = 9, /**< alert_handler */
  kTopDarjeelingPlicPeripheralSpiHost0 = 10, /**< spi_host0 */
  kTopDarjeelingPlicPeripheralSpiHost1 = 11, /**< spi_host1 */
  kTopDarjeelingPlicPeripheralUsbdev = 12, /**< usbdev */
  kTopDarjeelingPlicPeripheralPwrmgrAon = 13, /**< pwrmgr_aon */
  kTopDarjeelingPlicPeripheralSysrstCtrlAon = 14, /**< sysrst_ctrl_aon */
  kTopDarjeelingPlicPeripheralAdcCtrlAon = 15, /**< adc_ctrl_aon */
  kTopDarjeelingPlicPeripheralAonTimerAon = 16, /**< aon_timer_aon */
  kTopDarjeelingPlicPeripheralSensorCtrl = 17, /**< sensor_ctrl */
  kTopDarjeelingPlicPeripheralSocProxy = 18, /**< soc_proxy */
  kTopDarjeelingPlicPeripheralFlashCtrl = 19, /**< flash_ctrl */
  kTopDarjeelingPlicPeripheralHmac = 20, /**< hmac */
  kTopDarjeelingPlicPeripheralKmac = 21, /**< kmac */
  kTopDarjeelingPlicPeripheralOtbn = 22, /**< otbn */
  kTopDarjeelingPlicPeripheralKeymgr = 23, /**< keymgr */
  kTopDarjeelingPlicPeripheralCsrng = 24, /**< csrng */
  kTopDarjeelingPlicPeripheralEdn0 = 25, /**< edn0 */
  kTopDarjeelingPlicPeripheralEdn1 = 26, /**< edn1 */
  kTopDarjeelingPlicPeripheralDma = 27, /**< dma */
  kTopDarjeelingPlicPeripheralLast = 27, /**< \internal Final PLIC peripheral */
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
  kTopDarjeelingPlicIrqIdI2c1FmtThreshold = 68, /**< i2c1_fmt_threshold */
  kTopDarjeelingPlicIrqIdI2c1RxThreshold = 69, /**< i2c1_rx_threshold */
  kTopDarjeelingPlicIrqIdI2c1FmtOverflow = 70, /**< i2c1_fmt_overflow */
  kTopDarjeelingPlicIrqIdI2c1RxOverflow = 71, /**< i2c1_rx_overflow */
  kTopDarjeelingPlicIrqIdI2c1Nak = 72, /**< i2c1_nak */
  kTopDarjeelingPlicIrqIdI2c1SclInterference = 73, /**< i2c1_scl_interference */
  kTopDarjeelingPlicIrqIdI2c1SdaInterference = 74, /**< i2c1_sda_interference */
  kTopDarjeelingPlicIrqIdI2c1StretchTimeout = 75, /**< i2c1_stretch_timeout */
  kTopDarjeelingPlicIrqIdI2c1SdaUnstable = 76, /**< i2c1_sda_unstable */
  kTopDarjeelingPlicIrqIdI2c1CmdComplete = 77, /**< i2c1_cmd_complete */
  kTopDarjeelingPlicIrqIdI2c1TxStretch = 78, /**< i2c1_tx_stretch */
  kTopDarjeelingPlicIrqIdI2c1TxOverflow = 79, /**< i2c1_tx_overflow */
  kTopDarjeelingPlicIrqIdI2c1AcqFull = 80, /**< i2c1_acq_full */
  kTopDarjeelingPlicIrqIdI2c1UnexpStop = 81, /**< i2c1_unexp_stop */
  kTopDarjeelingPlicIrqIdI2c1HostTimeout = 82, /**< i2c1_host_timeout */
  kTopDarjeelingPlicIrqIdI2c2FmtThreshold = 83, /**< i2c2_fmt_threshold */
  kTopDarjeelingPlicIrqIdI2c2RxThreshold = 84, /**< i2c2_rx_threshold */
  kTopDarjeelingPlicIrqIdI2c2FmtOverflow = 85, /**< i2c2_fmt_overflow */
  kTopDarjeelingPlicIrqIdI2c2RxOverflow = 86, /**< i2c2_rx_overflow */
  kTopDarjeelingPlicIrqIdI2c2Nak = 87, /**< i2c2_nak */
  kTopDarjeelingPlicIrqIdI2c2SclInterference = 88, /**< i2c2_scl_interference */
  kTopDarjeelingPlicIrqIdI2c2SdaInterference = 89, /**< i2c2_sda_interference */
  kTopDarjeelingPlicIrqIdI2c2StretchTimeout = 90, /**< i2c2_stretch_timeout */
  kTopDarjeelingPlicIrqIdI2c2SdaUnstable = 91, /**< i2c2_sda_unstable */
  kTopDarjeelingPlicIrqIdI2c2CmdComplete = 92, /**< i2c2_cmd_complete */
  kTopDarjeelingPlicIrqIdI2c2TxStretch = 93, /**< i2c2_tx_stretch */
  kTopDarjeelingPlicIrqIdI2c2TxOverflow = 94, /**< i2c2_tx_overflow */
  kTopDarjeelingPlicIrqIdI2c2AcqFull = 95, /**< i2c2_acq_full */
  kTopDarjeelingPlicIrqIdI2c2UnexpStop = 96, /**< i2c2_unexp_stop */
  kTopDarjeelingPlicIrqIdI2c2HostTimeout = 97, /**< i2c2_host_timeout */
  kTopDarjeelingPlicIrqIdRvTimerTimerExpiredHart0Timer0 = 98, /**< rv_timer_timer_expired_hart0_timer0 */
  kTopDarjeelingPlicIrqIdOtpCtrlOtpOperationDone = 99, /**< otp_ctrl_otp_operation_done */
  kTopDarjeelingPlicIrqIdOtpCtrlOtpError = 100, /**< otp_ctrl_otp_error */
  kTopDarjeelingPlicIrqIdAlertHandlerClassa = 101, /**< alert_handler_classa */
  kTopDarjeelingPlicIrqIdAlertHandlerClassb = 102, /**< alert_handler_classb */
  kTopDarjeelingPlicIrqIdAlertHandlerClassc = 103, /**< alert_handler_classc */
  kTopDarjeelingPlicIrqIdAlertHandlerClassd = 104, /**< alert_handler_classd */
  kTopDarjeelingPlicIrqIdSpiHost0Error = 105, /**< spi_host0_error */
  kTopDarjeelingPlicIrqIdSpiHost0SpiEvent = 106, /**< spi_host0_spi_event */
  kTopDarjeelingPlicIrqIdSpiHost1Error = 107, /**< spi_host1_error */
  kTopDarjeelingPlicIrqIdSpiHost1SpiEvent = 108, /**< spi_host1_spi_event */
  kTopDarjeelingPlicIrqIdUsbdevPktReceived = 109, /**< usbdev_pkt_received */
  kTopDarjeelingPlicIrqIdUsbdevPktSent = 110, /**< usbdev_pkt_sent */
  kTopDarjeelingPlicIrqIdUsbdevDisconnected = 111, /**< usbdev_disconnected */
  kTopDarjeelingPlicIrqIdUsbdevHostLost = 112, /**< usbdev_host_lost */
  kTopDarjeelingPlicIrqIdUsbdevLinkReset = 113, /**< usbdev_link_reset */
  kTopDarjeelingPlicIrqIdUsbdevLinkSuspend = 114, /**< usbdev_link_suspend */
  kTopDarjeelingPlicIrqIdUsbdevLinkResume = 115, /**< usbdev_link_resume */
  kTopDarjeelingPlicIrqIdUsbdevAvEmpty = 116, /**< usbdev_av_empty */
  kTopDarjeelingPlicIrqIdUsbdevRxFull = 117, /**< usbdev_rx_full */
  kTopDarjeelingPlicIrqIdUsbdevAvOverflow = 118, /**< usbdev_av_overflow */
  kTopDarjeelingPlicIrqIdUsbdevLinkInErr = 119, /**< usbdev_link_in_err */
  kTopDarjeelingPlicIrqIdUsbdevRxCrcErr = 120, /**< usbdev_rx_crc_err */
  kTopDarjeelingPlicIrqIdUsbdevRxPidErr = 121, /**< usbdev_rx_pid_err */
  kTopDarjeelingPlicIrqIdUsbdevRxBitstuffErr = 122, /**< usbdev_rx_bitstuff_err */
  kTopDarjeelingPlicIrqIdUsbdevFrame = 123, /**< usbdev_frame */
  kTopDarjeelingPlicIrqIdUsbdevPowered = 124, /**< usbdev_powered */
  kTopDarjeelingPlicIrqIdUsbdevLinkOutErr = 125, /**< usbdev_link_out_err */
  kTopDarjeelingPlicIrqIdPwrmgrAonWakeup = 126, /**< pwrmgr_aon_wakeup */
  kTopDarjeelingPlicIrqIdSysrstCtrlAonEventDetected = 127, /**< sysrst_ctrl_aon_event_detected */
  kTopDarjeelingPlicIrqIdAdcCtrlAonMatchDone = 128, /**< adc_ctrl_aon_match_done */
  kTopDarjeelingPlicIrqIdAonTimerAonWkupTimerExpired = 129, /**< aon_timer_aon_wkup_timer_expired */
  kTopDarjeelingPlicIrqIdAonTimerAonWdogTimerBark = 130, /**< aon_timer_aon_wdog_timer_bark */
  kTopDarjeelingPlicIrqIdSensorCtrlIoStatusChange = 131, /**< sensor_ctrl_io_status_change */
  kTopDarjeelingPlicIrqIdSensorCtrlInitStatusChange = 132, /**< sensor_ctrl_init_status_change */
  kTopDarjeelingPlicIrqIdSocProxyExternal0 = 133, /**< soc_proxy_external 0 */
  kTopDarjeelingPlicIrqIdSocProxyExternal1 = 134, /**< soc_proxy_external 1 */
  kTopDarjeelingPlicIrqIdSocProxyExternal2 = 135, /**< soc_proxy_external 2 */
  kTopDarjeelingPlicIrqIdSocProxyExternal3 = 136, /**< soc_proxy_external 3 */
  kTopDarjeelingPlicIrqIdSocProxyExternal4 = 137, /**< soc_proxy_external 4 */
  kTopDarjeelingPlicIrqIdSocProxyExternal5 = 138, /**< soc_proxy_external 5 */
  kTopDarjeelingPlicIrqIdSocProxyExternal6 = 139, /**< soc_proxy_external 6 */
  kTopDarjeelingPlicIrqIdSocProxyExternal7 = 140, /**< soc_proxy_external 7 */
  kTopDarjeelingPlicIrqIdFlashCtrlProgEmpty = 141, /**< flash_ctrl_prog_empty */
  kTopDarjeelingPlicIrqIdFlashCtrlProgLvl = 142, /**< flash_ctrl_prog_lvl */
  kTopDarjeelingPlicIrqIdFlashCtrlRdFull = 143, /**< flash_ctrl_rd_full */
  kTopDarjeelingPlicIrqIdFlashCtrlRdLvl = 144, /**< flash_ctrl_rd_lvl */
  kTopDarjeelingPlicIrqIdFlashCtrlOpDone = 145, /**< flash_ctrl_op_done */
  kTopDarjeelingPlicIrqIdFlashCtrlCorrErr = 146, /**< flash_ctrl_corr_err */
  kTopDarjeelingPlicIrqIdHmacHmacDone = 147, /**< hmac_hmac_done */
  kTopDarjeelingPlicIrqIdHmacFifoEmpty = 148, /**< hmac_fifo_empty */
  kTopDarjeelingPlicIrqIdHmacHmacErr = 149, /**< hmac_hmac_err */
  kTopDarjeelingPlicIrqIdKmacKmacDone = 150, /**< kmac_kmac_done */
  kTopDarjeelingPlicIrqIdKmacFifoEmpty = 151, /**< kmac_fifo_empty */
  kTopDarjeelingPlicIrqIdKmacKmacErr = 152, /**< kmac_kmac_err */
  kTopDarjeelingPlicIrqIdOtbnDone = 153, /**< otbn_done */
  kTopDarjeelingPlicIrqIdKeymgrOpDone = 154, /**< keymgr_op_done */
  kTopDarjeelingPlicIrqIdCsrngCsCmdReqDone = 155, /**< csrng_cs_cmd_req_done */
  kTopDarjeelingPlicIrqIdCsrngCsEntropyReq = 156, /**< csrng_cs_entropy_req */
  kTopDarjeelingPlicIrqIdCsrngCsHwInstExc = 157, /**< csrng_cs_hw_inst_exc */
  kTopDarjeelingPlicIrqIdCsrngCsFatalErr = 158, /**< csrng_cs_fatal_err */
  kTopDarjeelingPlicIrqIdEdn0EdnCmdReqDone = 159, /**< edn0_edn_cmd_req_done */
  kTopDarjeelingPlicIrqIdEdn0EdnFatalErr = 160, /**< edn0_edn_fatal_err */
  kTopDarjeelingPlicIrqIdEdn1EdnCmdReqDone = 161, /**< edn1_edn_cmd_req_done */
  kTopDarjeelingPlicIrqIdEdn1EdnFatalErr = 162, /**< edn1_edn_fatal_err */
  kTopDarjeelingPlicIrqIdDmaDmaDone = 163, /**< dma_dma_done */
  kTopDarjeelingPlicIrqIdDmaDmaError = 164, /**< dma_dma_error */
  kTopDarjeelingPlicIrqIdDmaDmaMemoryBufferLimit = 165, /**< dma_dma_memory_buffer_limit */
  kTopDarjeelingPlicIrqIdLast = 165, /**< \internal The Last Valid Interrupt ID. */
} top_darjeeling_plic_irq_id_t;

/**
 * PLIC Interrupt Source to Peripheral Map
 *
 * This array is a mapping from `top_darjeeling_plic_irq_id_t` to
 * `top_darjeeling_plic_peripheral_t`.
 */
extern const top_darjeeling_plic_peripheral_t
    top_darjeeling_plic_interrupt_for_peripheral[166];

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
  kTopDarjeelingAlertPeripheralI2c1 = 4, /**< i2c1 */
  kTopDarjeelingAlertPeripheralI2c2 = 5, /**< i2c2 */
  kTopDarjeelingAlertPeripheralRvTimer = 6, /**< rv_timer */
  kTopDarjeelingAlertPeripheralOtpCtrl = 7, /**< otp_ctrl */
  kTopDarjeelingAlertPeripheralLcCtrl = 8, /**< lc_ctrl */
  kTopDarjeelingAlertPeripheralSpiHost0 = 9, /**< spi_host0 */
  kTopDarjeelingAlertPeripheralSpiHost1 = 10, /**< spi_host1 */
  kTopDarjeelingAlertPeripheralUsbdev = 11, /**< usbdev */
  kTopDarjeelingAlertPeripheralPwrmgrAon = 12, /**< pwrmgr_aon */
  kTopDarjeelingAlertPeripheralRstmgrAon = 13, /**< rstmgr_aon */
  kTopDarjeelingAlertPeripheralClkmgrAon = 14, /**< clkmgr_aon */
  kTopDarjeelingAlertPeripheralSysrstCtrlAon = 15, /**< sysrst_ctrl_aon */
  kTopDarjeelingAlertPeripheralAdcCtrlAon = 16, /**< adc_ctrl_aon */
  kTopDarjeelingAlertPeripheralPinmuxAon = 17, /**< pinmux_aon */
  kTopDarjeelingAlertPeripheralAonTimerAon = 18, /**< aon_timer_aon */
  kTopDarjeelingAlertPeripheralSensorCtrl = 19, /**< sensor_ctrl */
  kTopDarjeelingAlertPeripheralSocProxy = 20, /**< soc_proxy */
  kTopDarjeelingAlertPeripheralSramCtrlRetAon = 21, /**< sram_ctrl_ret_aon */
  kTopDarjeelingAlertPeripheralFlashCtrl = 22, /**< flash_ctrl */
  kTopDarjeelingAlertPeripheralRvDm = 23, /**< rv_dm */
  kTopDarjeelingAlertPeripheralRvPlic = 24, /**< rv_plic */
  kTopDarjeelingAlertPeripheralAes = 25, /**< aes */
  kTopDarjeelingAlertPeripheralHmac = 26, /**< hmac */
  kTopDarjeelingAlertPeripheralKmac = 27, /**< kmac */
  kTopDarjeelingAlertPeripheralOtbn = 28, /**< otbn */
  kTopDarjeelingAlertPeripheralKeymgr = 29, /**< keymgr */
  kTopDarjeelingAlertPeripheralCsrng = 30, /**< csrng */
  kTopDarjeelingAlertPeripheralEdn0 = 31, /**< edn0 */
  kTopDarjeelingAlertPeripheralEdn1 = 32, /**< edn1 */
  kTopDarjeelingAlertPeripheralSramCtrlMain = 33, /**< sram_ctrl_main */
  kTopDarjeelingAlertPeripheralSramCtrlMbox = 34, /**< sram_ctrl_mbox */
  kTopDarjeelingAlertPeripheralRomCtrl0 = 35, /**< rom_ctrl0 */
  kTopDarjeelingAlertPeripheralRomCtrl1 = 36, /**< rom_ctrl1 */
  kTopDarjeelingAlertPeripheralDma = 37, /**< dma */
  kTopDarjeelingAlertPeripheralRvCoreIbex = 38, /**< rv_core_ibex */
  kTopDarjeelingAlertPeripheralLast = 38, /**< \internal Final Alert peripheral */
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
  kTopDarjeelingAlertIdI2c1FatalFault = 4, /**< i2c1_fatal_fault */
  kTopDarjeelingAlertIdI2c2FatalFault = 5, /**< i2c2_fatal_fault */
  kTopDarjeelingAlertIdRvTimerFatalFault = 6, /**< rv_timer_fatal_fault */
  kTopDarjeelingAlertIdOtpCtrlFatalMacroError = 7, /**< otp_ctrl_fatal_macro_error */
  kTopDarjeelingAlertIdOtpCtrlFatalCheckError = 8, /**< otp_ctrl_fatal_check_error */
  kTopDarjeelingAlertIdOtpCtrlFatalBusIntegError = 9, /**< otp_ctrl_fatal_bus_integ_error */
  kTopDarjeelingAlertIdOtpCtrlFatalPrimOtpAlert = 10, /**< otp_ctrl_fatal_prim_otp_alert */
  kTopDarjeelingAlertIdOtpCtrlRecovPrimOtpAlert = 11, /**< otp_ctrl_recov_prim_otp_alert */
  kTopDarjeelingAlertIdLcCtrlFatalProgError = 12, /**< lc_ctrl_fatal_prog_error */
  kTopDarjeelingAlertIdLcCtrlFatalStateError = 13, /**< lc_ctrl_fatal_state_error */
  kTopDarjeelingAlertIdLcCtrlFatalBusIntegError = 14, /**< lc_ctrl_fatal_bus_integ_error */
  kTopDarjeelingAlertIdSpiHost0FatalFault = 15, /**< spi_host0_fatal_fault */
  kTopDarjeelingAlertIdSpiHost1FatalFault = 16, /**< spi_host1_fatal_fault */
  kTopDarjeelingAlertIdUsbdevFatalFault = 17, /**< usbdev_fatal_fault */
  kTopDarjeelingAlertIdPwrmgrAonFatalFault = 18, /**< pwrmgr_aon_fatal_fault */
  kTopDarjeelingAlertIdRstmgrAonFatalFault = 19, /**< rstmgr_aon_fatal_fault */
  kTopDarjeelingAlertIdRstmgrAonFatalCnstyFault = 20, /**< rstmgr_aon_fatal_cnsty_fault */
  kTopDarjeelingAlertIdClkmgrAonRecovFault = 21, /**< clkmgr_aon_recov_fault */
  kTopDarjeelingAlertIdClkmgrAonFatalFault = 22, /**< clkmgr_aon_fatal_fault */
  kTopDarjeelingAlertIdSysrstCtrlAonFatalFault = 23, /**< sysrst_ctrl_aon_fatal_fault */
  kTopDarjeelingAlertIdAdcCtrlAonFatalFault = 24, /**< adc_ctrl_aon_fatal_fault */
  kTopDarjeelingAlertIdPinmuxAonFatalFault = 25, /**< pinmux_aon_fatal_fault */
  kTopDarjeelingAlertIdAonTimerAonFatalFault = 26, /**< aon_timer_aon_fatal_fault */
  kTopDarjeelingAlertIdSensorCtrlRecovAlert = 27, /**< sensor_ctrl_recov_alert */
  kTopDarjeelingAlertIdSensorCtrlFatalAlert = 28, /**< sensor_ctrl_fatal_alert */
  kTopDarjeelingAlertIdSocProxyFatalAlertIntg = 29, /**< soc_proxy_fatal_alert_intg */
  kTopDarjeelingAlertIdSocProxyFatalAlertExternal0 = 30, /**< soc_proxy_fatal_alert_external_0 */
  kTopDarjeelingAlertIdSocProxyFatalAlertExternal1 = 31, /**< soc_proxy_fatal_alert_external_1 */
  kTopDarjeelingAlertIdSocProxyFatalAlertExternal2 = 32, /**< soc_proxy_fatal_alert_external_2 */
  kTopDarjeelingAlertIdSocProxyFatalAlertExternal3 = 33, /**< soc_proxy_fatal_alert_external_3 */
  kTopDarjeelingAlertIdSocProxyRecovAlertExternal0 = 34, /**< soc_proxy_recov_alert_external_0 */
  kTopDarjeelingAlertIdSocProxyRecovAlertExternal1 = 35, /**< soc_proxy_recov_alert_external_1 */
  kTopDarjeelingAlertIdSocProxyRecovAlertExternal2 = 36, /**< soc_proxy_recov_alert_external_2 */
  kTopDarjeelingAlertIdSocProxyRecovAlertExternal3 = 37, /**< soc_proxy_recov_alert_external_3 */
  kTopDarjeelingAlertIdSramCtrlRetAonFatalError = 38, /**< sram_ctrl_ret_aon_fatal_error */
  kTopDarjeelingAlertIdFlashCtrlRecovErr = 39, /**< flash_ctrl_recov_err */
  kTopDarjeelingAlertIdFlashCtrlFatalStdErr = 40, /**< flash_ctrl_fatal_std_err */
  kTopDarjeelingAlertIdFlashCtrlFatalErr = 41, /**< flash_ctrl_fatal_err */
  kTopDarjeelingAlertIdFlashCtrlFatalPrimFlashAlert = 42, /**< flash_ctrl_fatal_prim_flash_alert */
  kTopDarjeelingAlertIdFlashCtrlRecovPrimFlashAlert = 43, /**< flash_ctrl_recov_prim_flash_alert */
  kTopDarjeelingAlertIdRvDmFatalFault = 44, /**< rv_dm_fatal_fault */
  kTopDarjeelingAlertIdRvPlicFatalFault = 45, /**< rv_plic_fatal_fault */
  kTopDarjeelingAlertIdAesRecovCtrlUpdateErr = 46, /**< aes_recov_ctrl_update_err */
  kTopDarjeelingAlertIdAesFatalFault = 47, /**< aes_fatal_fault */
  kTopDarjeelingAlertIdHmacFatalFault = 48, /**< hmac_fatal_fault */
  kTopDarjeelingAlertIdKmacRecovOperationErr = 49, /**< kmac_recov_operation_err */
  kTopDarjeelingAlertIdKmacFatalFaultErr = 50, /**< kmac_fatal_fault_err */
  kTopDarjeelingAlertIdOtbnFatal = 51, /**< otbn_fatal */
  kTopDarjeelingAlertIdOtbnRecov = 52, /**< otbn_recov */
  kTopDarjeelingAlertIdKeymgrRecovOperationErr = 53, /**< keymgr_recov_operation_err */
  kTopDarjeelingAlertIdKeymgrFatalFaultErr = 54, /**< keymgr_fatal_fault_err */
  kTopDarjeelingAlertIdCsrngRecovAlert = 55, /**< csrng_recov_alert */
  kTopDarjeelingAlertIdCsrngFatalAlert = 56, /**< csrng_fatal_alert */
  kTopDarjeelingAlertIdEdn0RecovAlert = 57, /**< edn0_recov_alert */
  kTopDarjeelingAlertIdEdn0FatalAlert = 58, /**< edn0_fatal_alert */
  kTopDarjeelingAlertIdEdn1RecovAlert = 59, /**< edn1_recov_alert */
  kTopDarjeelingAlertIdEdn1FatalAlert = 60, /**< edn1_fatal_alert */
  kTopDarjeelingAlertIdSramCtrlMainFatalError = 61, /**< sram_ctrl_main_fatal_error */
  kTopDarjeelingAlertIdSramCtrlMboxFatalError = 62, /**< sram_ctrl_mbox_fatal_error */
  kTopDarjeelingAlertIdRomCtrl0Fatal = 63, /**< rom_ctrl0_fatal */
  kTopDarjeelingAlertIdRomCtrl1Fatal = 64, /**< rom_ctrl1_fatal */
  kTopDarjeelingAlertIdDmaFatalFault = 65, /**< dma_fatal_fault */
  kTopDarjeelingAlertIdRvCoreIbexFatalSwErr = 66, /**< rv_core_ibex_fatal_sw_err */
  kTopDarjeelingAlertIdRvCoreIbexRecovSwErr = 67, /**< rv_core_ibex_recov_sw_err */
  kTopDarjeelingAlertIdRvCoreIbexFatalHwErr = 68, /**< rv_core_ibex_fatal_hw_err */
  kTopDarjeelingAlertIdRvCoreIbexRecovHwErr = 69, /**< rv_core_ibex_recov_hw_err */
  kTopDarjeelingAlertIdLast = 69, /**< \internal The Last Valid Alert ID. */
} top_darjeeling_alert_id_t;

/**
 * Alert Handler Alert Source to Peripheral Map
 *
 * This array is a mapping from `top_darjeeling_alert_id_t` to
 * `top_darjeeling_alert_peripheral_t`.
 */
extern const top_darjeeling_alert_peripheral_t
    top_darjeeling_alert_for_peripheral[70];

// PERIPH_INSEL ranges from 0 to TOP_DARJEELING_NUM_MIO_PADS + 2 -1}
//  0 and 1 are tied to value 0 and 1
#define TOP_DARJEELING_NUM_MIO_PADS 47
#define TOP_DARJEELING_NUM_DIO_PADS 16

#define TOP_DARJEELING_PINMUX_MIO_PERIPH_INSEL_IDX_OFFSET 2
#define TOP_DARJEELING_PINMUX_PERIPH_OUTSEL_IDX_OFFSET 3

/**
 * Pinmux Peripheral Input.
 */
typedef enum top_darjeeling_pinmux_peripheral_in {
  kTopDarjeelingPinmuxPeripheralInGpioGpio0 = 0, /**< Peripheral Input 0 */
  kTopDarjeelingPinmuxPeripheralInGpioGpio1 = 1, /**< Peripheral Input 1 */
  kTopDarjeelingPinmuxPeripheralInGpioGpio2 = 2, /**< Peripheral Input 2 */
  kTopDarjeelingPinmuxPeripheralInGpioGpio3 = 3, /**< Peripheral Input 3 */
  kTopDarjeelingPinmuxPeripheralInGpioGpio4 = 4, /**< Peripheral Input 4 */
  kTopDarjeelingPinmuxPeripheralInGpioGpio5 = 5, /**< Peripheral Input 5 */
  kTopDarjeelingPinmuxPeripheralInGpioGpio6 = 6, /**< Peripheral Input 6 */
  kTopDarjeelingPinmuxPeripheralInGpioGpio7 = 7, /**< Peripheral Input 7 */
  kTopDarjeelingPinmuxPeripheralInGpioGpio8 = 8, /**< Peripheral Input 8 */
  kTopDarjeelingPinmuxPeripheralInGpioGpio9 = 9, /**< Peripheral Input 9 */
  kTopDarjeelingPinmuxPeripheralInGpioGpio10 = 10, /**< Peripheral Input 10 */
  kTopDarjeelingPinmuxPeripheralInGpioGpio11 = 11, /**< Peripheral Input 11 */
  kTopDarjeelingPinmuxPeripheralInGpioGpio12 = 12, /**< Peripheral Input 12 */
  kTopDarjeelingPinmuxPeripheralInGpioGpio13 = 13, /**< Peripheral Input 13 */
  kTopDarjeelingPinmuxPeripheralInGpioGpio14 = 14, /**< Peripheral Input 14 */
  kTopDarjeelingPinmuxPeripheralInGpioGpio15 = 15, /**< Peripheral Input 15 */
  kTopDarjeelingPinmuxPeripheralInGpioGpio16 = 16, /**< Peripheral Input 16 */
  kTopDarjeelingPinmuxPeripheralInGpioGpio17 = 17, /**< Peripheral Input 17 */
  kTopDarjeelingPinmuxPeripheralInGpioGpio18 = 18, /**< Peripheral Input 18 */
  kTopDarjeelingPinmuxPeripheralInGpioGpio19 = 19, /**< Peripheral Input 19 */
  kTopDarjeelingPinmuxPeripheralInGpioGpio20 = 20, /**< Peripheral Input 20 */
  kTopDarjeelingPinmuxPeripheralInGpioGpio21 = 21, /**< Peripheral Input 21 */
  kTopDarjeelingPinmuxPeripheralInGpioGpio22 = 22, /**< Peripheral Input 22 */
  kTopDarjeelingPinmuxPeripheralInGpioGpio23 = 23, /**< Peripheral Input 23 */
  kTopDarjeelingPinmuxPeripheralInGpioGpio24 = 24, /**< Peripheral Input 24 */
  kTopDarjeelingPinmuxPeripheralInGpioGpio25 = 25, /**< Peripheral Input 25 */
  kTopDarjeelingPinmuxPeripheralInGpioGpio26 = 26, /**< Peripheral Input 26 */
  kTopDarjeelingPinmuxPeripheralInGpioGpio27 = 27, /**< Peripheral Input 27 */
  kTopDarjeelingPinmuxPeripheralInGpioGpio28 = 28, /**< Peripheral Input 28 */
  kTopDarjeelingPinmuxPeripheralInGpioGpio29 = 29, /**< Peripheral Input 29 */
  kTopDarjeelingPinmuxPeripheralInGpioGpio30 = 30, /**< Peripheral Input 30 */
  kTopDarjeelingPinmuxPeripheralInGpioGpio31 = 31, /**< Peripheral Input 31 */
  kTopDarjeelingPinmuxPeripheralInI2c0Sda = 32, /**< Peripheral Input 32 */
  kTopDarjeelingPinmuxPeripheralInI2c0Scl = 33, /**< Peripheral Input 33 */
  kTopDarjeelingPinmuxPeripheralInI2c1Sda = 34, /**< Peripheral Input 34 */
  kTopDarjeelingPinmuxPeripheralInI2c1Scl = 35, /**< Peripheral Input 35 */
  kTopDarjeelingPinmuxPeripheralInI2c2Sda = 36, /**< Peripheral Input 36 */
  kTopDarjeelingPinmuxPeripheralInI2c2Scl = 37, /**< Peripheral Input 37 */
  kTopDarjeelingPinmuxPeripheralInSpiHost1Sd0 = 38, /**< Peripheral Input 38 */
  kTopDarjeelingPinmuxPeripheralInSpiHost1Sd1 = 39, /**< Peripheral Input 39 */
  kTopDarjeelingPinmuxPeripheralInSpiHost1Sd2 = 40, /**< Peripheral Input 40 */
  kTopDarjeelingPinmuxPeripheralInSpiHost1Sd3 = 41, /**< Peripheral Input 41 */
  kTopDarjeelingPinmuxPeripheralInUart0Rx = 42, /**< Peripheral Input 42 */
  kTopDarjeelingPinmuxPeripheralInSpiDeviceTpmCsb = 43, /**< Peripheral Input 43 */
  kTopDarjeelingPinmuxPeripheralInFlashCtrlTck = 44, /**< Peripheral Input 44 */
  kTopDarjeelingPinmuxPeripheralInFlashCtrlTms = 45, /**< Peripheral Input 45 */
  kTopDarjeelingPinmuxPeripheralInFlashCtrlTdi = 46, /**< Peripheral Input 46 */
  kTopDarjeelingPinmuxPeripheralInSysrstCtrlAonAcPresent = 47, /**< Peripheral Input 47 */
  kTopDarjeelingPinmuxPeripheralInSysrstCtrlAonKey0In = 48, /**< Peripheral Input 48 */
  kTopDarjeelingPinmuxPeripheralInSysrstCtrlAonKey1In = 49, /**< Peripheral Input 49 */
  kTopDarjeelingPinmuxPeripheralInSysrstCtrlAonKey2In = 50, /**< Peripheral Input 50 */
  kTopDarjeelingPinmuxPeripheralInSysrstCtrlAonPwrbIn = 51, /**< Peripheral Input 51 */
  kTopDarjeelingPinmuxPeripheralInSysrstCtrlAonLidOpen = 52, /**< Peripheral Input 52 */
  kTopDarjeelingPinmuxPeripheralInUsbdevSense = 53, /**< Peripheral Input 53 */
  kTopDarjeelingPinmuxPeripheralInLast = 53, /**< \internal Last valid peripheral input */
} top_darjeeling_pinmux_peripheral_in_t;

/**
 * Pinmux MIO Input Selector.
 */
typedef enum top_darjeeling_pinmux_insel {
  kTopDarjeelingPinmuxInselConstantZero = 0, /**< Tie constantly to zero */
  kTopDarjeelingPinmuxInselConstantOne = 1, /**< Tie constantly to one */
  kTopDarjeelingPinmuxInselIoa0 = 2, /**< MIO Pad 0 */
  kTopDarjeelingPinmuxInselIoa1 = 3, /**< MIO Pad 1 */
  kTopDarjeelingPinmuxInselIoa2 = 4, /**< MIO Pad 2 */
  kTopDarjeelingPinmuxInselIoa3 = 5, /**< MIO Pad 3 */
  kTopDarjeelingPinmuxInselIoa4 = 6, /**< MIO Pad 4 */
  kTopDarjeelingPinmuxInselIoa5 = 7, /**< MIO Pad 5 */
  kTopDarjeelingPinmuxInselIoa6 = 8, /**< MIO Pad 6 */
  kTopDarjeelingPinmuxInselIoa7 = 9, /**< MIO Pad 7 */
  kTopDarjeelingPinmuxInselIoa8 = 10, /**< MIO Pad 8 */
  kTopDarjeelingPinmuxInselIob0 = 11, /**< MIO Pad 9 */
  kTopDarjeelingPinmuxInselIob1 = 12, /**< MIO Pad 10 */
  kTopDarjeelingPinmuxInselIob2 = 13, /**< MIO Pad 11 */
  kTopDarjeelingPinmuxInselIob3 = 14, /**< MIO Pad 12 */
  kTopDarjeelingPinmuxInselIob4 = 15, /**< MIO Pad 13 */
  kTopDarjeelingPinmuxInselIob5 = 16, /**< MIO Pad 14 */
  kTopDarjeelingPinmuxInselIob6 = 17, /**< MIO Pad 15 */
  kTopDarjeelingPinmuxInselIob7 = 18, /**< MIO Pad 16 */
  kTopDarjeelingPinmuxInselIob8 = 19, /**< MIO Pad 17 */
  kTopDarjeelingPinmuxInselIob9 = 20, /**< MIO Pad 18 */
  kTopDarjeelingPinmuxInselIob10 = 21, /**< MIO Pad 19 */
  kTopDarjeelingPinmuxInselIob11 = 22, /**< MIO Pad 20 */
  kTopDarjeelingPinmuxInselIob12 = 23, /**< MIO Pad 21 */
  kTopDarjeelingPinmuxInselIoc0 = 24, /**< MIO Pad 22 */
  kTopDarjeelingPinmuxInselIoc1 = 25, /**< MIO Pad 23 */
  kTopDarjeelingPinmuxInselIoc2 = 26, /**< MIO Pad 24 */
  kTopDarjeelingPinmuxInselIoc3 = 27, /**< MIO Pad 25 */
  kTopDarjeelingPinmuxInselIoc4 = 28, /**< MIO Pad 26 */
  kTopDarjeelingPinmuxInselIoc5 = 29, /**< MIO Pad 27 */
  kTopDarjeelingPinmuxInselIoc6 = 30, /**< MIO Pad 28 */
  kTopDarjeelingPinmuxInselIoc7 = 31, /**< MIO Pad 29 */
  kTopDarjeelingPinmuxInselIoc8 = 32, /**< MIO Pad 30 */
  kTopDarjeelingPinmuxInselIoc9 = 33, /**< MIO Pad 31 */
  kTopDarjeelingPinmuxInselIoc10 = 34, /**< MIO Pad 32 */
  kTopDarjeelingPinmuxInselIoc11 = 35, /**< MIO Pad 33 */
  kTopDarjeelingPinmuxInselIoc12 = 36, /**< MIO Pad 34 */
  kTopDarjeelingPinmuxInselIor0 = 37, /**< MIO Pad 35 */
  kTopDarjeelingPinmuxInselIor1 = 38, /**< MIO Pad 36 */
  kTopDarjeelingPinmuxInselIor2 = 39, /**< MIO Pad 37 */
  kTopDarjeelingPinmuxInselIor3 = 40, /**< MIO Pad 38 */
  kTopDarjeelingPinmuxInselIor4 = 41, /**< MIO Pad 39 */
  kTopDarjeelingPinmuxInselIor5 = 42, /**< MIO Pad 40 */
  kTopDarjeelingPinmuxInselIor6 = 43, /**< MIO Pad 41 */
  kTopDarjeelingPinmuxInselIor7 = 44, /**< MIO Pad 42 */
  kTopDarjeelingPinmuxInselIor10 = 45, /**< MIO Pad 43 */
  kTopDarjeelingPinmuxInselIor11 = 46, /**< MIO Pad 44 */
  kTopDarjeelingPinmuxInselIor12 = 47, /**< MIO Pad 45 */
  kTopDarjeelingPinmuxInselIor13 = 48, /**< MIO Pad 46 */
  kTopDarjeelingPinmuxInselLast = 48, /**< \internal Last valid insel value */
} top_darjeeling_pinmux_insel_t;

/**
 * Pinmux MIO Output.
 */
typedef enum top_darjeeling_pinmux_mio_out {
  kTopDarjeelingPinmuxMioOutIoa0 = 0, /**< MIO Pad 0 */
  kTopDarjeelingPinmuxMioOutIoa1 = 1, /**< MIO Pad 1 */
  kTopDarjeelingPinmuxMioOutIoa2 = 2, /**< MIO Pad 2 */
  kTopDarjeelingPinmuxMioOutIoa3 = 3, /**< MIO Pad 3 */
  kTopDarjeelingPinmuxMioOutIoa4 = 4, /**< MIO Pad 4 */
  kTopDarjeelingPinmuxMioOutIoa5 = 5, /**< MIO Pad 5 */
  kTopDarjeelingPinmuxMioOutIoa6 = 6, /**< MIO Pad 6 */
  kTopDarjeelingPinmuxMioOutIoa7 = 7, /**< MIO Pad 7 */
  kTopDarjeelingPinmuxMioOutIoa8 = 8, /**< MIO Pad 8 */
  kTopDarjeelingPinmuxMioOutIob0 = 9, /**< MIO Pad 9 */
  kTopDarjeelingPinmuxMioOutIob1 = 10, /**< MIO Pad 10 */
  kTopDarjeelingPinmuxMioOutIob2 = 11, /**< MIO Pad 11 */
  kTopDarjeelingPinmuxMioOutIob3 = 12, /**< MIO Pad 12 */
  kTopDarjeelingPinmuxMioOutIob4 = 13, /**< MIO Pad 13 */
  kTopDarjeelingPinmuxMioOutIob5 = 14, /**< MIO Pad 14 */
  kTopDarjeelingPinmuxMioOutIob6 = 15, /**< MIO Pad 15 */
  kTopDarjeelingPinmuxMioOutIob7 = 16, /**< MIO Pad 16 */
  kTopDarjeelingPinmuxMioOutIob8 = 17, /**< MIO Pad 17 */
  kTopDarjeelingPinmuxMioOutIob9 = 18, /**< MIO Pad 18 */
  kTopDarjeelingPinmuxMioOutIob10 = 19, /**< MIO Pad 19 */
  kTopDarjeelingPinmuxMioOutIob11 = 20, /**< MIO Pad 20 */
  kTopDarjeelingPinmuxMioOutIob12 = 21, /**< MIO Pad 21 */
  kTopDarjeelingPinmuxMioOutIoc0 = 22, /**< MIO Pad 22 */
  kTopDarjeelingPinmuxMioOutIoc1 = 23, /**< MIO Pad 23 */
  kTopDarjeelingPinmuxMioOutIoc2 = 24, /**< MIO Pad 24 */
  kTopDarjeelingPinmuxMioOutIoc3 = 25, /**< MIO Pad 25 */
  kTopDarjeelingPinmuxMioOutIoc4 = 26, /**< MIO Pad 26 */
  kTopDarjeelingPinmuxMioOutIoc5 = 27, /**< MIO Pad 27 */
  kTopDarjeelingPinmuxMioOutIoc6 = 28, /**< MIO Pad 28 */
  kTopDarjeelingPinmuxMioOutIoc7 = 29, /**< MIO Pad 29 */
  kTopDarjeelingPinmuxMioOutIoc8 = 30, /**< MIO Pad 30 */
  kTopDarjeelingPinmuxMioOutIoc9 = 31, /**< MIO Pad 31 */
  kTopDarjeelingPinmuxMioOutIoc10 = 32, /**< MIO Pad 32 */
  kTopDarjeelingPinmuxMioOutIoc11 = 33, /**< MIO Pad 33 */
  kTopDarjeelingPinmuxMioOutIoc12 = 34, /**< MIO Pad 34 */
  kTopDarjeelingPinmuxMioOutIor0 = 35, /**< MIO Pad 35 */
  kTopDarjeelingPinmuxMioOutIor1 = 36, /**< MIO Pad 36 */
  kTopDarjeelingPinmuxMioOutIor2 = 37, /**< MIO Pad 37 */
  kTopDarjeelingPinmuxMioOutIor3 = 38, /**< MIO Pad 38 */
  kTopDarjeelingPinmuxMioOutIor4 = 39, /**< MIO Pad 39 */
  kTopDarjeelingPinmuxMioOutIor5 = 40, /**< MIO Pad 40 */
  kTopDarjeelingPinmuxMioOutIor6 = 41, /**< MIO Pad 41 */
  kTopDarjeelingPinmuxMioOutIor7 = 42, /**< MIO Pad 42 */
  kTopDarjeelingPinmuxMioOutIor10 = 43, /**< MIO Pad 43 */
  kTopDarjeelingPinmuxMioOutIor11 = 44, /**< MIO Pad 44 */
  kTopDarjeelingPinmuxMioOutIor12 = 45, /**< MIO Pad 45 */
  kTopDarjeelingPinmuxMioOutIor13 = 46, /**< MIO Pad 46 */
  kTopDarjeelingPinmuxMioOutLast = 46, /**< \internal Last valid mio output */
} top_darjeeling_pinmux_mio_out_t;

/**
 * Pinmux Peripheral Output Selector.
 */
typedef enum top_darjeeling_pinmux_outsel {
  kTopDarjeelingPinmuxOutselConstantZero = 0, /**< Tie constantly to zero */
  kTopDarjeelingPinmuxOutselConstantOne = 1, /**< Tie constantly to one */
  kTopDarjeelingPinmuxOutselConstantHighZ = 2, /**< Tie constantly to high-Z */
  kTopDarjeelingPinmuxOutselGpioGpio0 = 3, /**< Peripheral Output 0 */
  kTopDarjeelingPinmuxOutselGpioGpio1 = 4, /**< Peripheral Output 1 */
  kTopDarjeelingPinmuxOutselGpioGpio2 = 5, /**< Peripheral Output 2 */
  kTopDarjeelingPinmuxOutselGpioGpio3 = 6, /**< Peripheral Output 3 */
  kTopDarjeelingPinmuxOutselGpioGpio4 = 7, /**< Peripheral Output 4 */
  kTopDarjeelingPinmuxOutselGpioGpio5 = 8, /**< Peripheral Output 5 */
  kTopDarjeelingPinmuxOutselGpioGpio6 = 9, /**< Peripheral Output 6 */
  kTopDarjeelingPinmuxOutselGpioGpio7 = 10, /**< Peripheral Output 7 */
  kTopDarjeelingPinmuxOutselGpioGpio8 = 11, /**< Peripheral Output 8 */
  kTopDarjeelingPinmuxOutselGpioGpio9 = 12, /**< Peripheral Output 9 */
  kTopDarjeelingPinmuxOutselGpioGpio10 = 13, /**< Peripheral Output 10 */
  kTopDarjeelingPinmuxOutselGpioGpio11 = 14, /**< Peripheral Output 11 */
  kTopDarjeelingPinmuxOutselGpioGpio12 = 15, /**< Peripheral Output 12 */
  kTopDarjeelingPinmuxOutselGpioGpio13 = 16, /**< Peripheral Output 13 */
  kTopDarjeelingPinmuxOutselGpioGpio14 = 17, /**< Peripheral Output 14 */
  kTopDarjeelingPinmuxOutselGpioGpio15 = 18, /**< Peripheral Output 15 */
  kTopDarjeelingPinmuxOutselGpioGpio16 = 19, /**< Peripheral Output 16 */
  kTopDarjeelingPinmuxOutselGpioGpio17 = 20, /**< Peripheral Output 17 */
  kTopDarjeelingPinmuxOutselGpioGpio18 = 21, /**< Peripheral Output 18 */
  kTopDarjeelingPinmuxOutselGpioGpio19 = 22, /**< Peripheral Output 19 */
  kTopDarjeelingPinmuxOutselGpioGpio20 = 23, /**< Peripheral Output 20 */
  kTopDarjeelingPinmuxOutselGpioGpio21 = 24, /**< Peripheral Output 21 */
  kTopDarjeelingPinmuxOutselGpioGpio22 = 25, /**< Peripheral Output 22 */
  kTopDarjeelingPinmuxOutselGpioGpio23 = 26, /**< Peripheral Output 23 */
  kTopDarjeelingPinmuxOutselGpioGpio24 = 27, /**< Peripheral Output 24 */
  kTopDarjeelingPinmuxOutselGpioGpio25 = 28, /**< Peripheral Output 25 */
  kTopDarjeelingPinmuxOutselGpioGpio26 = 29, /**< Peripheral Output 26 */
  kTopDarjeelingPinmuxOutselGpioGpio27 = 30, /**< Peripheral Output 27 */
  kTopDarjeelingPinmuxOutselGpioGpio28 = 31, /**< Peripheral Output 28 */
  kTopDarjeelingPinmuxOutselGpioGpio29 = 32, /**< Peripheral Output 29 */
  kTopDarjeelingPinmuxOutselGpioGpio30 = 33, /**< Peripheral Output 30 */
  kTopDarjeelingPinmuxOutselGpioGpio31 = 34, /**< Peripheral Output 31 */
  kTopDarjeelingPinmuxOutselI2c0Sda = 35, /**< Peripheral Output 32 */
  kTopDarjeelingPinmuxOutselI2c0Scl = 36, /**< Peripheral Output 33 */
  kTopDarjeelingPinmuxOutselI2c1Sda = 37, /**< Peripheral Output 34 */
  kTopDarjeelingPinmuxOutselI2c1Scl = 38, /**< Peripheral Output 35 */
  kTopDarjeelingPinmuxOutselI2c2Sda = 39, /**< Peripheral Output 36 */
  kTopDarjeelingPinmuxOutselI2c2Scl = 40, /**< Peripheral Output 37 */
  kTopDarjeelingPinmuxOutselSpiHost1Sd0 = 41, /**< Peripheral Output 38 */
  kTopDarjeelingPinmuxOutselSpiHost1Sd1 = 42, /**< Peripheral Output 39 */
  kTopDarjeelingPinmuxOutselSpiHost1Sd2 = 43, /**< Peripheral Output 40 */
  kTopDarjeelingPinmuxOutselSpiHost1Sd3 = 44, /**< Peripheral Output 41 */
  kTopDarjeelingPinmuxOutselUart0Tx = 45, /**< Peripheral Output 42 */
  kTopDarjeelingPinmuxOutselSpiHost1Sck = 46, /**< Peripheral Output 43 */
  kTopDarjeelingPinmuxOutselSpiHost1Csb = 47, /**< Peripheral Output 44 */
  kTopDarjeelingPinmuxOutselFlashCtrlTdo = 48, /**< Peripheral Output 45 */
  kTopDarjeelingPinmuxOutselSensorCtrlAstDebugOut0 = 49, /**< Peripheral Output 46 */
  kTopDarjeelingPinmuxOutselSensorCtrlAstDebugOut1 = 50, /**< Peripheral Output 47 */
  kTopDarjeelingPinmuxOutselSensorCtrlAstDebugOut2 = 51, /**< Peripheral Output 48 */
  kTopDarjeelingPinmuxOutselSensorCtrlAstDebugOut3 = 52, /**< Peripheral Output 49 */
  kTopDarjeelingPinmuxOutselSensorCtrlAstDebugOut4 = 53, /**< Peripheral Output 50 */
  kTopDarjeelingPinmuxOutselSensorCtrlAstDebugOut5 = 54, /**< Peripheral Output 51 */
  kTopDarjeelingPinmuxOutselSensorCtrlAstDebugOut6 = 55, /**< Peripheral Output 52 */
  kTopDarjeelingPinmuxOutselSensorCtrlAstDebugOut7 = 56, /**< Peripheral Output 53 */
  kTopDarjeelingPinmuxOutselSensorCtrlAstDebugOut8 = 57, /**< Peripheral Output 54 */
  kTopDarjeelingPinmuxOutselOtpCtrlTest0 = 58, /**< Peripheral Output 55 */
  kTopDarjeelingPinmuxOutselSysrstCtrlAonBatDisable = 59, /**< Peripheral Output 56 */
  kTopDarjeelingPinmuxOutselSysrstCtrlAonKey0Out = 60, /**< Peripheral Output 57 */
  kTopDarjeelingPinmuxOutselSysrstCtrlAonKey1Out = 61, /**< Peripheral Output 58 */
  kTopDarjeelingPinmuxOutselSysrstCtrlAonKey2Out = 62, /**< Peripheral Output 59 */
  kTopDarjeelingPinmuxOutselSysrstCtrlAonPwrbOut = 63, /**< Peripheral Output 60 */
  kTopDarjeelingPinmuxOutselSysrstCtrlAonZ3Wakeup = 64, /**< Peripheral Output 61 */
  kTopDarjeelingPinmuxOutselLast = 64, /**< \internal Last valid outsel value */
} top_darjeeling_pinmux_outsel_t;

/**
 * Dedicated Pad Selects
 */
typedef enum top_darjeeling_direct_pads {
  kTopDarjeelingDirectPadsUsbdevUsbDp = 0, /**<  */
  kTopDarjeelingDirectPadsUsbdevUsbDn = 1, /**<  */
  kTopDarjeelingDirectPadsSpiHost0Sd0 = 2, /**<  */
  kTopDarjeelingDirectPadsSpiHost0Sd1 = 3, /**<  */
  kTopDarjeelingDirectPadsSpiHost0Sd2 = 4, /**<  */
  kTopDarjeelingDirectPadsSpiHost0Sd3 = 5, /**<  */
  kTopDarjeelingDirectPadsSpiDeviceSd0 = 6, /**<  */
  kTopDarjeelingDirectPadsSpiDeviceSd1 = 7, /**<  */
  kTopDarjeelingDirectPadsSpiDeviceSd2 = 8, /**<  */
  kTopDarjeelingDirectPadsSpiDeviceSd3 = 9, /**<  */
  kTopDarjeelingDirectPadsSysrstCtrlAonEcRstL = 10, /**<  */
  kTopDarjeelingDirectPadsSysrstCtrlAonFlashWpL = 11, /**<  */
  kTopDarjeelingDirectPadsSpiDeviceSck = 12, /**<  */
  kTopDarjeelingDirectPadsSpiDeviceCsb = 13, /**<  */
  kTopDarjeelingDirectPadsSpiHost0Sck = 14, /**<  */
  kTopDarjeelingDirectPadsSpiHost0Csb = 15, /**<  */
  kTopDarjeelingDirectPadsLast = 15, /**< \internal Last valid direct pad */
} top_darjeeling_direct_pads_t;

/**
 * Muxed Pad Selects
 */
typedef enum top_darjeeling_muxed_pads {
  kTopDarjeelingMuxedPadsIoa0 = 0, /**<  */
  kTopDarjeelingMuxedPadsIoa1 = 1, /**<  */
  kTopDarjeelingMuxedPadsIoa2 = 2, /**<  */
  kTopDarjeelingMuxedPadsIoa3 = 3, /**<  */
  kTopDarjeelingMuxedPadsIoa4 = 4, /**<  */
  kTopDarjeelingMuxedPadsIoa5 = 5, /**<  */
  kTopDarjeelingMuxedPadsIoa6 = 6, /**<  */
  kTopDarjeelingMuxedPadsIoa7 = 7, /**<  */
  kTopDarjeelingMuxedPadsIoa8 = 8, /**<  */
  kTopDarjeelingMuxedPadsIob0 = 9, /**<  */
  kTopDarjeelingMuxedPadsIob1 = 10, /**<  */
  kTopDarjeelingMuxedPadsIob2 = 11, /**<  */
  kTopDarjeelingMuxedPadsIob3 = 12, /**<  */
  kTopDarjeelingMuxedPadsIob4 = 13, /**<  */
  kTopDarjeelingMuxedPadsIob5 = 14, /**<  */
  kTopDarjeelingMuxedPadsIob6 = 15, /**<  */
  kTopDarjeelingMuxedPadsIob7 = 16, /**<  */
  kTopDarjeelingMuxedPadsIob8 = 17, /**<  */
  kTopDarjeelingMuxedPadsIob9 = 18, /**<  */
  kTopDarjeelingMuxedPadsIob10 = 19, /**<  */
  kTopDarjeelingMuxedPadsIob11 = 20, /**<  */
  kTopDarjeelingMuxedPadsIob12 = 21, /**<  */
  kTopDarjeelingMuxedPadsIoc0 = 22, /**<  */
  kTopDarjeelingMuxedPadsIoc1 = 23, /**<  */
  kTopDarjeelingMuxedPadsIoc2 = 24, /**<  */
  kTopDarjeelingMuxedPadsIoc3 = 25, /**<  */
  kTopDarjeelingMuxedPadsIoc4 = 26, /**<  */
  kTopDarjeelingMuxedPadsIoc5 = 27, /**<  */
  kTopDarjeelingMuxedPadsIoc6 = 28, /**<  */
  kTopDarjeelingMuxedPadsIoc7 = 29, /**<  */
  kTopDarjeelingMuxedPadsIoc8 = 30, /**<  */
  kTopDarjeelingMuxedPadsIoc9 = 31, /**<  */
  kTopDarjeelingMuxedPadsIoc10 = 32, /**<  */
  kTopDarjeelingMuxedPadsIoc11 = 33, /**<  */
  kTopDarjeelingMuxedPadsIoc12 = 34, /**<  */
  kTopDarjeelingMuxedPadsIor0 = 35, /**<  */
  kTopDarjeelingMuxedPadsIor1 = 36, /**<  */
  kTopDarjeelingMuxedPadsIor2 = 37, /**<  */
  kTopDarjeelingMuxedPadsIor3 = 38, /**<  */
  kTopDarjeelingMuxedPadsIor4 = 39, /**<  */
  kTopDarjeelingMuxedPadsIor5 = 40, /**<  */
  kTopDarjeelingMuxedPadsIor6 = 41, /**<  */
  kTopDarjeelingMuxedPadsIor7 = 42, /**<  */
  kTopDarjeelingMuxedPadsIor10 = 43, /**<  */
  kTopDarjeelingMuxedPadsIor11 = 44, /**<  */
  kTopDarjeelingMuxedPadsIor12 = 45, /**<  */
  kTopDarjeelingMuxedPadsIor13 = 46, /**<  */
  kTopDarjeelingMuxedPadsLast = 46, /**< \internal Last valid muxed pad */
} top_darjeeling_muxed_pads_t;

/**
 * Power Manager Wakeup Signals
 */
typedef enum top_darjeeling_power_manager_wake_ups {
  kTopDarjeelingPowerManagerWakeUpsSysrstCtrlAonWkupReq = 0, /**<  */
  kTopDarjeelingPowerManagerWakeUpsAdcCtrlAonWkupReq = 1, /**<  */
  kTopDarjeelingPowerManagerWakeUpsPinmuxAonPinWkupReq = 2, /**<  */
  kTopDarjeelingPowerManagerWakeUpsPinmuxAonUsbWkupReq = 3, /**<  */
  kTopDarjeelingPowerManagerWakeUpsAonTimerAonWkupReq = 4, /**<  */
  kTopDarjeelingPowerManagerWakeUpsSensorCtrlWkupReq = 5, /**<  */
  kTopDarjeelingPowerManagerWakeUpsSocProxyWkupInternalReq = 6, /**<  */
  kTopDarjeelingPowerManagerWakeUpsSocProxyWkupExternalReq = 7, /**<  */
  kTopDarjeelingPowerManagerWakeUpsLast = 7, /**< \internal Last valid pwrmgr wakeup signal */
} top_darjeeling_power_manager_wake_ups_t;

/**
 * Reset Manager Software Controlled Resets
 */
typedef enum top_darjeeling_reset_manager_sw_resets {
  kTopDarjeelingResetManagerSwResetsSpiDevice = 0, /**<  */
  kTopDarjeelingResetManagerSwResetsSpiHost0 = 1, /**<  */
  kTopDarjeelingResetManagerSwResetsSpiHost1 = 2, /**<  */
  kTopDarjeelingResetManagerSwResetsUsb = 3, /**<  */
  kTopDarjeelingResetManagerSwResetsUsbAon = 4, /**<  */
  kTopDarjeelingResetManagerSwResetsI2c0 = 5, /**<  */
  kTopDarjeelingResetManagerSwResetsI2c1 = 6, /**<  */
  kTopDarjeelingResetManagerSwResetsI2c2 = 7, /**<  */
  kTopDarjeelingResetManagerSwResetsLast = 7, /**< \internal Last valid rstmgr software reset request */
} top_darjeeling_reset_manager_sw_resets_t;

/**
 * Power Manager Reset Request Signals
 */
typedef enum top_darjeeling_power_manager_reset_requests {
  kTopDarjeelingPowerManagerResetRequestsSysrstCtrlAonRstReq = 0, /**<  */
  kTopDarjeelingPowerManagerResetRequestsAonTimerAonAonTimerRstReq = 1, /**<  */
  kTopDarjeelingPowerManagerResetRequestsSocProxyRstReqExternal = 2, /**<  */
  kTopDarjeelingPowerManagerResetRequestsLast = 2, /**< \internal Last valid pwrmgr reset_request signal */
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
#define TOP_DARJEELING_MMIO_SIZE_BYTES 0x11F08080u

// Header Extern Guard
#ifdef __cplusplus
}  // extern "C"
#endif

#endif  // OPENTITAN_HW_TOP_DARJEELING_SW_AUTOGEN_TOP_DARJEELING_H_
