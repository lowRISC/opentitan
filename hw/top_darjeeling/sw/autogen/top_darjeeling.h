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
#define TOP_DARJEELING_UART0_BASE_ADDR 0x40000000u

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
 * Peripheral base address for uart1 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_UART1_BASE_ADDR 0x40010000u

/**
 * Peripheral size for uart1 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_UART1_BASE_ADDR and
 * `TOP_DARJEELING_UART1_BASE_ADDR + TOP_DARJEELING_UART1_SIZE_BYTES`.
 */
#define TOP_DARJEELING_UART1_SIZE_BYTES 0x40u

/**
 * Peripheral base address for uart2 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_UART2_BASE_ADDR 0x40020000u

/**
 * Peripheral size for uart2 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_UART2_BASE_ADDR and
 * `TOP_DARJEELING_UART2_BASE_ADDR + TOP_DARJEELING_UART2_SIZE_BYTES`.
 */
#define TOP_DARJEELING_UART2_SIZE_BYTES 0x40u

/**
 * Peripheral base address for uart3 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_UART3_BASE_ADDR 0x40030000u

/**
 * Peripheral size for uart3 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_UART3_BASE_ADDR and
 * `TOP_DARJEELING_UART3_BASE_ADDR + TOP_DARJEELING_UART3_SIZE_BYTES`.
 */
#define TOP_DARJEELING_UART3_SIZE_BYTES 0x40u

/**
 * Peripheral base address for gpio in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_GPIO_BASE_ADDR 0x40040000u

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
#define TOP_DARJEELING_SPI_DEVICE_BASE_ADDR 0x40050000u

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
#define TOP_DARJEELING_I2C0_BASE_ADDR 0x40080000u

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
#define TOP_DARJEELING_I2C1_BASE_ADDR 0x40090000u

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
#define TOP_DARJEELING_I2C2_BASE_ADDR 0x400A0000u

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
 * Peripheral base address for pattgen in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_PATTGEN_BASE_ADDR 0x400E0000u

/**
 * Peripheral size for pattgen in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_PATTGEN_BASE_ADDR and
 * `TOP_DARJEELING_PATTGEN_BASE_ADDR + TOP_DARJEELING_PATTGEN_SIZE_BYTES`.
 */
#define TOP_DARJEELING_PATTGEN_SIZE_BYTES 0x40u

/**
 * Peripheral base address for rv_timer in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_RV_TIMER_BASE_ADDR 0x40100000u

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
#define TOP_DARJEELING_OTP_CTRL_CORE_BASE_ADDR 0x40130000u

/**
 * Peripheral size for core device on otp_ctrl in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_OTP_CTRL_CORE_BASE_ADDR and
 * `TOP_DARJEELING_OTP_CTRL_CORE_BASE_ADDR + TOP_DARJEELING_OTP_CTRL_CORE_SIZE_BYTES`.
 */
#define TOP_DARJEELING_OTP_CTRL_CORE_SIZE_BYTES 0x2000u

/**
 * Peripheral base address for prim device on otp_ctrl in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_OTP_CTRL_PRIM_BASE_ADDR 0x40132000u

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
#define TOP_DARJEELING_LC_CTRL_BASE_ADDR 0x40140000u

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
#define TOP_DARJEELING_ALERT_HANDLER_BASE_ADDR 0x40150000u

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
#define TOP_DARJEELING_SPI_HOST0_BASE_ADDR 0x40300000u

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
#define TOP_DARJEELING_SPI_HOST1_BASE_ADDR 0x40310000u

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
#define TOP_DARJEELING_USBDEV_BASE_ADDR 0x40320000u

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
#define TOP_DARJEELING_PWRMGR_AON_BASE_ADDR 0x40400000u

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
#define TOP_DARJEELING_RSTMGR_AON_BASE_ADDR 0x40410000u

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
#define TOP_DARJEELING_CLKMGR_AON_BASE_ADDR 0x40420000u

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
#define TOP_DARJEELING_SYSRST_CTRL_AON_BASE_ADDR 0x40430000u

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
#define TOP_DARJEELING_ADC_CTRL_AON_BASE_ADDR 0x40440000u

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
 * Peripheral base address for pwm_aon in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_PWM_AON_BASE_ADDR 0x40450000u

/**
 * Peripheral size for pwm_aon in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_PWM_AON_BASE_ADDR and
 * `TOP_DARJEELING_PWM_AON_BASE_ADDR + TOP_DARJEELING_PWM_AON_SIZE_BYTES`.
 */
#define TOP_DARJEELING_PWM_AON_SIZE_BYTES 0x80u

/**
 * Peripheral base address for pinmux_aon in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_PINMUX_AON_BASE_ADDR 0x40460000u

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
#define TOP_DARJEELING_AON_TIMER_AON_BASE_ADDR 0x40470000u

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
#define TOP_DARJEELING_AST_BASE_ADDR 0x40480000u

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
#define TOP_DARJEELING_SENSOR_CTRL_BASE_ADDR 0x40490000u

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
 * Peripheral base address for regs device on sram_ctrl_ret_aon in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_SRAM_CTRL_RET_AON_REGS_BASE_ADDR 0x40500000u

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
#define TOP_DARJEELING_SRAM_CTRL_RET_AON_RAM_BASE_ADDR 0x40600000u

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
#define TOP_DARJEELING_FLASH_CTRL_CORE_BASE_ADDR 0x41000000u

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
#define TOP_DARJEELING_FLASH_CTRL_PRIM_BASE_ADDR 0x41008000u

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
#define TOP_DARJEELING_FLASH_CTRL_MEM_BASE_ADDR 0x20000000u

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
#define TOP_DARJEELING_RV_DM_REGS_BASE_ADDR 0x41200000u

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
#define TOP_DARJEELING_RV_DM_MEM_BASE_ADDR 0x10000u

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
#define TOP_DARJEELING_RV_PLIC_BASE_ADDR 0x48000000u

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
#define TOP_DARJEELING_AES_BASE_ADDR 0x41100000u

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
#define TOP_DARJEELING_HMAC_BASE_ADDR 0x41110000u

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
#define TOP_DARJEELING_KMAC_BASE_ADDR 0x41120000u

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
#define TOP_DARJEELING_OTBN_BASE_ADDR 0x41130000u

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
#define TOP_DARJEELING_KEYMGR_BASE_ADDR 0x41140000u

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
#define TOP_DARJEELING_CSRNG_BASE_ADDR 0x41150000u

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
 * Peripheral base address for entropy_src in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_ENTROPY_SRC_BASE_ADDR 0x41160000u

/**
 * Peripheral size for entropy_src in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_ENTROPY_SRC_BASE_ADDR and
 * `TOP_DARJEELING_ENTROPY_SRC_BASE_ADDR + TOP_DARJEELING_ENTROPY_SRC_SIZE_BYTES`.
 */
#define TOP_DARJEELING_ENTROPY_SRC_SIZE_BYTES 0x100u

/**
 * Peripheral base address for edn0 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_EDN0_BASE_ADDR 0x41170000u

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
#define TOP_DARJEELING_EDN1_BASE_ADDR 0x41180000u

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
#define TOP_DARJEELING_SRAM_CTRL_MAIN_REGS_BASE_ADDR 0x411C0000u

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
#define TOP_DARJEELING_SRAM_CTRL_MBOX_REGS_BASE_ADDR 0x411D0000u

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
#define TOP_DARJEELING_ROM_CTRL0_REGS_BASE_ADDR 0x411E0000u

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
#define TOP_DARJEELING_ROM_CTRL1_REGS_BASE_ADDR 0x41210000u

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
#define TOP_DARJEELING_ROM_CTRL1_ROM_BASE_ADDR 0x50000u

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
 * Peripheral base address for cfg device on rv_core_ibex in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_RV_CORE_IBEX_CFG_BASE_ADDR 0x411F0000u

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
 * Memory base address for ram_ret_aon in top darjeeling.
 */
#define TOP_DARJEELING_RAM_RET_AON_BASE_ADDR 0x40600000u

/**
 * Memory size for ram_ret_aon in top darjeeling.
 */
#define TOP_DARJEELING_RAM_RET_AON_SIZE_BYTES 0x1000u

/**
 * Memory base address for eflash in top darjeeling.
 */
#define TOP_DARJEELING_EFLASH_BASE_ADDR 0x20000000u

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
#define TOP_DARJEELING_ROM1_BASE_ADDR 0x50000u

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
  kTopDarjeelingPlicPeripheralUart1 = 2, /**< uart1 */
  kTopDarjeelingPlicPeripheralUart2 = 3, /**< uart2 */
  kTopDarjeelingPlicPeripheralUart3 = 4, /**< uart3 */
  kTopDarjeelingPlicPeripheralGpio = 5, /**< gpio */
  kTopDarjeelingPlicPeripheralSpiDevice = 6, /**< spi_device */
  kTopDarjeelingPlicPeripheralI2c0 = 7, /**< i2c0 */
  kTopDarjeelingPlicPeripheralI2c1 = 8, /**< i2c1 */
  kTopDarjeelingPlicPeripheralI2c2 = 9, /**< i2c2 */
  kTopDarjeelingPlicPeripheralPattgen = 10, /**< pattgen */
  kTopDarjeelingPlicPeripheralRvTimer = 11, /**< rv_timer */
  kTopDarjeelingPlicPeripheralOtpCtrl = 12, /**< otp_ctrl */
  kTopDarjeelingPlicPeripheralAlertHandler = 13, /**< alert_handler */
  kTopDarjeelingPlicPeripheralSpiHost0 = 14, /**< spi_host0 */
  kTopDarjeelingPlicPeripheralSpiHost1 = 15, /**< spi_host1 */
  kTopDarjeelingPlicPeripheralUsbdev = 16, /**< usbdev */
  kTopDarjeelingPlicPeripheralPwrmgrAon = 17, /**< pwrmgr_aon */
  kTopDarjeelingPlicPeripheralSysrstCtrlAon = 18, /**< sysrst_ctrl_aon */
  kTopDarjeelingPlicPeripheralAdcCtrlAon = 19, /**< adc_ctrl_aon */
  kTopDarjeelingPlicPeripheralAonTimerAon = 20, /**< aon_timer_aon */
  kTopDarjeelingPlicPeripheralSensorCtrl = 21, /**< sensor_ctrl */
  kTopDarjeelingPlicPeripheralFlashCtrl = 22, /**< flash_ctrl */
  kTopDarjeelingPlicPeripheralHmac = 23, /**< hmac */
  kTopDarjeelingPlicPeripheralKmac = 24, /**< kmac */
  kTopDarjeelingPlicPeripheralOtbn = 25, /**< otbn */
  kTopDarjeelingPlicPeripheralKeymgr = 26, /**< keymgr */
  kTopDarjeelingPlicPeripheralCsrng = 27, /**< csrng */
  kTopDarjeelingPlicPeripheralEntropySrc = 28, /**< entropy_src */
  kTopDarjeelingPlicPeripheralEdn0 = 29, /**< edn0 */
  kTopDarjeelingPlicPeripheralEdn1 = 30, /**< edn1 */
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
  kTopDarjeelingPlicIrqIdUart1TxWatermark = 9, /**< uart1_tx_watermark */
  kTopDarjeelingPlicIrqIdUart1RxWatermark = 10, /**< uart1_rx_watermark */
  kTopDarjeelingPlicIrqIdUart1TxEmpty = 11, /**< uart1_tx_empty */
  kTopDarjeelingPlicIrqIdUart1RxOverflow = 12, /**< uart1_rx_overflow */
  kTopDarjeelingPlicIrqIdUart1RxFrameErr = 13, /**< uart1_rx_frame_err */
  kTopDarjeelingPlicIrqIdUart1RxBreakErr = 14, /**< uart1_rx_break_err */
  kTopDarjeelingPlicIrqIdUart1RxTimeout = 15, /**< uart1_rx_timeout */
  kTopDarjeelingPlicIrqIdUart1RxParityErr = 16, /**< uart1_rx_parity_err */
  kTopDarjeelingPlicIrqIdUart2TxWatermark = 17, /**< uart2_tx_watermark */
  kTopDarjeelingPlicIrqIdUart2RxWatermark = 18, /**< uart2_rx_watermark */
  kTopDarjeelingPlicIrqIdUart2TxEmpty = 19, /**< uart2_tx_empty */
  kTopDarjeelingPlicIrqIdUart2RxOverflow = 20, /**< uart2_rx_overflow */
  kTopDarjeelingPlicIrqIdUart2RxFrameErr = 21, /**< uart2_rx_frame_err */
  kTopDarjeelingPlicIrqIdUart2RxBreakErr = 22, /**< uart2_rx_break_err */
  kTopDarjeelingPlicIrqIdUart2RxTimeout = 23, /**< uart2_rx_timeout */
  kTopDarjeelingPlicIrqIdUart2RxParityErr = 24, /**< uart2_rx_parity_err */
  kTopDarjeelingPlicIrqIdUart3TxWatermark = 25, /**< uart3_tx_watermark */
  kTopDarjeelingPlicIrqIdUart3RxWatermark = 26, /**< uart3_rx_watermark */
  kTopDarjeelingPlicIrqIdUart3TxEmpty = 27, /**< uart3_tx_empty */
  kTopDarjeelingPlicIrqIdUart3RxOverflow = 28, /**< uart3_rx_overflow */
  kTopDarjeelingPlicIrqIdUart3RxFrameErr = 29, /**< uart3_rx_frame_err */
  kTopDarjeelingPlicIrqIdUart3RxBreakErr = 30, /**< uart3_rx_break_err */
  kTopDarjeelingPlicIrqIdUart3RxTimeout = 31, /**< uart3_rx_timeout */
  kTopDarjeelingPlicIrqIdUart3RxParityErr = 32, /**< uart3_rx_parity_err */
  kTopDarjeelingPlicIrqIdGpioGpio0 = 33, /**< gpio_gpio 0 */
  kTopDarjeelingPlicIrqIdGpioGpio1 = 34, /**< gpio_gpio 1 */
  kTopDarjeelingPlicIrqIdGpioGpio2 = 35, /**< gpio_gpio 2 */
  kTopDarjeelingPlicIrqIdGpioGpio3 = 36, /**< gpio_gpio 3 */
  kTopDarjeelingPlicIrqIdGpioGpio4 = 37, /**< gpio_gpio 4 */
  kTopDarjeelingPlicIrqIdGpioGpio5 = 38, /**< gpio_gpio 5 */
  kTopDarjeelingPlicIrqIdGpioGpio6 = 39, /**< gpio_gpio 6 */
  kTopDarjeelingPlicIrqIdGpioGpio7 = 40, /**< gpio_gpio 7 */
  kTopDarjeelingPlicIrqIdGpioGpio8 = 41, /**< gpio_gpio 8 */
  kTopDarjeelingPlicIrqIdGpioGpio9 = 42, /**< gpio_gpio 9 */
  kTopDarjeelingPlicIrqIdGpioGpio10 = 43, /**< gpio_gpio 10 */
  kTopDarjeelingPlicIrqIdGpioGpio11 = 44, /**< gpio_gpio 11 */
  kTopDarjeelingPlicIrqIdGpioGpio12 = 45, /**< gpio_gpio 12 */
  kTopDarjeelingPlicIrqIdGpioGpio13 = 46, /**< gpio_gpio 13 */
  kTopDarjeelingPlicIrqIdGpioGpio14 = 47, /**< gpio_gpio 14 */
  kTopDarjeelingPlicIrqIdGpioGpio15 = 48, /**< gpio_gpio 15 */
  kTopDarjeelingPlicIrqIdGpioGpio16 = 49, /**< gpio_gpio 16 */
  kTopDarjeelingPlicIrqIdGpioGpio17 = 50, /**< gpio_gpio 17 */
  kTopDarjeelingPlicIrqIdGpioGpio18 = 51, /**< gpio_gpio 18 */
  kTopDarjeelingPlicIrqIdGpioGpio19 = 52, /**< gpio_gpio 19 */
  kTopDarjeelingPlicIrqIdGpioGpio20 = 53, /**< gpio_gpio 20 */
  kTopDarjeelingPlicIrqIdGpioGpio21 = 54, /**< gpio_gpio 21 */
  kTopDarjeelingPlicIrqIdGpioGpio22 = 55, /**< gpio_gpio 22 */
  kTopDarjeelingPlicIrqIdGpioGpio23 = 56, /**< gpio_gpio 23 */
  kTopDarjeelingPlicIrqIdGpioGpio24 = 57, /**< gpio_gpio 24 */
  kTopDarjeelingPlicIrqIdGpioGpio25 = 58, /**< gpio_gpio 25 */
  kTopDarjeelingPlicIrqIdGpioGpio26 = 59, /**< gpio_gpio 26 */
  kTopDarjeelingPlicIrqIdGpioGpio27 = 60, /**< gpio_gpio 27 */
  kTopDarjeelingPlicIrqIdGpioGpio28 = 61, /**< gpio_gpio 28 */
  kTopDarjeelingPlicIrqIdGpioGpio29 = 62, /**< gpio_gpio 29 */
  kTopDarjeelingPlicIrqIdGpioGpio30 = 63, /**< gpio_gpio 30 */
  kTopDarjeelingPlicIrqIdGpioGpio31 = 64, /**< gpio_gpio 31 */
  kTopDarjeelingPlicIrqIdSpiDeviceGenericRxFull = 65, /**< spi_device_generic_rx_full */
  kTopDarjeelingPlicIrqIdSpiDeviceGenericRxWatermark = 66, /**< spi_device_generic_rx_watermark */
  kTopDarjeelingPlicIrqIdSpiDeviceGenericTxWatermark = 67, /**< spi_device_generic_tx_watermark */
  kTopDarjeelingPlicIrqIdSpiDeviceGenericRxError = 68, /**< spi_device_generic_rx_error */
  kTopDarjeelingPlicIrqIdSpiDeviceGenericRxOverflow = 69, /**< spi_device_generic_rx_overflow */
  kTopDarjeelingPlicIrqIdSpiDeviceGenericTxUnderflow = 70, /**< spi_device_generic_tx_underflow */
  kTopDarjeelingPlicIrqIdSpiDeviceUploadCmdfifoNotEmpty = 71, /**< spi_device_upload_cmdfifo_not_empty */
  kTopDarjeelingPlicIrqIdSpiDeviceUploadPayloadNotEmpty = 72, /**< spi_device_upload_payload_not_empty */
  kTopDarjeelingPlicIrqIdSpiDeviceUploadPayloadOverflow = 73, /**< spi_device_upload_payload_overflow */
  kTopDarjeelingPlicIrqIdSpiDeviceReadbufWatermark = 74, /**< spi_device_readbuf_watermark */
  kTopDarjeelingPlicIrqIdSpiDeviceReadbufFlip = 75, /**< spi_device_readbuf_flip */
  kTopDarjeelingPlicIrqIdSpiDeviceTpmHeaderNotEmpty = 76, /**< spi_device_tpm_header_not_empty */
  kTopDarjeelingPlicIrqIdI2c0FmtThreshold = 77, /**< i2c0_fmt_threshold */
  kTopDarjeelingPlicIrqIdI2c0RxThreshold = 78, /**< i2c0_rx_threshold */
  kTopDarjeelingPlicIrqIdI2c0FmtOverflow = 79, /**< i2c0_fmt_overflow */
  kTopDarjeelingPlicIrqIdI2c0RxOverflow = 80, /**< i2c0_rx_overflow */
  kTopDarjeelingPlicIrqIdI2c0Nak = 81, /**< i2c0_nak */
  kTopDarjeelingPlicIrqIdI2c0SclInterference = 82, /**< i2c0_scl_interference */
  kTopDarjeelingPlicIrqIdI2c0SdaInterference = 83, /**< i2c0_sda_interference */
  kTopDarjeelingPlicIrqIdI2c0StretchTimeout = 84, /**< i2c0_stretch_timeout */
  kTopDarjeelingPlicIrqIdI2c0SdaUnstable = 85, /**< i2c0_sda_unstable */
  kTopDarjeelingPlicIrqIdI2c0CmdComplete = 86, /**< i2c0_cmd_complete */
  kTopDarjeelingPlicIrqIdI2c0TxStretch = 87, /**< i2c0_tx_stretch */
  kTopDarjeelingPlicIrqIdI2c0TxOverflow = 88, /**< i2c0_tx_overflow */
  kTopDarjeelingPlicIrqIdI2c0AcqFull = 89, /**< i2c0_acq_full */
  kTopDarjeelingPlicIrqIdI2c0UnexpStop = 90, /**< i2c0_unexp_stop */
  kTopDarjeelingPlicIrqIdI2c0HostTimeout = 91, /**< i2c0_host_timeout */
  kTopDarjeelingPlicIrqIdI2c1FmtThreshold = 92, /**< i2c1_fmt_threshold */
  kTopDarjeelingPlicIrqIdI2c1RxThreshold = 93, /**< i2c1_rx_threshold */
  kTopDarjeelingPlicIrqIdI2c1FmtOverflow = 94, /**< i2c1_fmt_overflow */
  kTopDarjeelingPlicIrqIdI2c1RxOverflow = 95, /**< i2c1_rx_overflow */
  kTopDarjeelingPlicIrqIdI2c1Nak = 96, /**< i2c1_nak */
  kTopDarjeelingPlicIrqIdI2c1SclInterference = 97, /**< i2c1_scl_interference */
  kTopDarjeelingPlicIrqIdI2c1SdaInterference = 98, /**< i2c1_sda_interference */
  kTopDarjeelingPlicIrqIdI2c1StretchTimeout = 99, /**< i2c1_stretch_timeout */
  kTopDarjeelingPlicIrqIdI2c1SdaUnstable = 100, /**< i2c1_sda_unstable */
  kTopDarjeelingPlicIrqIdI2c1CmdComplete = 101, /**< i2c1_cmd_complete */
  kTopDarjeelingPlicIrqIdI2c1TxStretch = 102, /**< i2c1_tx_stretch */
  kTopDarjeelingPlicIrqIdI2c1TxOverflow = 103, /**< i2c1_tx_overflow */
  kTopDarjeelingPlicIrqIdI2c1AcqFull = 104, /**< i2c1_acq_full */
  kTopDarjeelingPlicIrqIdI2c1UnexpStop = 105, /**< i2c1_unexp_stop */
  kTopDarjeelingPlicIrqIdI2c1HostTimeout = 106, /**< i2c1_host_timeout */
  kTopDarjeelingPlicIrqIdI2c2FmtThreshold = 107, /**< i2c2_fmt_threshold */
  kTopDarjeelingPlicIrqIdI2c2RxThreshold = 108, /**< i2c2_rx_threshold */
  kTopDarjeelingPlicIrqIdI2c2FmtOverflow = 109, /**< i2c2_fmt_overflow */
  kTopDarjeelingPlicIrqIdI2c2RxOverflow = 110, /**< i2c2_rx_overflow */
  kTopDarjeelingPlicIrqIdI2c2Nak = 111, /**< i2c2_nak */
  kTopDarjeelingPlicIrqIdI2c2SclInterference = 112, /**< i2c2_scl_interference */
  kTopDarjeelingPlicIrqIdI2c2SdaInterference = 113, /**< i2c2_sda_interference */
  kTopDarjeelingPlicIrqIdI2c2StretchTimeout = 114, /**< i2c2_stretch_timeout */
  kTopDarjeelingPlicIrqIdI2c2SdaUnstable = 115, /**< i2c2_sda_unstable */
  kTopDarjeelingPlicIrqIdI2c2CmdComplete = 116, /**< i2c2_cmd_complete */
  kTopDarjeelingPlicIrqIdI2c2TxStretch = 117, /**< i2c2_tx_stretch */
  kTopDarjeelingPlicIrqIdI2c2TxOverflow = 118, /**< i2c2_tx_overflow */
  kTopDarjeelingPlicIrqIdI2c2AcqFull = 119, /**< i2c2_acq_full */
  kTopDarjeelingPlicIrqIdI2c2UnexpStop = 120, /**< i2c2_unexp_stop */
  kTopDarjeelingPlicIrqIdI2c2HostTimeout = 121, /**< i2c2_host_timeout */
  kTopDarjeelingPlicIrqIdPattgenDoneCh0 = 122, /**< pattgen_done_ch0 */
  kTopDarjeelingPlicIrqIdPattgenDoneCh1 = 123, /**< pattgen_done_ch1 */
  kTopDarjeelingPlicIrqIdRvTimerTimerExpiredHart0Timer0 = 124, /**< rv_timer_timer_expired_hart0_timer0 */
  kTopDarjeelingPlicIrqIdOtpCtrlOtpOperationDone = 125, /**< otp_ctrl_otp_operation_done */
  kTopDarjeelingPlicIrqIdOtpCtrlOtpError = 126, /**< otp_ctrl_otp_error */
  kTopDarjeelingPlicIrqIdAlertHandlerClassa = 127, /**< alert_handler_classa */
  kTopDarjeelingPlicIrqIdAlertHandlerClassb = 128, /**< alert_handler_classb */
  kTopDarjeelingPlicIrqIdAlertHandlerClassc = 129, /**< alert_handler_classc */
  kTopDarjeelingPlicIrqIdAlertHandlerClassd = 130, /**< alert_handler_classd */
  kTopDarjeelingPlicIrqIdSpiHost0Error = 131, /**< spi_host0_error */
  kTopDarjeelingPlicIrqIdSpiHost0SpiEvent = 132, /**< spi_host0_spi_event */
  kTopDarjeelingPlicIrqIdSpiHost1Error = 133, /**< spi_host1_error */
  kTopDarjeelingPlicIrqIdSpiHost1SpiEvent = 134, /**< spi_host1_spi_event */
  kTopDarjeelingPlicIrqIdUsbdevPktReceived = 135, /**< usbdev_pkt_received */
  kTopDarjeelingPlicIrqIdUsbdevPktSent = 136, /**< usbdev_pkt_sent */
  kTopDarjeelingPlicIrqIdUsbdevDisconnected = 137, /**< usbdev_disconnected */
  kTopDarjeelingPlicIrqIdUsbdevHostLost = 138, /**< usbdev_host_lost */
  kTopDarjeelingPlicIrqIdUsbdevLinkReset = 139, /**< usbdev_link_reset */
  kTopDarjeelingPlicIrqIdUsbdevLinkSuspend = 140, /**< usbdev_link_suspend */
  kTopDarjeelingPlicIrqIdUsbdevLinkResume = 141, /**< usbdev_link_resume */
  kTopDarjeelingPlicIrqIdUsbdevAvEmpty = 142, /**< usbdev_av_empty */
  kTopDarjeelingPlicIrqIdUsbdevRxFull = 143, /**< usbdev_rx_full */
  kTopDarjeelingPlicIrqIdUsbdevAvOverflow = 144, /**< usbdev_av_overflow */
  kTopDarjeelingPlicIrqIdUsbdevLinkInErr = 145, /**< usbdev_link_in_err */
  kTopDarjeelingPlicIrqIdUsbdevRxCrcErr = 146, /**< usbdev_rx_crc_err */
  kTopDarjeelingPlicIrqIdUsbdevRxPidErr = 147, /**< usbdev_rx_pid_err */
  kTopDarjeelingPlicIrqIdUsbdevRxBitstuffErr = 148, /**< usbdev_rx_bitstuff_err */
  kTopDarjeelingPlicIrqIdUsbdevFrame = 149, /**< usbdev_frame */
  kTopDarjeelingPlicIrqIdUsbdevPowered = 150, /**< usbdev_powered */
  kTopDarjeelingPlicIrqIdUsbdevLinkOutErr = 151, /**< usbdev_link_out_err */
  kTopDarjeelingPlicIrqIdPwrmgrAonWakeup = 152, /**< pwrmgr_aon_wakeup */
  kTopDarjeelingPlicIrqIdSysrstCtrlAonEventDetected = 153, /**< sysrst_ctrl_aon_event_detected */
  kTopDarjeelingPlicIrqIdAdcCtrlAonMatchDone = 154, /**< adc_ctrl_aon_match_done */
  kTopDarjeelingPlicIrqIdAonTimerAonWkupTimerExpired = 155, /**< aon_timer_aon_wkup_timer_expired */
  kTopDarjeelingPlicIrqIdAonTimerAonWdogTimerBark = 156, /**< aon_timer_aon_wdog_timer_bark */
  kTopDarjeelingPlicIrqIdSensorCtrlIoStatusChange = 157, /**< sensor_ctrl_io_status_change */
  kTopDarjeelingPlicIrqIdSensorCtrlInitStatusChange = 158, /**< sensor_ctrl_init_status_change */
  kTopDarjeelingPlicIrqIdFlashCtrlProgEmpty = 159, /**< flash_ctrl_prog_empty */
  kTopDarjeelingPlicIrqIdFlashCtrlProgLvl = 160, /**< flash_ctrl_prog_lvl */
  kTopDarjeelingPlicIrqIdFlashCtrlRdFull = 161, /**< flash_ctrl_rd_full */
  kTopDarjeelingPlicIrqIdFlashCtrlRdLvl = 162, /**< flash_ctrl_rd_lvl */
  kTopDarjeelingPlicIrqIdFlashCtrlOpDone = 163, /**< flash_ctrl_op_done */
  kTopDarjeelingPlicIrqIdFlashCtrlCorrErr = 164, /**< flash_ctrl_corr_err */
  kTopDarjeelingPlicIrqIdHmacHmacDone = 165, /**< hmac_hmac_done */
  kTopDarjeelingPlicIrqIdHmacFifoEmpty = 166, /**< hmac_fifo_empty */
  kTopDarjeelingPlicIrqIdHmacHmacErr = 167, /**< hmac_hmac_err */
  kTopDarjeelingPlicIrqIdKmacKmacDone = 168, /**< kmac_kmac_done */
  kTopDarjeelingPlicIrqIdKmacFifoEmpty = 169, /**< kmac_fifo_empty */
  kTopDarjeelingPlicIrqIdKmacKmacErr = 170, /**< kmac_kmac_err */
  kTopDarjeelingPlicIrqIdOtbnDone = 171, /**< otbn_done */
  kTopDarjeelingPlicIrqIdKeymgrOpDone = 172, /**< keymgr_op_done */
  kTopDarjeelingPlicIrqIdCsrngCsCmdReqDone = 173, /**< csrng_cs_cmd_req_done */
  kTopDarjeelingPlicIrqIdCsrngCsEntropyReq = 174, /**< csrng_cs_entropy_req */
  kTopDarjeelingPlicIrqIdCsrngCsHwInstExc = 175, /**< csrng_cs_hw_inst_exc */
  kTopDarjeelingPlicIrqIdCsrngCsFatalErr = 176, /**< csrng_cs_fatal_err */
  kTopDarjeelingPlicIrqIdEntropySrcEsEntropyValid = 177, /**< entropy_src_es_entropy_valid */
  kTopDarjeelingPlicIrqIdEntropySrcEsHealthTestFailed = 178, /**< entropy_src_es_health_test_failed */
  kTopDarjeelingPlicIrqIdEntropySrcEsObserveFifoReady = 179, /**< entropy_src_es_observe_fifo_ready */
  kTopDarjeelingPlicIrqIdEntropySrcEsFatalErr = 180, /**< entropy_src_es_fatal_err */
  kTopDarjeelingPlicIrqIdEdn0EdnCmdReqDone = 181, /**< edn0_edn_cmd_req_done */
  kTopDarjeelingPlicIrqIdEdn0EdnFatalErr = 182, /**< edn0_edn_fatal_err */
  kTopDarjeelingPlicIrqIdEdn1EdnCmdReqDone = 183, /**< edn1_edn_cmd_req_done */
  kTopDarjeelingPlicIrqIdEdn1EdnFatalErr = 184, /**< edn1_edn_fatal_err */
  kTopDarjeelingPlicIrqIdLast = 184, /**< \internal The Last Valid Interrupt ID. */
} top_darjeeling_plic_irq_id_t;

/**
 * PLIC Interrupt Source to Peripheral Map
 *
 * This array is a mapping from `top_darjeeling_plic_irq_id_t` to
 * `top_darjeeling_plic_peripheral_t`.
 */
extern const top_darjeeling_plic_peripheral_t
    top_darjeeling_plic_interrupt_for_peripheral[185];

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
  kTopDarjeelingAlertPeripheralUart1 = 1, /**< uart1 */
  kTopDarjeelingAlertPeripheralUart2 = 2, /**< uart2 */
  kTopDarjeelingAlertPeripheralUart3 = 3, /**< uart3 */
  kTopDarjeelingAlertPeripheralGpio = 4, /**< gpio */
  kTopDarjeelingAlertPeripheralSpiDevice = 5, /**< spi_device */
  kTopDarjeelingAlertPeripheralI2c0 = 6, /**< i2c0 */
  kTopDarjeelingAlertPeripheralI2c1 = 7, /**< i2c1 */
  kTopDarjeelingAlertPeripheralI2c2 = 8, /**< i2c2 */
  kTopDarjeelingAlertPeripheralPattgen = 9, /**< pattgen */
  kTopDarjeelingAlertPeripheralRvTimer = 10, /**< rv_timer */
  kTopDarjeelingAlertPeripheralOtpCtrl = 11, /**< otp_ctrl */
  kTopDarjeelingAlertPeripheralLcCtrl = 12, /**< lc_ctrl */
  kTopDarjeelingAlertPeripheralSpiHost0 = 13, /**< spi_host0 */
  kTopDarjeelingAlertPeripheralSpiHost1 = 14, /**< spi_host1 */
  kTopDarjeelingAlertPeripheralUsbdev = 15, /**< usbdev */
  kTopDarjeelingAlertPeripheralPwrmgrAon = 16, /**< pwrmgr_aon */
  kTopDarjeelingAlertPeripheralRstmgrAon = 17, /**< rstmgr_aon */
  kTopDarjeelingAlertPeripheralClkmgrAon = 18, /**< clkmgr_aon */
  kTopDarjeelingAlertPeripheralSysrstCtrlAon = 19, /**< sysrst_ctrl_aon */
  kTopDarjeelingAlertPeripheralAdcCtrlAon = 20, /**< adc_ctrl_aon */
  kTopDarjeelingAlertPeripheralPwmAon = 21, /**< pwm_aon */
  kTopDarjeelingAlertPeripheralPinmuxAon = 22, /**< pinmux_aon */
  kTopDarjeelingAlertPeripheralAonTimerAon = 23, /**< aon_timer_aon */
  kTopDarjeelingAlertPeripheralSensorCtrl = 24, /**< sensor_ctrl */
  kTopDarjeelingAlertPeripheralSramCtrlRetAon = 25, /**< sram_ctrl_ret_aon */
  kTopDarjeelingAlertPeripheralFlashCtrl = 26, /**< flash_ctrl */
  kTopDarjeelingAlertPeripheralRvDm = 27, /**< rv_dm */
  kTopDarjeelingAlertPeripheralRvPlic = 28, /**< rv_plic */
  kTopDarjeelingAlertPeripheralAes = 29, /**< aes */
  kTopDarjeelingAlertPeripheralHmac = 30, /**< hmac */
  kTopDarjeelingAlertPeripheralKmac = 31, /**< kmac */
  kTopDarjeelingAlertPeripheralOtbn = 32, /**< otbn */
  kTopDarjeelingAlertPeripheralKeymgr = 33, /**< keymgr */
  kTopDarjeelingAlertPeripheralCsrng = 34, /**< csrng */
  kTopDarjeelingAlertPeripheralEntropySrc = 35, /**< entropy_src */
  kTopDarjeelingAlertPeripheralEdn0 = 36, /**< edn0 */
  kTopDarjeelingAlertPeripheralEdn1 = 37, /**< edn1 */
  kTopDarjeelingAlertPeripheralSramCtrlMain = 38, /**< sram_ctrl_main */
  kTopDarjeelingAlertPeripheralSramCtrlMbox = 39, /**< sram_ctrl_mbox */
  kTopDarjeelingAlertPeripheralRomCtrl0 = 40, /**< rom_ctrl0 */
  kTopDarjeelingAlertPeripheralRomCtrl1 = 41, /**< rom_ctrl1 */
  kTopDarjeelingAlertPeripheralRvCoreIbex = 42, /**< rv_core_ibex */
  kTopDarjeelingAlertPeripheralLast = 42, /**< \internal Final Alert peripheral */
} top_darjeeling_alert_peripheral_t;

/**
 * Alert Handler Alert Source.
 *
 * Enumeration of all Alert Handler Alert Sources. The alert sources belonging to
 * the same peripheral are guaranteed to be consecutive.
 */
typedef enum top_darjeeling_alert_id {
  kTopDarjeelingAlertIdUart0FatalFault = 0, /**< uart0_fatal_fault */
  kTopDarjeelingAlertIdUart1FatalFault = 1, /**< uart1_fatal_fault */
  kTopDarjeelingAlertIdUart2FatalFault = 2, /**< uart2_fatal_fault */
  kTopDarjeelingAlertIdUart3FatalFault = 3, /**< uart3_fatal_fault */
  kTopDarjeelingAlertIdGpioFatalFault = 4, /**< gpio_fatal_fault */
  kTopDarjeelingAlertIdSpiDeviceFatalFault = 5, /**< spi_device_fatal_fault */
  kTopDarjeelingAlertIdI2c0FatalFault = 6, /**< i2c0_fatal_fault */
  kTopDarjeelingAlertIdI2c1FatalFault = 7, /**< i2c1_fatal_fault */
  kTopDarjeelingAlertIdI2c2FatalFault = 8, /**< i2c2_fatal_fault */
  kTopDarjeelingAlertIdPattgenFatalFault = 9, /**< pattgen_fatal_fault */
  kTopDarjeelingAlertIdRvTimerFatalFault = 10, /**< rv_timer_fatal_fault */
  kTopDarjeelingAlertIdOtpCtrlFatalMacroError = 11, /**< otp_ctrl_fatal_macro_error */
  kTopDarjeelingAlertIdOtpCtrlFatalCheckError = 12, /**< otp_ctrl_fatal_check_error */
  kTopDarjeelingAlertIdOtpCtrlFatalBusIntegError = 13, /**< otp_ctrl_fatal_bus_integ_error */
  kTopDarjeelingAlertIdOtpCtrlFatalPrimOtpAlert = 14, /**< otp_ctrl_fatal_prim_otp_alert */
  kTopDarjeelingAlertIdOtpCtrlRecovPrimOtpAlert = 15, /**< otp_ctrl_recov_prim_otp_alert */
  kTopDarjeelingAlertIdLcCtrlFatalProgError = 16, /**< lc_ctrl_fatal_prog_error */
  kTopDarjeelingAlertIdLcCtrlFatalStateError = 17, /**< lc_ctrl_fatal_state_error */
  kTopDarjeelingAlertIdLcCtrlFatalBusIntegError = 18, /**< lc_ctrl_fatal_bus_integ_error */
  kTopDarjeelingAlertIdSpiHost0FatalFault = 19, /**< spi_host0_fatal_fault */
  kTopDarjeelingAlertIdSpiHost1FatalFault = 20, /**< spi_host1_fatal_fault */
  kTopDarjeelingAlertIdUsbdevFatalFault = 21, /**< usbdev_fatal_fault */
  kTopDarjeelingAlertIdPwrmgrAonFatalFault = 22, /**< pwrmgr_aon_fatal_fault */
  kTopDarjeelingAlertIdRstmgrAonFatalFault = 23, /**< rstmgr_aon_fatal_fault */
  kTopDarjeelingAlertIdRstmgrAonFatalCnstyFault = 24, /**< rstmgr_aon_fatal_cnsty_fault */
  kTopDarjeelingAlertIdClkmgrAonRecovFault = 25, /**< clkmgr_aon_recov_fault */
  kTopDarjeelingAlertIdClkmgrAonFatalFault = 26, /**< clkmgr_aon_fatal_fault */
  kTopDarjeelingAlertIdSysrstCtrlAonFatalFault = 27, /**< sysrst_ctrl_aon_fatal_fault */
  kTopDarjeelingAlertIdAdcCtrlAonFatalFault = 28, /**< adc_ctrl_aon_fatal_fault */
  kTopDarjeelingAlertIdPwmAonFatalFault = 29, /**< pwm_aon_fatal_fault */
  kTopDarjeelingAlertIdPinmuxAonFatalFault = 30, /**< pinmux_aon_fatal_fault */
  kTopDarjeelingAlertIdAonTimerAonFatalFault = 31, /**< aon_timer_aon_fatal_fault */
  kTopDarjeelingAlertIdSensorCtrlRecovAlert = 32, /**< sensor_ctrl_recov_alert */
  kTopDarjeelingAlertIdSensorCtrlFatalAlert = 33, /**< sensor_ctrl_fatal_alert */
  kTopDarjeelingAlertIdSramCtrlRetAonFatalError = 34, /**< sram_ctrl_ret_aon_fatal_error */
  kTopDarjeelingAlertIdFlashCtrlRecovErr = 35, /**< flash_ctrl_recov_err */
  kTopDarjeelingAlertIdFlashCtrlFatalStdErr = 36, /**< flash_ctrl_fatal_std_err */
  kTopDarjeelingAlertIdFlashCtrlFatalErr = 37, /**< flash_ctrl_fatal_err */
  kTopDarjeelingAlertIdFlashCtrlFatalPrimFlashAlert = 38, /**< flash_ctrl_fatal_prim_flash_alert */
  kTopDarjeelingAlertIdFlashCtrlRecovPrimFlashAlert = 39, /**< flash_ctrl_recov_prim_flash_alert */
  kTopDarjeelingAlertIdRvDmFatalFault = 40, /**< rv_dm_fatal_fault */
  kTopDarjeelingAlertIdRvPlicFatalFault = 41, /**< rv_plic_fatal_fault */
  kTopDarjeelingAlertIdAesRecovCtrlUpdateErr = 42, /**< aes_recov_ctrl_update_err */
  kTopDarjeelingAlertIdAesFatalFault = 43, /**< aes_fatal_fault */
  kTopDarjeelingAlertIdHmacFatalFault = 44, /**< hmac_fatal_fault */
  kTopDarjeelingAlertIdKmacRecovOperationErr = 45, /**< kmac_recov_operation_err */
  kTopDarjeelingAlertIdKmacFatalFaultErr = 46, /**< kmac_fatal_fault_err */
  kTopDarjeelingAlertIdOtbnFatal = 47, /**< otbn_fatal */
  kTopDarjeelingAlertIdOtbnRecov = 48, /**< otbn_recov */
  kTopDarjeelingAlertIdKeymgrRecovOperationErr = 49, /**< keymgr_recov_operation_err */
  kTopDarjeelingAlertIdKeymgrFatalFaultErr = 50, /**< keymgr_fatal_fault_err */
  kTopDarjeelingAlertIdCsrngRecovAlert = 51, /**< csrng_recov_alert */
  kTopDarjeelingAlertIdCsrngFatalAlert = 52, /**< csrng_fatal_alert */
  kTopDarjeelingAlertIdEntropySrcRecovAlert = 53, /**< entropy_src_recov_alert */
  kTopDarjeelingAlertIdEntropySrcFatalAlert = 54, /**< entropy_src_fatal_alert */
  kTopDarjeelingAlertIdEdn0RecovAlert = 55, /**< edn0_recov_alert */
  kTopDarjeelingAlertIdEdn0FatalAlert = 56, /**< edn0_fatal_alert */
  kTopDarjeelingAlertIdEdn1RecovAlert = 57, /**< edn1_recov_alert */
  kTopDarjeelingAlertIdEdn1FatalAlert = 58, /**< edn1_fatal_alert */
  kTopDarjeelingAlertIdSramCtrlMainFatalError = 59, /**< sram_ctrl_main_fatal_error */
  kTopDarjeelingAlertIdSramCtrlMboxFatalError = 60, /**< sram_ctrl_mbox_fatal_error */
  kTopDarjeelingAlertIdRomCtrl0Fatal = 61, /**< rom_ctrl0_fatal */
  kTopDarjeelingAlertIdRomCtrl1Fatal = 62, /**< rom_ctrl1_fatal */
  kTopDarjeelingAlertIdRvCoreIbexFatalSwErr = 63, /**< rv_core_ibex_fatal_sw_err */
  kTopDarjeelingAlertIdRvCoreIbexRecovSwErr = 64, /**< rv_core_ibex_recov_sw_err */
  kTopDarjeelingAlertIdRvCoreIbexFatalHwErr = 65, /**< rv_core_ibex_fatal_hw_err */
  kTopDarjeelingAlertIdRvCoreIbexRecovHwErr = 66, /**< rv_core_ibex_recov_hw_err */
  kTopDarjeelingAlertIdLast = 66, /**< \internal The Last Valid Alert ID. */
} top_darjeeling_alert_id_t;

/**
 * Alert Handler Alert Source to Peripheral Map
 *
 * This array is a mapping from `top_darjeeling_alert_id_t` to
 * `top_darjeeling_alert_peripheral_t`.
 */
extern const top_darjeeling_alert_peripheral_t
    top_darjeeling_alert_for_peripheral[67];

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
  kTopDarjeelingPinmuxPeripheralInUart1Rx = 43, /**< Peripheral Input 43 */
  kTopDarjeelingPinmuxPeripheralInUart2Rx = 44, /**< Peripheral Input 44 */
  kTopDarjeelingPinmuxPeripheralInUart3Rx = 45, /**< Peripheral Input 45 */
  kTopDarjeelingPinmuxPeripheralInSpiDeviceTpmCsb = 46, /**< Peripheral Input 46 */
  kTopDarjeelingPinmuxPeripheralInFlashCtrlTck = 47, /**< Peripheral Input 47 */
  kTopDarjeelingPinmuxPeripheralInFlashCtrlTms = 48, /**< Peripheral Input 48 */
  kTopDarjeelingPinmuxPeripheralInFlashCtrlTdi = 49, /**< Peripheral Input 49 */
  kTopDarjeelingPinmuxPeripheralInSysrstCtrlAonAcPresent = 50, /**< Peripheral Input 50 */
  kTopDarjeelingPinmuxPeripheralInSysrstCtrlAonKey0In = 51, /**< Peripheral Input 51 */
  kTopDarjeelingPinmuxPeripheralInSysrstCtrlAonKey1In = 52, /**< Peripheral Input 52 */
  kTopDarjeelingPinmuxPeripheralInSysrstCtrlAonKey2In = 53, /**< Peripheral Input 53 */
  kTopDarjeelingPinmuxPeripheralInSysrstCtrlAonPwrbIn = 54, /**< Peripheral Input 54 */
  kTopDarjeelingPinmuxPeripheralInSysrstCtrlAonLidOpen = 55, /**< Peripheral Input 55 */
  kTopDarjeelingPinmuxPeripheralInUsbdevSense = 56, /**< Peripheral Input 56 */
  kTopDarjeelingPinmuxPeripheralInLast = 56, /**< \internal Last valid peripheral input */
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
  kTopDarjeelingPinmuxOutselUart1Tx = 46, /**< Peripheral Output 43 */
  kTopDarjeelingPinmuxOutselUart2Tx = 47, /**< Peripheral Output 44 */
  kTopDarjeelingPinmuxOutselUart3Tx = 48, /**< Peripheral Output 45 */
  kTopDarjeelingPinmuxOutselPattgenPda0Tx = 49, /**< Peripheral Output 46 */
  kTopDarjeelingPinmuxOutselPattgenPcl0Tx = 50, /**< Peripheral Output 47 */
  kTopDarjeelingPinmuxOutselPattgenPda1Tx = 51, /**< Peripheral Output 48 */
  kTopDarjeelingPinmuxOutselPattgenPcl1Tx = 52, /**< Peripheral Output 49 */
  kTopDarjeelingPinmuxOutselSpiHost1Sck = 53, /**< Peripheral Output 50 */
  kTopDarjeelingPinmuxOutselSpiHost1Csb = 54, /**< Peripheral Output 51 */
  kTopDarjeelingPinmuxOutselFlashCtrlTdo = 55, /**< Peripheral Output 52 */
  kTopDarjeelingPinmuxOutselSensorCtrlAstDebugOut0 = 56, /**< Peripheral Output 53 */
  kTopDarjeelingPinmuxOutselSensorCtrlAstDebugOut1 = 57, /**< Peripheral Output 54 */
  kTopDarjeelingPinmuxOutselSensorCtrlAstDebugOut2 = 58, /**< Peripheral Output 55 */
  kTopDarjeelingPinmuxOutselSensorCtrlAstDebugOut3 = 59, /**< Peripheral Output 56 */
  kTopDarjeelingPinmuxOutselSensorCtrlAstDebugOut4 = 60, /**< Peripheral Output 57 */
  kTopDarjeelingPinmuxOutselSensorCtrlAstDebugOut5 = 61, /**< Peripheral Output 58 */
  kTopDarjeelingPinmuxOutselSensorCtrlAstDebugOut6 = 62, /**< Peripheral Output 59 */
  kTopDarjeelingPinmuxOutselSensorCtrlAstDebugOut7 = 63, /**< Peripheral Output 60 */
  kTopDarjeelingPinmuxOutselSensorCtrlAstDebugOut8 = 64, /**< Peripheral Output 61 */
  kTopDarjeelingPinmuxOutselPwmAonPwm0 = 65, /**< Peripheral Output 62 */
  kTopDarjeelingPinmuxOutselPwmAonPwm1 = 66, /**< Peripheral Output 63 */
  kTopDarjeelingPinmuxOutselPwmAonPwm2 = 67, /**< Peripheral Output 64 */
  kTopDarjeelingPinmuxOutselPwmAonPwm3 = 68, /**< Peripheral Output 65 */
  kTopDarjeelingPinmuxOutselPwmAonPwm4 = 69, /**< Peripheral Output 66 */
  kTopDarjeelingPinmuxOutselPwmAonPwm5 = 70, /**< Peripheral Output 67 */
  kTopDarjeelingPinmuxOutselOtpCtrlTest0 = 71, /**< Peripheral Output 68 */
  kTopDarjeelingPinmuxOutselSysrstCtrlAonBatDisable = 72, /**< Peripheral Output 69 */
  kTopDarjeelingPinmuxOutselSysrstCtrlAonKey0Out = 73, /**< Peripheral Output 70 */
  kTopDarjeelingPinmuxOutselSysrstCtrlAonKey1Out = 74, /**< Peripheral Output 71 */
  kTopDarjeelingPinmuxOutselSysrstCtrlAonKey2Out = 75, /**< Peripheral Output 72 */
  kTopDarjeelingPinmuxOutselSysrstCtrlAonPwrbOut = 76, /**< Peripheral Output 73 */
  kTopDarjeelingPinmuxOutselSysrstCtrlAonZ3Wakeup = 77, /**< Peripheral Output 74 */
  kTopDarjeelingPinmuxOutselLast = 77, /**< \internal Last valid outsel value */
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
  kTopDarjeelingPowerManagerWakeUpsLast = 5, /**< \internal Last valid pwrmgr wakeup signal */
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
#define TOP_DARJEELING_MMIO_BASE_ADDR 0x40000000u
#define TOP_DARJEELING_MMIO_SIZE_BYTES 0x10000000u

// Header Extern Guard
#ifdef __cplusplus
}  // extern "C"
#endif

#endif  // OPENTITAN_HW_TOP_DARJEELING_SW_AUTOGEN_TOP_DARJEELING_H_
