// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
// util/topgen.py -t hw/top_verbano/data/top_verbano.hjson \
//                -o hw/top_verbano/

#ifndef OPENTITAN_HW_TOP_VERBANO_SW_AUTOGEN_TOP_VERBANO_H_
#define OPENTITAN_HW_TOP_VERBANO_SW_AUTOGEN_TOP_VERBANO_H_

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
 * Peripheral base address for uart0 in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_UART0_BASE_ADDR 0x40000000u

/**
 * Peripheral size for uart0 in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_UART0_BASE_ADDR and
 * `TOP_VERBANO_UART0_BASE_ADDR + TOP_VERBANO_UART0_SIZE_BYTES`.
 */
#define TOP_VERBANO_UART0_SIZE_BYTES 0x40u

/**
 * Peripheral base address for uart1 in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_UART1_BASE_ADDR 0x40010000u

/**
 * Peripheral size for uart1 in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_UART1_BASE_ADDR and
 * `TOP_VERBANO_UART1_BASE_ADDR + TOP_VERBANO_UART1_SIZE_BYTES`.
 */
#define TOP_VERBANO_UART1_SIZE_BYTES 0x40u

/**
 * Peripheral base address for uart2 in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_UART2_BASE_ADDR 0x40020000u

/**
 * Peripheral size for uart2 in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_UART2_BASE_ADDR and
 * `TOP_VERBANO_UART2_BASE_ADDR + TOP_VERBANO_UART2_SIZE_BYTES`.
 */
#define TOP_VERBANO_UART2_SIZE_BYTES 0x40u

/**
 * Peripheral base address for uart3 in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_UART3_BASE_ADDR 0x40030000u

/**
 * Peripheral size for uart3 in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_UART3_BASE_ADDR and
 * `TOP_VERBANO_UART3_BASE_ADDR + TOP_VERBANO_UART3_SIZE_BYTES`.
 */
#define TOP_VERBANO_UART3_SIZE_BYTES 0x40u

/**
 * Peripheral base address for gpio in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_GPIO_BASE_ADDR 0x40040000u

/**
 * Peripheral size for gpio in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_GPIO_BASE_ADDR and
 * `TOP_VERBANO_GPIO_BASE_ADDR + TOP_VERBANO_GPIO_SIZE_BYTES`.
 */
#define TOP_VERBANO_GPIO_SIZE_BYTES 0x80u

/**
 * Peripheral base address for spi_device in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_SPI_DEVICE_BASE_ADDR 0x40050000u

/**
 * Peripheral size for spi_device in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_SPI_DEVICE_BASE_ADDR and
 * `TOP_VERBANO_SPI_DEVICE_BASE_ADDR + TOP_VERBANO_SPI_DEVICE_SIZE_BYTES`.
 */
#define TOP_VERBANO_SPI_DEVICE_SIZE_BYTES 0x2000u

/**
 * Peripheral base address for i2c0 in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_I2C0_BASE_ADDR 0x40080000u

/**
 * Peripheral size for i2c0 in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_I2C0_BASE_ADDR and
 * `TOP_VERBANO_I2C0_BASE_ADDR + TOP_VERBANO_I2C0_SIZE_BYTES`.
 */
#define TOP_VERBANO_I2C0_SIZE_BYTES 0x80u

/**
 * Peripheral base address for i2c1 in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_I2C1_BASE_ADDR 0x40090000u

/**
 * Peripheral size for i2c1 in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_I2C1_BASE_ADDR and
 * `TOP_VERBANO_I2C1_BASE_ADDR + TOP_VERBANO_I2C1_SIZE_BYTES`.
 */
#define TOP_VERBANO_I2C1_SIZE_BYTES 0x80u

/**
 * Peripheral base address for i2c2 in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_I2C2_BASE_ADDR 0x400A0000u

/**
 * Peripheral size for i2c2 in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_I2C2_BASE_ADDR and
 * `TOP_VERBANO_I2C2_BASE_ADDR + TOP_VERBANO_I2C2_SIZE_BYTES`.
 */
#define TOP_VERBANO_I2C2_SIZE_BYTES 0x80u

/**
 * Peripheral base address for pattgen in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_PATTGEN_BASE_ADDR 0x400E0000u

/**
 * Peripheral size for pattgen in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_PATTGEN_BASE_ADDR and
 * `TOP_VERBANO_PATTGEN_BASE_ADDR + TOP_VERBANO_PATTGEN_SIZE_BYTES`.
 */
#define TOP_VERBANO_PATTGEN_SIZE_BYTES 0x40u

/**
 * Peripheral base address for rv_timer in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_RV_TIMER_BASE_ADDR 0x40100000u

/**
 * Peripheral size for rv_timer in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_RV_TIMER_BASE_ADDR and
 * `TOP_VERBANO_RV_TIMER_BASE_ADDR + TOP_VERBANO_RV_TIMER_SIZE_BYTES`.
 */
#define TOP_VERBANO_RV_TIMER_SIZE_BYTES 0x200u

/**
 * Peripheral base address for core device on otp_ctrl in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_OTP_CTRL_CORE_BASE_ADDR 0x40130000u

/**
 * Peripheral size for core device on otp_ctrl in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_OTP_CTRL_CORE_BASE_ADDR and
 * `TOP_VERBANO_OTP_CTRL_CORE_BASE_ADDR + TOP_VERBANO_OTP_CTRL_CORE_SIZE_BYTES`.
 */
#define TOP_VERBANO_OTP_CTRL_CORE_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for prim device on otp_macro in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_OTP_MACRO_PRIM_BASE_ADDR 0x40138000u

/**
 * Peripheral size for prim device on otp_macro in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_OTP_MACRO_PRIM_BASE_ADDR and
 * `TOP_VERBANO_OTP_MACRO_PRIM_BASE_ADDR + TOP_VERBANO_OTP_MACRO_PRIM_SIZE_BYTES`.
 */
#define TOP_VERBANO_OTP_MACRO_PRIM_SIZE_BYTES 0x20u

/**
 * Peripheral base address for regs device on lc_ctrl in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_LC_CTRL_REGS_BASE_ADDR 0x40140000u

/**
 * Peripheral size for regs device on lc_ctrl in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_LC_CTRL_REGS_BASE_ADDR and
 * `TOP_VERBANO_LC_CTRL_REGS_BASE_ADDR + TOP_VERBANO_LC_CTRL_REGS_SIZE_BYTES`.
 */
#define TOP_VERBANO_LC_CTRL_REGS_SIZE_BYTES 0x100u

/**
 * Peripheral base address for dmi device on lc_ctrl in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_LC_CTRL_DMI_BASE_ADDR 0x0u

/**
 * Peripheral size for dmi device on lc_ctrl in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_LC_CTRL_DMI_BASE_ADDR and
 * `TOP_VERBANO_LC_CTRL_DMI_BASE_ADDR + TOP_VERBANO_LC_CTRL_DMI_SIZE_BYTES`.
 */
#define TOP_VERBANO_LC_CTRL_DMI_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for alert_handler in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_ALERT_HANDLER_BASE_ADDR 0x40150000u

/**
 * Peripheral size for alert_handler in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_ALERT_HANDLER_BASE_ADDR and
 * `TOP_VERBANO_ALERT_HANDLER_BASE_ADDR + TOP_VERBANO_ALERT_HANDLER_SIZE_BYTES`.
 */
#define TOP_VERBANO_ALERT_HANDLER_SIZE_BYTES 0x800u

/**
 * Peripheral base address for spi_host0 in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_SPI_HOST0_BASE_ADDR 0x40300000u

/**
 * Peripheral size for spi_host0 in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_SPI_HOST0_BASE_ADDR and
 * `TOP_VERBANO_SPI_HOST0_BASE_ADDR + TOP_VERBANO_SPI_HOST0_SIZE_BYTES`.
 */
#define TOP_VERBANO_SPI_HOST0_SIZE_BYTES 0x40u

/**
 * Peripheral base address for spi_host1 in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_SPI_HOST1_BASE_ADDR 0x40310000u

/**
 * Peripheral size for spi_host1 in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_SPI_HOST1_BASE_ADDR and
 * `TOP_VERBANO_SPI_HOST1_BASE_ADDR + TOP_VERBANO_SPI_HOST1_SIZE_BYTES`.
 */
#define TOP_VERBANO_SPI_HOST1_SIZE_BYTES 0x40u

/**
 * Peripheral base address for usbdev in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_USBDEV_BASE_ADDR 0x40320000u

/**
 * Peripheral size for usbdev in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_USBDEV_BASE_ADDR and
 * `TOP_VERBANO_USBDEV_BASE_ADDR + TOP_VERBANO_USBDEV_SIZE_BYTES`.
 */
#define TOP_VERBANO_USBDEV_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for pwrmgr_aon in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_PWRMGR_AON_BASE_ADDR 0x40400000u

/**
 * Peripheral size for pwrmgr_aon in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_PWRMGR_AON_BASE_ADDR and
 * `TOP_VERBANO_PWRMGR_AON_BASE_ADDR + TOP_VERBANO_PWRMGR_AON_SIZE_BYTES`.
 */
#define TOP_VERBANO_PWRMGR_AON_SIZE_BYTES 0x80u

/**
 * Peripheral base address for rstmgr_aon in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_RSTMGR_AON_BASE_ADDR 0x40410000u

/**
 * Peripheral size for rstmgr_aon in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_RSTMGR_AON_BASE_ADDR and
 * `TOP_VERBANO_RSTMGR_AON_BASE_ADDR + TOP_VERBANO_RSTMGR_AON_SIZE_BYTES`.
 */
#define TOP_VERBANO_RSTMGR_AON_SIZE_BYTES 0x80u

/**
 * Peripheral base address for clkmgr_aon in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_CLKMGR_AON_BASE_ADDR 0x40420000u

/**
 * Peripheral size for clkmgr_aon in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_CLKMGR_AON_BASE_ADDR and
 * `TOP_VERBANO_CLKMGR_AON_BASE_ADDR + TOP_VERBANO_CLKMGR_AON_SIZE_BYTES`.
 */
#define TOP_VERBANO_CLKMGR_AON_SIZE_BYTES 0x80u

/**
 * Peripheral base address for sysrst_ctrl_aon in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_SYSRST_CTRL_AON_BASE_ADDR 0x40430000u

/**
 * Peripheral size for sysrst_ctrl_aon in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_SYSRST_CTRL_AON_BASE_ADDR and
 * `TOP_VERBANO_SYSRST_CTRL_AON_BASE_ADDR + TOP_VERBANO_SYSRST_CTRL_AON_SIZE_BYTES`.
 */
#define TOP_VERBANO_SYSRST_CTRL_AON_SIZE_BYTES 0x100u

/**
 * Peripheral base address for adc_ctrl_aon in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_ADC_CTRL_AON_BASE_ADDR 0x40440000u

/**
 * Peripheral size for adc_ctrl_aon in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_ADC_CTRL_AON_BASE_ADDR and
 * `TOP_VERBANO_ADC_CTRL_AON_BASE_ADDR + TOP_VERBANO_ADC_CTRL_AON_SIZE_BYTES`.
 */
#define TOP_VERBANO_ADC_CTRL_AON_SIZE_BYTES 0x80u

/**
 * Peripheral base address for pwm_aon in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_PWM_AON_BASE_ADDR 0x40450000u

/**
 * Peripheral size for pwm_aon in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_PWM_AON_BASE_ADDR and
 * `TOP_VERBANO_PWM_AON_BASE_ADDR + TOP_VERBANO_PWM_AON_SIZE_BYTES`.
 */
#define TOP_VERBANO_PWM_AON_SIZE_BYTES 0x80u

/**
 * Peripheral base address for pinmux_aon in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_PINMUX_AON_BASE_ADDR 0x40460000u

/**
 * Peripheral size for pinmux_aon in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_PINMUX_AON_BASE_ADDR and
 * `TOP_VERBANO_PINMUX_AON_BASE_ADDR + TOP_VERBANO_PINMUX_AON_SIZE_BYTES`.
 */
#define TOP_VERBANO_PINMUX_AON_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for aon_timer_aon in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_AON_TIMER_AON_BASE_ADDR 0x40470000u

/**
 * Peripheral size for aon_timer_aon in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_AON_TIMER_AON_BASE_ADDR and
 * `TOP_VERBANO_AON_TIMER_AON_BASE_ADDR + TOP_VERBANO_AON_TIMER_AON_SIZE_BYTES`.
 */
#define TOP_VERBANO_AON_TIMER_AON_SIZE_BYTES 0x40u

/**
 * Peripheral base address for ast in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_AST_BASE_ADDR 0x40480000u

/**
 * Peripheral size for ast in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_AST_BASE_ADDR and
 * `TOP_VERBANO_AST_BASE_ADDR + TOP_VERBANO_AST_SIZE_BYTES`.
 */
#define TOP_VERBANO_AST_SIZE_BYTES 0x400u

/**
 * Peripheral base address for sensor_ctrl_aon in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_SENSOR_CTRL_AON_BASE_ADDR 0x40490000u

/**
 * Peripheral size for sensor_ctrl_aon in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_SENSOR_CTRL_AON_BASE_ADDR and
 * `TOP_VERBANO_SENSOR_CTRL_AON_BASE_ADDR + TOP_VERBANO_SENSOR_CTRL_AON_SIZE_BYTES`.
 */
#define TOP_VERBANO_SENSOR_CTRL_AON_SIZE_BYTES 0x80u

/**
 * Peripheral base address for regs device on sram_ctrl_ret_aon in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_SRAM_CTRL_RET_AON_REGS_BASE_ADDR 0x40500000u

/**
 * Peripheral size for regs device on sram_ctrl_ret_aon in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_SRAM_CTRL_RET_AON_REGS_BASE_ADDR and
 * `TOP_VERBANO_SRAM_CTRL_RET_AON_REGS_BASE_ADDR + TOP_VERBANO_SRAM_CTRL_RET_AON_REGS_SIZE_BYTES`.
 */
#define TOP_VERBANO_SRAM_CTRL_RET_AON_REGS_SIZE_BYTES 0x40u

/**
 * Peripheral base address for ram device on sram_ctrl_ret_aon in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_SRAM_CTRL_RET_AON_RAM_BASE_ADDR 0x40600000u

/**
 * Peripheral size for ram device on sram_ctrl_ret_aon in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_SRAM_CTRL_RET_AON_RAM_BASE_ADDR and
 * `TOP_VERBANO_SRAM_CTRL_RET_AON_RAM_BASE_ADDR + TOP_VERBANO_SRAM_CTRL_RET_AON_RAM_SIZE_BYTES`.
 */
#define TOP_VERBANO_SRAM_CTRL_RET_AON_RAM_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for core device on flash_ctrl in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_FLASH_CTRL_CORE_BASE_ADDR 0x41000000u

/**
 * Peripheral size for core device on flash_ctrl in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_FLASH_CTRL_CORE_BASE_ADDR and
 * `TOP_VERBANO_FLASH_CTRL_CORE_BASE_ADDR + TOP_VERBANO_FLASH_CTRL_CORE_SIZE_BYTES`.
 */
#define TOP_VERBANO_FLASH_CTRL_CORE_SIZE_BYTES 0x200u

/**
 * Peripheral base address for prim device on flash_ctrl in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_FLASH_CTRL_PRIM_BASE_ADDR 0x41008000u

/**
 * Peripheral size for prim device on flash_ctrl in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_FLASH_CTRL_PRIM_BASE_ADDR and
 * `TOP_VERBANO_FLASH_CTRL_PRIM_BASE_ADDR + TOP_VERBANO_FLASH_CTRL_PRIM_SIZE_BYTES`.
 */
#define TOP_VERBANO_FLASH_CTRL_PRIM_SIZE_BYTES 0x80u

/**
 * Peripheral base address for mem device on flash_ctrl in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_FLASH_CTRL_MEM_BASE_ADDR 0x20000000u

/**
 * Peripheral size for mem device on flash_ctrl in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_FLASH_CTRL_MEM_BASE_ADDR and
 * `TOP_VERBANO_FLASH_CTRL_MEM_BASE_ADDR + TOP_VERBANO_FLASH_CTRL_MEM_SIZE_BYTES`.
 */
#define TOP_VERBANO_FLASH_CTRL_MEM_SIZE_BYTES 0x100000u

/**
 * Peripheral base address for regs device on rv_dm in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_RV_DM_REGS_BASE_ADDR 0x41200000u

/**
 * Peripheral size for regs device on rv_dm in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_RV_DM_REGS_BASE_ADDR and
 * `TOP_VERBANO_RV_DM_REGS_BASE_ADDR + TOP_VERBANO_RV_DM_REGS_SIZE_BYTES`.
 */
#define TOP_VERBANO_RV_DM_REGS_SIZE_BYTES 0x10u

/**
 * Peripheral base address for mem device on rv_dm in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_RV_DM_MEM_BASE_ADDR 0x10000u

/**
 * Peripheral size for mem device on rv_dm in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_RV_DM_MEM_BASE_ADDR and
 * `TOP_VERBANO_RV_DM_MEM_BASE_ADDR + TOP_VERBANO_RV_DM_MEM_SIZE_BYTES`.
 */
#define TOP_VERBANO_RV_DM_MEM_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for dbg device on rv_dm in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_RV_DM_DBG_BASE_ADDR 0x1000u

/**
 * Peripheral size for dbg device on rv_dm in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_RV_DM_DBG_BASE_ADDR and
 * `TOP_VERBANO_RV_DM_DBG_BASE_ADDR + TOP_VERBANO_RV_DM_DBG_SIZE_BYTES`.
 */
#define TOP_VERBANO_RV_DM_DBG_SIZE_BYTES 0x200u

/**
 * Peripheral base address for rv_plic in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_RV_PLIC_BASE_ADDR 0x48000000u

/**
 * Peripheral size for rv_plic in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_RV_PLIC_BASE_ADDR and
 * `TOP_VERBANO_RV_PLIC_BASE_ADDR + TOP_VERBANO_RV_PLIC_SIZE_BYTES`.
 */
#define TOP_VERBANO_RV_PLIC_SIZE_BYTES 0x8000000u

/**
 * Peripheral base address for aes in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_AES_BASE_ADDR 0x41100000u

/**
 * Peripheral size for aes in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_AES_BASE_ADDR and
 * `TOP_VERBANO_AES_BASE_ADDR + TOP_VERBANO_AES_SIZE_BYTES`.
 */
#define TOP_VERBANO_AES_SIZE_BYTES 0x100u

/**
 * Peripheral base address for hmac in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_HMAC_BASE_ADDR 0x41110000u

/**
 * Peripheral size for hmac in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_HMAC_BASE_ADDR and
 * `TOP_VERBANO_HMAC_BASE_ADDR + TOP_VERBANO_HMAC_SIZE_BYTES`.
 */
#define TOP_VERBANO_HMAC_SIZE_BYTES 0x2000u

/**
 * Peripheral base address for kmac in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_KMAC_BASE_ADDR 0x41120000u

/**
 * Peripheral size for kmac in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_KMAC_BASE_ADDR and
 * `TOP_VERBANO_KMAC_BASE_ADDR + TOP_VERBANO_KMAC_SIZE_BYTES`.
 */
#define TOP_VERBANO_KMAC_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for otbn in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_OTBN_BASE_ADDR 0x41130000u

/**
 * Peripheral size for otbn in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_OTBN_BASE_ADDR and
 * `TOP_VERBANO_OTBN_BASE_ADDR + TOP_VERBANO_OTBN_SIZE_BYTES`.
 */
#define TOP_VERBANO_OTBN_SIZE_BYTES 0x10000u

/**
 * Peripheral base address for keymgr in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_KEYMGR_BASE_ADDR 0x41140000u

/**
 * Peripheral size for keymgr in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_KEYMGR_BASE_ADDR and
 * `TOP_VERBANO_KEYMGR_BASE_ADDR + TOP_VERBANO_KEYMGR_SIZE_BYTES`.
 */
#define TOP_VERBANO_KEYMGR_SIZE_BYTES 0x100u

/**
 * Peripheral base address for csrng in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_CSRNG_BASE_ADDR 0x41150000u

/**
 * Peripheral size for csrng in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_CSRNG_BASE_ADDR and
 * `TOP_VERBANO_CSRNG_BASE_ADDR + TOP_VERBANO_CSRNG_SIZE_BYTES`.
 */
#define TOP_VERBANO_CSRNG_SIZE_BYTES 0x80u

/**
 * Peripheral base address for entropy_src in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_ENTROPY_SRC_BASE_ADDR 0x41160000u

/**
 * Peripheral size for entropy_src in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_ENTROPY_SRC_BASE_ADDR and
 * `TOP_VERBANO_ENTROPY_SRC_BASE_ADDR + TOP_VERBANO_ENTROPY_SRC_SIZE_BYTES`.
 */
#define TOP_VERBANO_ENTROPY_SRC_SIZE_BYTES 0x100u

/**
 * Peripheral base address for edn0 in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_EDN0_BASE_ADDR 0x41170000u

/**
 * Peripheral size for edn0 in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_EDN0_BASE_ADDR and
 * `TOP_VERBANO_EDN0_BASE_ADDR + TOP_VERBANO_EDN0_SIZE_BYTES`.
 */
#define TOP_VERBANO_EDN0_SIZE_BYTES 0x80u

/**
 * Peripheral base address for edn1 in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_EDN1_BASE_ADDR 0x41180000u

/**
 * Peripheral size for edn1 in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_EDN1_BASE_ADDR and
 * `TOP_VERBANO_EDN1_BASE_ADDR + TOP_VERBANO_EDN1_SIZE_BYTES`.
 */
#define TOP_VERBANO_EDN1_SIZE_BYTES 0x80u

/**
 * Peripheral base address for regs device on sram_ctrl_main in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_SRAM_CTRL_MAIN_REGS_BASE_ADDR 0x411C0000u

/**
 * Peripheral size for regs device on sram_ctrl_main in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_SRAM_CTRL_MAIN_REGS_BASE_ADDR and
 * `TOP_VERBANO_SRAM_CTRL_MAIN_REGS_BASE_ADDR + TOP_VERBANO_SRAM_CTRL_MAIN_REGS_SIZE_BYTES`.
 */
#define TOP_VERBANO_SRAM_CTRL_MAIN_REGS_SIZE_BYTES 0x40u

/**
 * Peripheral base address for ram device on sram_ctrl_main in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_SRAM_CTRL_MAIN_RAM_BASE_ADDR 0x10000000u

/**
 * Peripheral size for ram device on sram_ctrl_main in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_SRAM_CTRL_MAIN_RAM_BASE_ADDR and
 * `TOP_VERBANO_SRAM_CTRL_MAIN_RAM_BASE_ADDR + TOP_VERBANO_SRAM_CTRL_MAIN_RAM_SIZE_BYTES`.
 */
#define TOP_VERBANO_SRAM_CTRL_MAIN_RAM_SIZE_BYTES 0x20000u

/**
 * Peripheral base address for regs device on rom_ctrl in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_ROM_CTRL_REGS_BASE_ADDR 0x411E0000u

/**
 * Peripheral size for regs device on rom_ctrl in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_ROM_CTRL_REGS_BASE_ADDR and
 * `TOP_VERBANO_ROM_CTRL_REGS_BASE_ADDR + TOP_VERBANO_ROM_CTRL_REGS_SIZE_BYTES`.
 */
#define TOP_VERBANO_ROM_CTRL_REGS_SIZE_BYTES 0x80u

/**
 * Peripheral base address for rom device on rom_ctrl in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_ROM_CTRL_ROM_BASE_ADDR 0x8000u

/**
 * Peripheral size for rom device on rom_ctrl in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_ROM_CTRL_ROM_BASE_ADDR and
 * `TOP_VERBANO_ROM_CTRL_ROM_BASE_ADDR + TOP_VERBANO_ROM_CTRL_ROM_SIZE_BYTES`.
 */
#define TOP_VERBANO_ROM_CTRL_ROM_SIZE_BYTES 0x8000u

/**
 * Peripheral base address for cfg device on rv_core_ibex in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_RV_CORE_IBEX_CFG_BASE_ADDR 0x411F0000u

/**
 * Peripheral size for cfg device on rv_core_ibex in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_RV_CORE_IBEX_CFG_BASE_ADDR and
 * `TOP_VERBANO_RV_CORE_IBEX_CFG_BASE_ADDR + TOP_VERBANO_RV_CORE_IBEX_CFG_SIZE_BYTES`.
 */
#define TOP_VERBANO_RV_CORE_IBEX_CFG_SIZE_BYTES 0x100u


/**
 * Memory base address for ram_ret_aon in top verbano.
 */
#define TOP_VERBANO_RAM_RET_AON_BASE_ADDR 0x40600000u

/**
 * Memory size for ram_ret_aon in top verbano.
 */
#define TOP_VERBANO_RAM_RET_AON_SIZE_BYTES 0x1000u

/**
 * Memory base address for eflash in top verbano.
 */
#define TOP_VERBANO_EFLASH_BASE_ADDR 0x20000000u

/**
 * Memory size for eflash in top verbano.
 */
#define TOP_VERBANO_EFLASH_SIZE_BYTES 0x100000u

/**
 * Memory base address for ram_main in top verbano.
 */
#define TOP_VERBANO_RAM_MAIN_BASE_ADDR 0x10000000u

/**
 * Memory size for ram_main in top verbano.
 */
#define TOP_VERBANO_RAM_MAIN_SIZE_BYTES 0x20000u

/**
 * Memory base address for rom in top verbano.
 */
#define TOP_VERBANO_ROM_BASE_ADDR 0x8000u

/**
 * Memory size for rom in top verbano.
 */
#define TOP_VERBANO_ROM_SIZE_BYTES 0x8000u


/**
 * PLIC Interrupt Source Peripheral.
 *
 * Enumeration used to determine which peripheral asserted the corresponding
 * interrupt.
 */
typedef enum top_verbano_plic_peripheral {
  kTopVerbanoPlicPeripheralUnknown = 0, /**< Unknown Peripheral */
  kTopVerbanoPlicPeripheralUart0 = 1, /**< uart0 */
  kTopVerbanoPlicPeripheralUart1 = 2, /**< uart1 */
  kTopVerbanoPlicPeripheralUart2 = 3, /**< uart2 */
  kTopVerbanoPlicPeripheralUart3 = 4, /**< uart3 */
  kTopVerbanoPlicPeripheralGpio = 5, /**< gpio */
  kTopVerbanoPlicPeripheralSpiDevice = 6, /**< spi_device */
  kTopVerbanoPlicPeripheralI2c0 = 7, /**< i2c0 */
  kTopVerbanoPlicPeripheralI2c1 = 8, /**< i2c1 */
  kTopVerbanoPlicPeripheralI2c2 = 9, /**< i2c2 */
  kTopVerbanoPlicPeripheralPattgen = 10, /**< pattgen */
  kTopVerbanoPlicPeripheralRvTimer = 11, /**< rv_timer */
  kTopVerbanoPlicPeripheralOtpCtrl = 12, /**< otp_ctrl */
  kTopVerbanoPlicPeripheralAlertHandler = 13, /**< alert_handler */
  kTopVerbanoPlicPeripheralSpiHost0 = 14, /**< spi_host0 */
  kTopVerbanoPlicPeripheralSpiHost1 = 15, /**< spi_host1 */
  kTopVerbanoPlicPeripheralUsbdev = 16, /**< usbdev */
  kTopVerbanoPlicPeripheralPwrmgrAon = 17, /**< pwrmgr_aon */
  kTopVerbanoPlicPeripheralSysrstCtrlAon = 18, /**< sysrst_ctrl_aon */
  kTopVerbanoPlicPeripheralAdcCtrlAon = 19, /**< adc_ctrl_aon */
  kTopVerbanoPlicPeripheralAonTimerAon = 20, /**< aon_timer_aon */
  kTopVerbanoPlicPeripheralSensorCtrlAon = 21, /**< sensor_ctrl_aon */
  kTopVerbanoPlicPeripheralFlashCtrl = 22, /**< flash_ctrl */
  kTopVerbanoPlicPeripheralHmac = 23, /**< hmac */
  kTopVerbanoPlicPeripheralKmac = 24, /**< kmac */
  kTopVerbanoPlicPeripheralOtbn = 25, /**< otbn */
  kTopVerbanoPlicPeripheralKeymgr = 26, /**< keymgr */
  kTopVerbanoPlicPeripheralCsrng = 27, /**< csrng */
  kTopVerbanoPlicPeripheralEntropySrc = 28, /**< entropy_src */
  kTopVerbanoPlicPeripheralEdn0 = 29, /**< edn0 */
  kTopVerbanoPlicPeripheralEdn1 = 30, /**< edn1 */
  kTopVerbanoPlicPeripheralLast = 30, /**< \internal Final PLIC peripheral */
} top_verbano_plic_peripheral_t;

/**
 * PLIC Interrupt Source.
 *
 * Enumeration of all PLIC interrupt sources. The interrupt sources belonging to
 * the same peripheral are guaranteed to be consecutive.
 */
typedef enum top_verbano_plic_irq_id {
  kTopVerbanoPlicIrqIdNone = 0, /**< No Interrupt */
  kTopVerbanoPlicIrqIdUart0TxWatermark = 1, /**< uart0_tx_watermark */
  kTopVerbanoPlicIrqIdUart0RxWatermark = 2, /**< uart0_rx_watermark */
  kTopVerbanoPlicIrqIdUart0TxDone = 3, /**< uart0_tx_done */
  kTopVerbanoPlicIrqIdUart0RxOverflow = 4, /**< uart0_rx_overflow */
  kTopVerbanoPlicIrqIdUart0RxFrameErr = 5, /**< uart0_rx_frame_err */
  kTopVerbanoPlicIrqIdUart0RxBreakErr = 6, /**< uart0_rx_break_err */
  kTopVerbanoPlicIrqIdUart0RxTimeout = 7, /**< uart0_rx_timeout */
  kTopVerbanoPlicIrqIdUart0RxParityErr = 8, /**< uart0_rx_parity_err */
  kTopVerbanoPlicIrqIdUart0TxEmpty = 9, /**< uart0_tx_empty */
  kTopVerbanoPlicIrqIdUart1TxWatermark = 10, /**< uart1_tx_watermark */
  kTopVerbanoPlicIrqIdUart1RxWatermark = 11, /**< uart1_rx_watermark */
  kTopVerbanoPlicIrqIdUart1TxDone = 12, /**< uart1_tx_done */
  kTopVerbanoPlicIrqIdUart1RxOverflow = 13, /**< uart1_rx_overflow */
  kTopVerbanoPlicIrqIdUart1RxFrameErr = 14, /**< uart1_rx_frame_err */
  kTopVerbanoPlicIrqIdUart1RxBreakErr = 15, /**< uart1_rx_break_err */
  kTopVerbanoPlicIrqIdUart1RxTimeout = 16, /**< uart1_rx_timeout */
  kTopVerbanoPlicIrqIdUart1RxParityErr = 17, /**< uart1_rx_parity_err */
  kTopVerbanoPlicIrqIdUart1TxEmpty = 18, /**< uart1_tx_empty */
  kTopVerbanoPlicIrqIdUart2TxWatermark = 19, /**< uart2_tx_watermark */
  kTopVerbanoPlicIrqIdUart2RxWatermark = 20, /**< uart2_rx_watermark */
  kTopVerbanoPlicIrqIdUart2TxDone = 21, /**< uart2_tx_done */
  kTopVerbanoPlicIrqIdUart2RxOverflow = 22, /**< uart2_rx_overflow */
  kTopVerbanoPlicIrqIdUart2RxFrameErr = 23, /**< uart2_rx_frame_err */
  kTopVerbanoPlicIrqIdUart2RxBreakErr = 24, /**< uart2_rx_break_err */
  kTopVerbanoPlicIrqIdUart2RxTimeout = 25, /**< uart2_rx_timeout */
  kTopVerbanoPlicIrqIdUart2RxParityErr = 26, /**< uart2_rx_parity_err */
  kTopVerbanoPlicIrqIdUart2TxEmpty = 27, /**< uart2_tx_empty */
  kTopVerbanoPlicIrqIdUart3TxWatermark = 28, /**< uart3_tx_watermark */
  kTopVerbanoPlicIrqIdUart3RxWatermark = 29, /**< uart3_rx_watermark */
  kTopVerbanoPlicIrqIdUart3TxDone = 30, /**< uart3_tx_done */
  kTopVerbanoPlicIrqIdUart3RxOverflow = 31, /**< uart3_rx_overflow */
  kTopVerbanoPlicIrqIdUart3RxFrameErr = 32, /**< uart3_rx_frame_err */
  kTopVerbanoPlicIrqIdUart3RxBreakErr = 33, /**< uart3_rx_break_err */
  kTopVerbanoPlicIrqIdUart3RxTimeout = 34, /**< uart3_rx_timeout */
  kTopVerbanoPlicIrqIdUart3RxParityErr = 35, /**< uart3_rx_parity_err */
  kTopVerbanoPlicIrqIdUart3TxEmpty = 36, /**< uart3_tx_empty */
  kTopVerbanoPlicIrqIdGpioGpio0 = 37, /**< gpio_gpio 0 */
  kTopVerbanoPlicIrqIdGpioGpio1 = 38, /**< gpio_gpio 1 */
  kTopVerbanoPlicIrqIdGpioGpio2 = 39, /**< gpio_gpio 2 */
  kTopVerbanoPlicIrqIdGpioGpio3 = 40, /**< gpio_gpio 3 */
  kTopVerbanoPlicIrqIdGpioGpio4 = 41, /**< gpio_gpio 4 */
  kTopVerbanoPlicIrqIdGpioGpio5 = 42, /**< gpio_gpio 5 */
  kTopVerbanoPlicIrqIdGpioGpio6 = 43, /**< gpio_gpio 6 */
  kTopVerbanoPlicIrqIdGpioGpio7 = 44, /**< gpio_gpio 7 */
  kTopVerbanoPlicIrqIdGpioGpio8 = 45, /**< gpio_gpio 8 */
  kTopVerbanoPlicIrqIdGpioGpio9 = 46, /**< gpio_gpio 9 */
  kTopVerbanoPlicIrqIdGpioGpio10 = 47, /**< gpio_gpio 10 */
  kTopVerbanoPlicIrqIdGpioGpio11 = 48, /**< gpio_gpio 11 */
  kTopVerbanoPlicIrqIdGpioGpio12 = 49, /**< gpio_gpio 12 */
  kTopVerbanoPlicIrqIdGpioGpio13 = 50, /**< gpio_gpio 13 */
  kTopVerbanoPlicIrqIdGpioGpio14 = 51, /**< gpio_gpio 14 */
  kTopVerbanoPlicIrqIdGpioGpio15 = 52, /**< gpio_gpio 15 */
  kTopVerbanoPlicIrqIdGpioGpio16 = 53, /**< gpio_gpio 16 */
  kTopVerbanoPlicIrqIdGpioGpio17 = 54, /**< gpio_gpio 17 */
  kTopVerbanoPlicIrqIdGpioGpio18 = 55, /**< gpio_gpio 18 */
  kTopVerbanoPlicIrqIdGpioGpio19 = 56, /**< gpio_gpio 19 */
  kTopVerbanoPlicIrqIdGpioGpio20 = 57, /**< gpio_gpio 20 */
  kTopVerbanoPlicIrqIdGpioGpio21 = 58, /**< gpio_gpio 21 */
  kTopVerbanoPlicIrqIdGpioGpio22 = 59, /**< gpio_gpio 22 */
  kTopVerbanoPlicIrqIdGpioGpio23 = 60, /**< gpio_gpio 23 */
  kTopVerbanoPlicIrqIdGpioGpio24 = 61, /**< gpio_gpio 24 */
  kTopVerbanoPlicIrqIdGpioGpio25 = 62, /**< gpio_gpio 25 */
  kTopVerbanoPlicIrqIdGpioGpio26 = 63, /**< gpio_gpio 26 */
  kTopVerbanoPlicIrqIdGpioGpio27 = 64, /**< gpio_gpio 27 */
  kTopVerbanoPlicIrqIdGpioGpio28 = 65, /**< gpio_gpio 28 */
  kTopVerbanoPlicIrqIdGpioGpio29 = 66, /**< gpio_gpio 29 */
  kTopVerbanoPlicIrqIdGpioGpio30 = 67, /**< gpio_gpio 30 */
  kTopVerbanoPlicIrqIdGpioGpio31 = 68, /**< gpio_gpio 31 */
  kTopVerbanoPlicIrqIdSpiDeviceUploadCmdfifoNotEmpty = 69, /**< spi_device_upload_cmdfifo_not_empty */
  kTopVerbanoPlicIrqIdSpiDeviceUploadPayloadNotEmpty = 70, /**< spi_device_upload_payload_not_empty */
  kTopVerbanoPlicIrqIdSpiDeviceUploadPayloadOverflow = 71, /**< spi_device_upload_payload_overflow */
  kTopVerbanoPlicIrqIdSpiDeviceReadbufWatermark = 72, /**< spi_device_readbuf_watermark */
  kTopVerbanoPlicIrqIdSpiDeviceReadbufFlip = 73, /**< spi_device_readbuf_flip */
  kTopVerbanoPlicIrqIdSpiDeviceTpmHeaderNotEmpty = 74, /**< spi_device_tpm_header_not_empty */
  kTopVerbanoPlicIrqIdSpiDeviceTpmRdfifoCmdEnd = 75, /**< spi_device_tpm_rdfifo_cmd_end */
  kTopVerbanoPlicIrqIdSpiDeviceTpmRdfifoDrop = 76, /**< spi_device_tpm_rdfifo_drop */
  kTopVerbanoPlicIrqIdI2c0FmtThreshold = 77, /**< i2c0_fmt_threshold */
  kTopVerbanoPlicIrqIdI2c0RxThreshold = 78, /**< i2c0_rx_threshold */
  kTopVerbanoPlicIrqIdI2c0AcqThreshold = 79, /**< i2c0_acq_threshold */
  kTopVerbanoPlicIrqIdI2c0RxOverflow = 80, /**< i2c0_rx_overflow */
  kTopVerbanoPlicIrqIdI2c0ControllerHalt = 81, /**< i2c0_controller_halt */
  kTopVerbanoPlicIrqIdI2c0SclInterference = 82, /**< i2c0_scl_interference */
  kTopVerbanoPlicIrqIdI2c0SdaInterference = 83, /**< i2c0_sda_interference */
  kTopVerbanoPlicIrqIdI2c0StretchTimeout = 84, /**< i2c0_stretch_timeout */
  kTopVerbanoPlicIrqIdI2c0SdaUnstable = 85, /**< i2c0_sda_unstable */
  kTopVerbanoPlicIrqIdI2c0CmdComplete = 86, /**< i2c0_cmd_complete */
  kTopVerbanoPlicIrqIdI2c0TxStretch = 87, /**< i2c0_tx_stretch */
  kTopVerbanoPlicIrqIdI2c0TxThreshold = 88, /**< i2c0_tx_threshold */
  kTopVerbanoPlicIrqIdI2c0AcqStretch = 89, /**< i2c0_acq_stretch */
  kTopVerbanoPlicIrqIdI2c0UnexpStop = 90, /**< i2c0_unexp_stop */
  kTopVerbanoPlicIrqIdI2c0HostTimeout = 91, /**< i2c0_host_timeout */
  kTopVerbanoPlicIrqIdI2c1FmtThreshold = 92, /**< i2c1_fmt_threshold */
  kTopVerbanoPlicIrqIdI2c1RxThreshold = 93, /**< i2c1_rx_threshold */
  kTopVerbanoPlicIrqIdI2c1AcqThreshold = 94, /**< i2c1_acq_threshold */
  kTopVerbanoPlicIrqIdI2c1RxOverflow = 95, /**< i2c1_rx_overflow */
  kTopVerbanoPlicIrqIdI2c1ControllerHalt = 96, /**< i2c1_controller_halt */
  kTopVerbanoPlicIrqIdI2c1SclInterference = 97, /**< i2c1_scl_interference */
  kTopVerbanoPlicIrqIdI2c1SdaInterference = 98, /**< i2c1_sda_interference */
  kTopVerbanoPlicIrqIdI2c1StretchTimeout = 99, /**< i2c1_stretch_timeout */
  kTopVerbanoPlicIrqIdI2c1SdaUnstable = 100, /**< i2c1_sda_unstable */
  kTopVerbanoPlicIrqIdI2c1CmdComplete = 101, /**< i2c1_cmd_complete */
  kTopVerbanoPlicIrqIdI2c1TxStretch = 102, /**< i2c1_tx_stretch */
  kTopVerbanoPlicIrqIdI2c1TxThreshold = 103, /**< i2c1_tx_threshold */
  kTopVerbanoPlicIrqIdI2c1AcqStretch = 104, /**< i2c1_acq_stretch */
  kTopVerbanoPlicIrqIdI2c1UnexpStop = 105, /**< i2c1_unexp_stop */
  kTopVerbanoPlicIrqIdI2c1HostTimeout = 106, /**< i2c1_host_timeout */
  kTopVerbanoPlicIrqIdI2c2FmtThreshold = 107, /**< i2c2_fmt_threshold */
  kTopVerbanoPlicIrqIdI2c2RxThreshold = 108, /**< i2c2_rx_threshold */
  kTopVerbanoPlicIrqIdI2c2AcqThreshold = 109, /**< i2c2_acq_threshold */
  kTopVerbanoPlicIrqIdI2c2RxOverflow = 110, /**< i2c2_rx_overflow */
  kTopVerbanoPlicIrqIdI2c2ControllerHalt = 111, /**< i2c2_controller_halt */
  kTopVerbanoPlicIrqIdI2c2SclInterference = 112, /**< i2c2_scl_interference */
  kTopVerbanoPlicIrqIdI2c2SdaInterference = 113, /**< i2c2_sda_interference */
  kTopVerbanoPlicIrqIdI2c2StretchTimeout = 114, /**< i2c2_stretch_timeout */
  kTopVerbanoPlicIrqIdI2c2SdaUnstable = 115, /**< i2c2_sda_unstable */
  kTopVerbanoPlicIrqIdI2c2CmdComplete = 116, /**< i2c2_cmd_complete */
  kTopVerbanoPlicIrqIdI2c2TxStretch = 117, /**< i2c2_tx_stretch */
  kTopVerbanoPlicIrqIdI2c2TxThreshold = 118, /**< i2c2_tx_threshold */
  kTopVerbanoPlicIrqIdI2c2AcqStretch = 119, /**< i2c2_acq_stretch */
  kTopVerbanoPlicIrqIdI2c2UnexpStop = 120, /**< i2c2_unexp_stop */
  kTopVerbanoPlicIrqIdI2c2HostTimeout = 121, /**< i2c2_host_timeout */
  kTopVerbanoPlicIrqIdPattgenDoneCh0 = 122, /**< pattgen_done_ch0 */
  kTopVerbanoPlicIrqIdPattgenDoneCh1 = 123, /**< pattgen_done_ch1 */
  kTopVerbanoPlicIrqIdRvTimerTimerExpiredHart0Timer0 = 124, /**< rv_timer_timer_expired_hart0_timer0 */
  kTopVerbanoPlicIrqIdOtpCtrlOtpOperationDone = 125, /**< otp_ctrl_otp_operation_done */
  kTopVerbanoPlicIrqIdOtpCtrlOtpError = 126, /**< otp_ctrl_otp_error */
  kTopVerbanoPlicIrqIdAlertHandlerClassa = 127, /**< alert_handler_classa */
  kTopVerbanoPlicIrqIdAlertHandlerClassb = 128, /**< alert_handler_classb */
  kTopVerbanoPlicIrqIdAlertHandlerClassc = 129, /**< alert_handler_classc */
  kTopVerbanoPlicIrqIdAlertHandlerClassd = 130, /**< alert_handler_classd */
  kTopVerbanoPlicIrqIdSpiHost0Error = 131, /**< spi_host0_error */
  kTopVerbanoPlicIrqIdSpiHost0SpiEvent = 132, /**< spi_host0_spi_event */
  kTopVerbanoPlicIrqIdSpiHost1Error = 133, /**< spi_host1_error */
  kTopVerbanoPlicIrqIdSpiHost1SpiEvent = 134, /**< spi_host1_spi_event */
  kTopVerbanoPlicIrqIdUsbdevPktReceived = 135, /**< usbdev_pkt_received */
  kTopVerbanoPlicIrqIdUsbdevPktSent = 136, /**< usbdev_pkt_sent */
  kTopVerbanoPlicIrqIdUsbdevDisconnected = 137, /**< usbdev_disconnected */
  kTopVerbanoPlicIrqIdUsbdevHostLost = 138, /**< usbdev_host_lost */
  kTopVerbanoPlicIrqIdUsbdevLinkReset = 139, /**< usbdev_link_reset */
  kTopVerbanoPlicIrqIdUsbdevLinkSuspend = 140, /**< usbdev_link_suspend */
  kTopVerbanoPlicIrqIdUsbdevLinkResume = 141, /**< usbdev_link_resume */
  kTopVerbanoPlicIrqIdUsbdevAvOutEmpty = 142, /**< usbdev_av_out_empty */
  kTopVerbanoPlicIrqIdUsbdevRxFull = 143, /**< usbdev_rx_full */
  kTopVerbanoPlicIrqIdUsbdevAvOverflow = 144, /**< usbdev_av_overflow */
  kTopVerbanoPlicIrqIdUsbdevLinkInErr = 145, /**< usbdev_link_in_err */
  kTopVerbanoPlicIrqIdUsbdevRxCrcErr = 146, /**< usbdev_rx_crc_err */
  kTopVerbanoPlicIrqIdUsbdevRxPidErr = 147, /**< usbdev_rx_pid_err */
  kTopVerbanoPlicIrqIdUsbdevRxBitstuffErr = 148, /**< usbdev_rx_bitstuff_err */
  kTopVerbanoPlicIrqIdUsbdevFrame = 149, /**< usbdev_frame */
  kTopVerbanoPlicIrqIdUsbdevPowered = 150, /**< usbdev_powered */
  kTopVerbanoPlicIrqIdUsbdevLinkOutErr = 151, /**< usbdev_link_out_err */
  kTopVerbanoPlicIrqIdUsbdevAvSetupEmpty = 152, /**< usbdev_av_setup_empty */
  kTopVerbanoPlicIrqIdPwrmgrAonWakeup = 153, /**< pwrmgr_aon_wakeup */
  kTopVerbanoPlicIrqIdSysrstCtrlAonEventDetected = 154, /**< sysrst_ctrl_aon_event_detected */
  kTopVerbanoPlicIrqIdAdcCtrlAonMatchPending = 155, /**< adc_ctrl_aon_match_pending */
  kTopVerbanoPlicIrqIdAonTimerAonWkupTimerExpired = 156, /**< aon_timer_aon_wkup_timer_expired */
  kTopVerbanoPlicIrqIdAonTimerAonWdogTimerBark = 157, /**< aon_timer_aon_wdog_timer_bark */
  kTopVerbanoPlicIrqIdSensorCtrlAonIoStatusChange = 158, /**< sensor_ctrl_aon_io_status_change */
  kTopVerbanoPlicIrqIdSensorCtrlAonInitStatusChange = 159, /**< sensor_ctrl_aon_init_status_change */
  kTopVerbanoPlicIrqIdFlashCtrlProgEmpty = 160, /**< flash_ctrl_prog_empty */
  kTopVerbanoPlicIrqIdFlashCtrlProgLvl = 161, /**< flash_ctrl_prog_lvl */
  kTopVerbanoPlicIrqIdFlashCtrlRdFull = 162, /**< flash_ctrl_rd_full */
  kTopVerbanoPlicIrqIdFlashCtrlRdLvl = 163, /**< flash_ctrl_rd_lvl */
  kTopVerbanoPlicIrqIdFlashCtrlOpDone = 164, /**< flash_ctrl_op_done */
  kTopVerbanoPlicIrqIdFlashCtrlCorrErr = 165, /**< flash_ctrl_corr_err */
  kTopVerbanoPlicIrqIdHmacHmacDone = 166, /**< hmac_hmac_done */
  kTopVerbanoPlicIrqIdHmacFifoEmpty = 167, /**< hmac_fifo_empty */
  kTopVerbanoPlicIrqIdHmacHmacErr = 168, /**< hmac_hmac_err */
  kTopVerbanoPlicIrqIdKmacKmacDone = 169, /**< kmac_kmac_done */
  kTopVerbanoPlicIrqIdKmacFifoEmpty = 170, /**< kmac_fifo_empty */
  kTopVerbanoPlicIrqIdKmacKmacErr = 171, /**< kmac_kmac_err */
  kTopVerbanoPlicIrqIdOtbnDone = 172, /**< otbn_done */
  kTopVerbanoPlicIrqIdKeymgrOpDone = 173, /**< keymgr_op_done */
  kTopVerbanoPlicIrqIdCsrngCsCmdReqDone = 174, /**< csrng_cs_cmd_req_done */
  kTopVerbanoPlicIrqIdCsrngCsEntropyReq = 175, /**< csrng_cs_entropy_req */
  kTopVerbanoPlicIrqIdCsrngCsHwInstExc = 176, /**< csrng_cs_hw_inst_exc */
  kTopVerbanoPlicIrqIdCsrngCsFatalErr = 177, /**< csrng_cs_fatal_err */
  kTopVerbanoPlicIrqIdEntropySrcEsEntropyValid = 178, /**< entropy_src_es_entropy_valid */
  kTopVerbanoPlicIrqIdEntropySrcEsHealthTestFailed = 179, /**< entropy_src_es_health_test_failed */
  kTopVerbanoPlicIrqIdEntropySrcEsObserveFifoReady = 180, /**< entropy_src_es_observe_fifo_ready */
  kTopVerbanoPlicIrqIdEntropySrcEsFatalErr = 181, /**< entropy_src_es_fatal_err */
  kTopVerbanoPlicIrqIdEdn0EdnCmdReqDone = 182, /**< edn0_edn_cmd_req_done */
  kTopVerbanoPlicIrqIdEdn0EdnFatalErr = 183, /**< edn0_edn_fatal_err */
  kTopVerbanoPlicIrqIdEdn1EdnCmdReqDone = 184, /**< edn1_edn_cmd_req_done */
  kTopVerbanoPlicIrqIdEdn1EdnFatalErr = 185, /**< edn1_edn_fatal_err */
  kTopVerbanoPlicIrqIdLast = 185, /**< \internal The Last Valid Interrupt ID. */
} top_verbano_plic_irq_id_t;

/**
 * PLIC Interrupt Source to Peripheral Map
 *
 * This array is a mapping from `top_verbano_plic_irq_id_t` to
 * `top_verbano_plic_peripheral_t`.
 */
extern const top_verbano_plic_peripheral_t
    top_verbano_plic_interrupt_for_peripheral[186];

/**
 * PLIC Interrupt Target.
 *
 * Enumeration used to determine which set of IE, CC, threshold registers to
 * access for a given interrupt target.
 */
typedef enum top_verbano_plic_target {
  kTopVerbanoPlicTargetIbex0 = 0, /**< Ibex Core 0 */
  kTopVerbanoPlicTargetLast = 0, /**< \internal Final PLIC target */
} top_verbano_plic_target_t;


/**
 * Alert Handler Source Peripheral.
 *
 * Enumeration used to determine which peripheral asserted the corresponding
 * alert.
 */
typedef enum top_verbano_alert_peripheral {
  kTopVerbanoAlertPeripheralExternal = 0, /**< External Peripheral */
  kTopVerbanoAlertPeripheralUart0 = 1, /**< uart0 */
  kTopVerbanoAlertPeripheralUart1 = 2, /**< uart1 */
  kTopVerbanoAlertPeripheralUart2 = 3, /**< uart2 */
  kTopVerbanoAlertPeripheralUart3 = 4, /**< uart3 */
  kTopVerbanoAlertPeripheralGpio = 5, /**< gpio */
  kTopVerbanoAlertPeripheralSpiDevice = 6, /**< spi_device */
  kTopVerbanoAlertPeripheralI2c0 = 7, /**< i2c0 */
  kTopVerbanoAlertPeripheralI2c1 = 8, /**< i2c1 */
  kTopVerbanoAlertPeripheralI2c2 = 9, /**< i2c2 */
  kTopVerbanoAlertPeripheralPattgen = 10, /**< pattgen */
  kTopVerbanoAlertPeripheralRvTimer = 11, /**< rv_timer */
  kTopVerbanoAlertPeripheralOtpCtrl = 12, /**< otp_ctrl */
  kTopVerbanoAlertPeripheralLcCtrl = 13, /**< lc_ctrl */
  kTopVerbanoAlertPeripheralSpiHost0 = 14, /**< spi_host0 */
  kTopVerbanoAlertPeripheralSpiHost1 = 15, /**< spi_host1 */
  kTopVerbanoAlertPeripheralUsbdev = 16, /**< usbdev */
  kTopVerbanoAlertPeripheralPwrmgrAon = 17, /**< pwrmgr_aon */
  kTopVerbanoAlertPeripheralRstmgrAon = 18, /**< rstmgr_aon */
  kTopVerbanoAlertPeripheralClkmgrAon = 19, /**< clkmgr_aon */
  kTopVerbanoAlertPeripheralSysrstCtrlAon = 20, /**< sysrst_ctrl_aon */
  kTopVerbanoAlertPeripheralAdcCtrlAon = 21, /**< adc_ctrl_aon */
  kTopVerbanoAlertPeripheralPwmAon = 22, /**< pwm_aon */
  kTopVerbanoAlertPeripheralPinmuxAon = 23, /**< pinmux_aon */
  kTopVerbanoAlertPeripheralAonTimerAon = 24, /**< aon_timer_aon */
  kTopVerbanoAlertPeripheralSensorCtrlAon = 25, /**< sensor_ctrl_aon */
  kTopVerbanoAlertPeripheralSramCtrlRetAon = 26, /**< sram_ctrl_ret_aon */
  kTopVerbanoAlertPeripheralFlashCtrl = 27, /**< flash_ctrl */
  kTopVerbanoAlertPeripheralRvDm = 28, /**< rv_dm */
  kTopVerbanoAlertPeripheralRvPlic = 29, /**< rv_plic */
  kTopVerbanoAlertPeripheralAes = 30, /**< aes */
  kTopVerbanoAlertPeripheralHmac = 31, /**< hmac */
  kTopVerbanoAlertPeripheralKmac = 32, /**< kmac */
  kTopVerbanoAlertPeripheralOtbn = 33, /**< otbn */
  kTopVerbanoAlertPeripheralKeymgr = 34, /**< keymgr */
  kTopVerbanoAlertPeripheralCsrng = 35, /**< csrng */
  kTopVerbanoAlertPeripheralEntropySrc = 36, /**< entropy_src */
  kTopVerbanoAlertPeripheralEdn0 = 37, /**< edn0 */
  kTopVerbanoAlertPeripheralEdn1 = 38, /**< edn1 */
  kTopVerbanoAlertPeripheralSramCtrlMain = 39, /**< sram_ctrl_main */
  kTopVerbanoAlertPeripheralRomCtrl = 40, /**< rom_ctrl */
  kTopVerbanoAlertPeripheralRvCoreIbex = 41, /**< rv_core_ibex */
  kTopVerbanoAlertPeripheralLast = 41, /**< \internal Final Alert peripheral */
} top_verbano_alert_peripheral_t;

/**
 * Alert Handler Alert Source.
 *
 * Enumeration of all Alert Handler Alert Sources. The alert sources belonging to
 * the same peripheral are guaranteed to be consecutive.
 */
typedef enum top_verbano_alert_id {
  kTopVerbanoAlertIdUart0FatalFault = 0, /**< uart0_fatal_fault */
  kTopVerbanoAlertIdUart1FatalFault = 1, /**< uart1_fatal_fault */
  kTopVerbanoAlertIdUart2FatalFault = 2, /**< uart2_fatal_fault */
  kTopVerbanoAlertIdUart3FatalFault = 3, /**< uart3_fatal_fault */
  kTopVerbanoAlertIdGpioFatalFault = 4, /**< gpio_fatal_fault */
  kTopVerbanoAlertIdSpiDeviceFatalFault = 5, /**< spi_device_fatal_fault */
  kTopVerbanoAlertIdI2c0FatalFault = 6, /**< i2c0_fatal_fault */
  kTopVerbanoAlertIdI2c1FatalFault = 7, /**< i2c1_fatal_fault */
  kTopVerbanoAlertIdI2c2FatalFault = 8, /**< i2c2_fatal_fault */
  kTopVerbanoAlertIdPattgenFatalFault = 9, /**< pattgen_fatal_fault */
  kTopVerbanoAlertIdRvTimerFatalFault = 10, /**< rv_timer_fatal_fault */
  kTopVerbanoAlertIdOtpCtrlFatalMacroError = 11, /**< otp_ctrl_fatal_macro_error */
  kTopVerbanoAlertIdOtpCtrlFatalCheckError = 12, /**< otp_ctrl_fatal_check_error */
  kTopVerbanoAlertIdOtpCtrlFatalBusIntegError = 13, /**< otp_ctrl_fatal_bus_integ_error */
  kTopVerbanoAlertIdOtpCtrlFatalPrimOtpAlert = 14, /**< otp_ctrl_fatal_prim_otp_alert */
  kTopVerbanoAlertIdOtpCtrlRecovPrimOtpAlert = 15, /**< otp_ctrl_recov_prim_otp_alert */
  kTopVerbanoAlertIdLcCtrlFatalProgError = 16, /**< lc_ctrl_fatal_prog_error */
  kTopVerbanoAlertIdLcCtrlFatalStateError = 17, /**< lc_ctrl_fatal_state_error */
  kTopVerbanoAlertIdLcCtrlFatalBusIntegError = 18, /**< lc_ctrl_fatal_bus_integ_error */
  kTopVerbanoAlertIdSpiHost0FatalFault = 19, /**< spi_host0_fatal_fault */
  kTopVerbanoAlertIdSpiHost1FatalFault = 20, /**< spi_host1_fatal_fault */
  kTopVerbanoAlertIdUsbdevFatalFault = 21, /**< usbdev_fatal_fault */
  kTopVerbanoAlertIdPwrmgrAonFatalFault = 22, /**< pwrmgr_aon_fatal_fault */
  kTopVerbanoAlertIdRstmgrAonFatalFault = 23, /**< rstmgr_aon_fatal_fault */
  kTopVerbanoAlertIdRstmgrAonFatalCnstyFault = 24, /**< rstmgr_aon_fatal_cnsty_fault */
  kTopVerbanoAlertIdClkmgrAonRecovFault = 25, /**< clkmgr_aon_recov_fault */
  kTopVerbanoAlertIdClkmgrAonFatalFault = 26, /**< clkmgr_aon_fatal_fault */
  kTopVerbanoAlertIdSysrstCtrlAonFatalFault = 27, /**< sysrst_ctrl_aon_fatal_fault */
  kTopVerbanoAlertIdAdcCtrlAonFatalFault = 28, /**< adc_ctrl_aon_fatal_fault */
  kTopVerbanoAlertIdPwmAonFatalFault = 29, /**< pwm_aon_fatal_fault */
  kTopVerbanoAlertIdPinmuxAonFatalFault = 30, /**< pinmux_aon_fatal_fault */
  kTopVerbanoAlertIdAonTimerAonFatalFault = 31, /**< aon_timer_aon_fatal_fault */
  kTopVerbanoAlertIdSensorCtrlAonRecovAlert = 32, /**< sensor_ctrl_aon_recov_alert */
  kTopVerbanoAlertIdSensorCtrlAonFatalAlert = 33, /**< sensor_ctrl_aon_fatal_alert */
  kTopVerbanoAlertIdSramCtrlRetAonFatalError = 34, /**< sram_ctrl_ret_aon_fatal_error */
  kTopVerbanoAlertIdFlashCtrlRecovErr = 35, /**< flash_ctrl_recov_err */
  kTopVerbanoAlertIdFlashCtrlFatalStdErr = 36, /**< flash_ctrl_fatal_std_err */
  kTopVerbanoAlertIdFlashCtrlFatalErr = 37, /**< flash_ctrl_fatal_err */
  kTopVerbanoAlertIdFlashCtrlFatalPrimFlashAlert = 38, /**< flash_ctrl_fatal_prim_flash_alert */
  kTopVerbanoAlertIdFlashCtrlRecovPrimFlashAlert = 39, /**< flash_ctrl_recov_prim_flash_alert */
  kTopVerbanoAlertIdRvDmFatalFault = 40, /**< rv_dm_fatal_fault */
  kTopVerbanoAlertIdRvPlicFatalFault = 41, /**< rv_plic_fatal_fault */
  kTopVerbanoAlertIdAesRecovCtrlUpdateErr = 42, /**< aes_recov_ctrl_update_err */
  kTopVerbanoAlertIdAesFatalFault = 43, /**< aes_fatal_fault */
  kTopVerbanoAlertIdHmacFatalFault = 44, /**< hmac_fatal_fault */
  kTopVerbanoAlertIdKmacRecovOperationErr = 45, /**< kmac_recov_operation_err */
  kTopVerbanoAlertIdKmacFatalFaultErr = 46, /**< kmac_fatal_fault_err */
  kTopVerbanoAlertIdOtbnFatal = 47, /**< otbn_fatal */
  kTopVerbanoAlertIdOtbnRecov = 48, /**< otbn_recov */
  kTopVerbanoAlertIdKeymgrRecovOperationErr = 49, /**< keymgr_recov_operation_err */
  kTopVerbanoAlertIdKeymgrFatalFaultErr = 50, /**< keymgr_fatal_fault_err */
  kTopVerbanoAlertIdCsrngRecovAlert = 51, /**< csrng_recov_alert */
  kTopVerbanoAlertIdCsrngFatalAlert = 52, /**< csrng_fatal_alert */
  kTopVerbanoAlertIdEntropySrcRecovAlert = 53, /**< entropy_src_recov_alert */
  kTopVerbanoAlertIdEntropySrcFatalAlert = 54, /**< entropy_src_fatal_alert */
  kTopVerbanoAlertIdEdn0RecovAlert = 55, /**< edn0_recov_alert */
  kTopVerbanoAlertIdEdn0FatalAlert = 56, /**< edn0_fatal_alert */
  kTopVerbanoAlertIdEdn1RecovAlert = 57, /**< edn1_recov_alert */
  kTopVerbanoAlertIdEdn1FatalAlert = 58, /**< edn1_fatal_alert */
  kTopVerbanoAlertIdSramCtrlMainFatalError = 59, /**< sram_ctrl_main_fatal_error */
  kTopVerbanoAlertIdRomCtrlFatal = 60, /**< rom_ctrl_fatal */
  kTopVerbanoAlertIdRvCoreIbexFatalSwErr = 61, /**< rv_core_ibex_fatal_sw_err */
  kTopVerbanoAlertIdRvCoreIbexRecovSwErr = 62, /**< rv_core_ibex_recov_sw_err */
  kTopVerbanoAlertIdRvCoreIbexFatalHwErr = 63, /**< rv_core_ibex_fatal_hw_err */
  kTopVerbanoAlertIdRvCoreIbexRecovHwErr = 64, /**< rv_core_ibex_recov_hw_err */
  kTopVerbanoAlertIdLast = 64, /**< \internal The Last Valid Alert ID. */
} top_verbano_alert_id_t;

/**
 * Alert Handler Alert Source to Peripheral Map
 *
 * This array is a mapping from `top_verbano_alert_id_t` to
 * `top_verbano_alert_peripheral_t`.
 */
extern const top_verbano_alert_peripheral_t
    top_verbano_alert_for_peripheral[65];

#define PINMUX_MIO_PERIPH_INSEL_IDX_OFFSET 2

// PERIPH_INSEL ranges from 0 to NUM_MIO_PADS + 2 -1}
//  0 and 1 are tied to value 0 and 1
#define NUM_MIO_PADS 47
#define NUM_DIO_PADS 16

#define PINMUX_PERIPH_OUTSEL_IDX_OFFSET 3

/**
 * Pinmux Peripheral Input.
 */
typedef enum top_verbano_pinmux_peripheral_in {
  kTopVerbanoPinmuxPeripheralInGpioGpio0 = 0, /**< Peripheral Input 0 */
  kTopVerbanoPinmuxPeripheralInGpioGpio1 = 1, /**< Peripheral Input 1 */
  kTopVerbanoPinmuxPeripheralInGpioGpio2 = 2, /**< Peripheral Input 2 */
  kTopVerbanoPinmuxPeripheralInGpioGpio3 = 3, /**< Peripheral Input 3 */
  kTopVerbanoPinmuxPeripheralInGpioGpio4 = 4, /**< Peripheral Input 4 */
  kTopVerbanoPinmuxPeripheralInGpioGpio5 = 5, /**< Peripheral Input 5 */
  kTopVerbanoPinmuxPeripheralInGpioGpio6 = 6, /**< Peripheral Input 6 */
  kTopVerbanoPinmuxPeripheralInGpioGpio7 = 7, /**< Peripheral Input 7 */
  kTopVerbanoPinmuxPeripheralInGpioGpio8 = 8, /**< Peripheral Input 8 */
  kTopVerbanoPinmuxPeripheralInGpioGpio9 = 9, /**< Peripheral Input 9 */
  kTopVerbanoPinmuxPeripheralInGpioGpio10 = 10, /**< Peripheral Input 10 */
  kTopVerbanoPinmuxPeripheralInGpioGpio11 = 11, /**< Peripheral Input 11 */
  kTopVerbanoPinmuxPeripheralInGpioGpio12 = 12, /**< Peripheral Input 12 */
  kTopVerbanoPinmuxPeripheralInGpioGpio13 = 13, /**< Peripheral Input 13 */
  kTopVerbanoPinmuxPeripheralInGpioGpio14 = 14, /**< Peripheral Input 14 */
  kTopVerbanoPinmuxPeripheralInGpioGpio15 = 15, /**< Peripheral Input 15 */
  kTopVerbanoPinmuxPeripheralInGpioGpio16 = 16, /**< Peripheral Input 16 */
  kTopVerbanoPinmuxPeripheralInGpioGpio17 = 17, /**< Peripheral Input 17 */
  kTopVerbanoPinmuxPeripheralInGpioGpio18 = 18, /**< Peripheral Input 18 */
  kTopVerbanoPinmuxPeripheralInGpioGpio19 = 19, /**< Peripheral Input 19 */
  kTopVerbanoPinmuxPeripheralInGpioGpio20 = 20, /**< Peripheral Input 20 */
  kTopVerbanoPinmuxPeripheralInGpioGpio21 = 21, /**< Peripheral Input 21 */
  kTopVerbanoPinmuxPeripheralInGpioGpio22 = 22, /**< Peripheral Input 22 */
  kTopVerbanoPinmuxPeripheralInGpioGpio23 = 23, /**< Peripheral Input 23 */
  kTopVerbanoPinmuxPeripheralInGpioGpio24 = 24, /**< Peripheral Input 24 */
  kTopVerbanoPinmuxPeripheralInGpioGpio25 = 25, /**< Peripheral Input 25 */
  kTopVerbanoPinmuxPeripheralInGpioGpio26 = 26, /**< Peripheral Input 26 */
  kTopVerbanoPinmuxPeripheralInGpioGpio27 = 27, /**< Peripheral Input 27 */
  kTopVerbanoPinmuxPeripheralInGpioGpio28 = 28, /**< Peripheral Input 28 */
  kTopVerbanoPinmuxPeripheralInGpioGpio29 = 29, /**< Peripheral Input 29 */
  kTopVerbanoPinmuxPeripheralInGpioGpio30 = 30, /**< Peripheral Input 30 */
  kTopVerbanoPinmuxPeripheralInGpioGpio31 = 31, /**< Peripheral Input 31 */
  kTopVerbanoPinmuxPeripheralInI2c0Sda = 32, /**< Peripheral Input 32 */
  kTopVerbanoPinmuxPeripheralInI2c0Scl = 33, /**< Peripheral Input 33 */
  kTopVerbanoPinmuxPeripheralInI2c1Sda = 34, /**< Peripheral Input 34 */
  kTopVerbanoPinmuxPeripheralInI2c1Scl = 35, /**< Peripheral Input 35 */
  kTopVerbanoPinmuxPeripheralInI2c2Sda = 36, /**< Peripheral Input 36 */
  kTopVerbanoPinmuxPeripheralInI2c2Scl = 37, /**< Peripheral Input 37 */
  kTopVerbanoPinmuxPeripheralInSpiHost1Sd0 = 38, /**< Peripheral Input 38 */
  kTopVerbanoPinmuxPeripheralInSpiHost1Sd1 = 39, /**< Peripheral Input 39 */
  kTopVerbanoPinmuxPeripheralInSpiHost1Sd2 = 40, /**< Peripheral Input 40 */
  kTopVerbanoPinmuxPeripheralInSpiHost1Sd3 = 41, /**< Peripheral Input 41 */
  kTopVerbanoPinmuxPeripheralInUart0Rx = 42, /**< Peripheral Input 42 */
  kTopVerbanoPinmuxPeripheralInUart1Rx = 43, /**< Peripheral Input 43 */
  kTopVerbanoPinmuxPeripheralInUart2Rx = 44, /**< Peripheral Input 44 */
  kTopVerbanoPinmuxPeripheralInUart3Rx = 45, /**< Peripheral Input 45 */
  kTopVerbanoPinmuxPeripheralInSpiDeviceTpmCsb = 46, /**< Peripheral Input 46 */
  kTopVerbanoPinmuxPeripheralInFlashCtrlTck = 47, /**< Peripheral Input 47 */
  kTopVerbanoPinmuxPeripheralInFlashCtrlTms = 48, /**< Peripheral Input 48 */
  kTopVerbanoPinmuxPeripheralInFlashCtrlTdi = 49, /**< Peripheral Input 49 */
  kTopVerbanoPinmuxPeripheralInSysrstCtrlAonAcPresent = 50, /**< Peripheral Input 50 */
  kTopVerbanoPinmuxPeripheralInSysrstCtrlAonKey0In = 51, /**< Peripheral Input 51 */
  kTopVerbanoPinmuxPeripheralInSysrstCtrlAonKey1In = 52, /**< Peripheral Input 52 */
  kTopVerbanoPinmuxPeripheralInSysrstCtrlAonKey2In = 53, /**< Peripheral Input 53 */
  kTopVerbanoPinmuxPeripheralInSysrstCtrlAonPwrbIn = 54, /**< Peripheral Input 54 */
  kTopVerbanoPinmuxPeripheralInSysrstCtrlAonLidOpen = 55, /**< Peripheral Input 55 */
  kTopVerbanoPinmuxPeripheralInUsbdevSense = 56, /**< Peripheral Input 56 */
  kTopVerbanoPinmuxPeripheralInLast = 56, /**< \internal Last valid peripheral input */
} top_verbano_pinmux_peripheral_in_t;

/**
 * Pinmux MIO Input Selector.
 */
typedef enum top_verbano_pinmux_insel {
  kTopVerbanoPinmuxInselConstantZero = 0, /**< Tie constantly to zero */
  kTopVerbanoPinmuxInselConstantOne = 1, /**< Tie constantly to one */
  kTopVerbanoPinmuxInselIoa0 = 2, /**< MIO Pad 0 */
  kTopVerbanoPinmuxInselIoa1 = 3, /**< MIO Pad 1 */
  kTopVerbanoPinmuxInselIoa2 = 4, /**< MIO Pad 2 */
  kTopVerbanoPinmuxInselIoa3 = 5, /**< MIO Pad 3 */
  kTopVerbanoPinmuxInselIoa4 = 6, /**< MIO Pad 4 */
  kTopVerbanoPinmuxInselIoa5 = 7, /**< MIO Pad 5 */
  kTopVerbanoPinmuxInselIoa6 = 8, /**< MIO Pad 6 */
  kTopVerbanoPinmuxInselIoa7 = 9, /**< MIO Pad 7 */
  kTopVerbanoPinmuxInselIoa8 = 10, /**< MIO Pad 8 */
  kTopVerbanoPinmuxInselIob0 = 11, /**< MIO Pad 9 */
  kTopVerbanoPinmuxInselIob1 = 12, /**< MIO Pad 10 */
  kTopVerbanoPinmuxInselIob2 = 13, /**< MIO Pad 11 */
  kTopVerbanoPinmuxInselIob3 = 14, /**< MIO Pad 12 */
  kTopVerbanoPinmuxInselIob4 = 15, /**< MIO Pad 13 */
  kTopVerbanoPinmuxInselIob5 = 16, /**< MIO Pad 14 */
  kTopVerbanoPinmuxInselIob6 = 17, /**< MIO Pad 15 */
  kTopVerbanoPinmuxInselIob7 = 18, /**< MIO Pad 16 */
  kTopVerbanoPinmuxInselIob8 = 19, /**< MIO Pad 17 */
  kTopVerbanoPinmuxInselIob9 = 20, /**< MIO Pad 18 */
  kTopVerbanoPinmuxInselIob10 = 21, /**< MIO Pad 19 */
  kTopVerbanoPinmuxInselIob11 = 22, /**< MIO Pad 20 */
  kTopVerbanoPinmuxInselIob12 = 23, /**< MIO Pad 21 */
  kTopVerbanoPinmuxInselIoc0 = 24, /**< MIO Pad 22 */
  kTopVerbanoPinmuxInselIoc1 = 25, /**< MIO Pad 23 */
  kTopVerbanoPinmuxInselIoc2 = 26, /**< MIO Pad 24 */
  kTopVerbanoPinmuxInselIoc3 = 27, /**< MIO Pad 25 */
  kTopVerbanoPinmuxInselIoc4 = 28, /**< MIO Pad 26 */
  kTopVerbanoPinmuxInselIoc5 = 29, /**< MIO Pad 27 */
  kTopVerbanoPinmuxInselIoc6 = 30, /**< MIO Pad 28 */
  kTopVerbanoPinmuxInselIoc7 = 31, /**< MIO Pad 29 */
  kTopVerbanoPinmuxInselIoc8 = 32, /**< MIO Pad 30 */
  kTopVerbanoPinmuxInselIoc9 = 33, /**< MIO Pad 31 */
  kTopVerbanoPinmuxInselIoc10 = 34, /**< MIO Pad 32 */
  kTopVerbanoPinmuxInselIoc11 = 35, /**< MIO Pad 33 */
  kTopVerbanoPinmuxInselIoc12 = 36, /**< MIO Pad 34 */
  kTopVerbanoPinmuxInselIor0 = 37, /**< MIO Pad 35 */
  kTopVerbanoPinmuxInselIor1 = 38, /**< MIO Pad 36 */
  kTopVerbanoPinmuxInselIor2 = 39, /**< MIO Pad 37 */
  kTopVerbanoPinmuxInselIor3 = 40, /**< MIO Pad 38 */
  kTopVerbanoPinmuxInselIor4 = 41, /**< MIO Pad 39 */
  kTopVerbanoPinmuxInselIor5 = 42, /**< MIO Pad 40 */
  kTopVerbanoPinmuxInselIor6 = 43, /**< MIO Pad 41 */
  kTopVerbanoPinmuxInselIor7 = 44, /**< MIO Pad 42 */
  kTopVerbanoPinmuxInselIor10 = 45, /**< MIO Pad 43 */
  kTopVerbanoPinmuxInselIor11 = 46, /**< MIO Pad 44 */
  kTopVerbanoPinmuxInselIor12 = 47, /**< MIO Pad 45 */
  kTopVerbanoPinmuxInselIor13 = 48, /**< MIO Pad 46 */
  kTopVerbanoPinmuxInselLast = 48, /**< \internal Last valid insel value */
} top_verbano_pinmux_insel_t;

/**
 * Pinmux MIO Output.
 */
typedef enum top_verbano_pinmux_mio_out {
  kTopVerbanoPinmuxMioOutIoa0 = 0, /**< MIO Pad 0 */
  kTopVerbanoPinmuxMioOutIoa1 = 1, /**< MIO Pad 1 */
  kTopVerbanoPinmuxMioOutIoa2 = 2, /**< MIO Pad 2 */
  kTopVerbanoPinmuxMioOutIoa3 = 3, /**< MIO Pad 3 */
  kTopVerbanoPinmuxMioOutIoa4 = 4, /**< MIO Pad 4 */
  kTopVerbanoPinmuxMioOutIoa5 = 5, /**< MIO Pad 5 */
  kTopVerbanoPinmuxMioOutIoa6 = 6, /**< MIO Pad 6 */
  kTopVerbanoPinmuxMioOutIoa7 = 7, /**< MIO Pad 7 */
  kTopVerbanoPinmuxMioOutIoa8 = 8, /**< MIO Pad 8 */
  kTopVerbanoPinmuxMioOutIob0 = 9, /**< MIO Pad 9 */
  kTopVerbanoPinmuxMioOutIob1 = 10, /**< MIO Pad 10 */
  kTopVerbanoPinmuxMioOutIob2 = 11, /**< MIO Pad 11 */
  kTopVerbanoPinmuxMioOutIob3 = 12, /**< MIO Pad 12 */
  kTopVerbanoPinmuxMioOutIob4 = 13, /**< MIO Pad 13 */
  kTopVerbanoPinmuxMioOutIob5 = 14, /**< MIO Pad 14 */
  kTopVerbanoPinmuxMioOutIob6 = 15, /**< MIO Pad 15 */
  kTopVerbanoPinmuxMioOutIob7 = 16, /**< MIO Pad 16 */
  kTopVerbanoPinmuxMioOutIob8 = 17, /**< MIO Pad 17 */
  kTopVerbanoPinmuxMioOutIob9 = 18, /**< MIO Pad 18 */
  kTopVerbanoPinmuxMioOutIob10 = 19, /**< MIO Pad 19 */
  kTopVerbanoPinmuxMioOutIob11 = 20, /**< MIO Pad 20 */
  kTopVerbanoPinmuxMioOutIob12 = 21, /**< MIO Pad 21 */
  kTopVerbanoPinmuxMioOutIoc0 = 22, /**< MIO Pad 22 */
  kTopVerbanoPinmuxMioOutIoc1 = 23, /**< MIO Pad 23 */
  kTopVerbanoPinmuxMioOutIoc2 = 24, /**< MIO Pad 24 */
  kTopVerbanoPinmuxMioOutIoc3 = 25, /**< MIO Pad 25 */
  kTopVerbanoPinmuxMioOutIoc4 = 26, /**< MIO Pad 26 */
  kTopVerbanoPinmuxMioOutIoc5 = 27, /**< MIO Pad 27 */
  kTopVerbanoPinmuxMioOutIoc6 = 28, /**< MIO Pad 28 */
  kTopVerbanoPinmuxMioOutIoc7 = 29, /**< MIO Pad 29 */
  kTopVerbanoPinmuxMioOutIoc8 = 30, /**< MIO Pad 30 */
  kTopVerbanoPinmuxMioOutIoc9 = 31, /**< MIO Pad 31 */
  kTopVerbanoPinmuxMioOutIoc10 = 32, /**< MIO Pad 32 */
  kTopVerbanoPinmuxMioOutIoc11 = 33, /**< MIO Pad 33 */
  kTopVerbanoPinmuxMioOutIoc12 = 34, /**< MIO Pad 34 */
  kTopVerbanoPinmuxMioOutIor0 = 35, /**< MIO Pad 35 */
  kTopVerbanoPinmuxMioOutIor1 = 36, /**< MIO Pad 36 */
  kTopVerbanoPinmuxMioOutIor2 = 37, /**< MIO Pad 37 */
  kTopVerbanoPinmuxMioOutIor3 = 38, /**< MIO Pad 38 */
  kTopVerbanoPinmuxMioOutIor4 = 39, /**< MIO Pad 39 */
  kTopVerbanoPinmuxMioOutIor5 = 40, /**< MIO Pad 40 */
  kTopVerbanoPinmuxMioOutIor6 = 41, /**< MIO Pad 41 */
  kTopVerbanoPinmuxMioOutIor7 = 42, /**< MIO Pad 42 */
  kTopVerbanoPinmuxMioOutIor10 = 43, /**< MIO Pad 43 */
  kTopVerbanoPinmuxMioOutIor11 = 44, /**< MIO Pad 44 */
  kTopVerbanoPinmuxMioOutIor12 = 45, /**< MIO Pad 45 */
  kTopVerbanoPinmuxMioOutIor13 = 46, /**< MIO Pad 46 */
  kTopVerbanoPinmuxMioOutLast = 46, /**< \internal Last valid mio output */
} top_verbano_pinmux_mio_out_t;

/**
 * Pinmux Peripheral Output Selector.
 */
typedef enum top_verbano_pinmux_outsel {
  kTopVerbanoPinmuxOutselConstantZero = 0, /**< Tie constantly to zero */
  kTopVerbanoPinmuxOutselConstantOne = 1, /**< Tie constantly to one */
  kTopVerbanoPinmuxOutselConstantHighZ = 2, /**< Tie constantly to high-Z */
  kTopVerbanoPinmuxOutselGpioGpio0 = 3, /**< Peripheral Output 0 */
  kTopVerbanoPinmuxOutselGpioGpio1 = 4, /**< Peripheral Output 1 */
  kTopVerbanoPinmuxOutselGpioGpio2 = 5, /**< Peripheral Output 2 */
  kTopVerbanoPinmuxOutselGpioGpio3 = 6, /**< Peripheral Output 3 */
  kTopVerbanoPinmuxOutselGpioGpio4 = 7, /**< Peripheral Output 4 */
  kTopVerbanoPinmuxOutselGpioGpio5 = 8, /**< Peripheral Output 5 */
  kTopVerbanoPinmuxOutselGpioGpio6 = 9, /**< Peripheral Output 6 */
  kTopVerbanoPinmuxOutselGpioGpio7 = 10, /**< Peripheral Output 7 */
  kTopVerbanoPinmuxOutselGpioGpio8 = 11, /**< Peripheral Output 8 */
  kTopVerbanoPinmuxOutselGpioGpio9 = 12, /**< Peripheral Output 9 */
  kTopVerbanoPinmuxOutselGpioGpio10 = 13, /**< Peripheral Output 10 */
  kTopVerbanoPinmuxOutselGpioGpio11 = 14, /**< Peripheral Output 11 */
  kTopVerbanoPinmuxOutselGpioGpio12 = 15, /**< Peripheral Output 12 */
  kTopVerbanoPinmuxOutselGpioGpio13 = 16, /**< Peripheral Output 13 */
  kTopVerbanoPinmuxOutselGpioGpio14 = 17, /**< Peripheral Output 14 */
  kTopVerbanoPinmuxOutselGpioGpio15 = 18, /**< Peripheral Output 15 */
  kTopVerbanoPinmuxOutselGpioGpio16 = 19, /**< Peripheral Output 16 */
  kTopVerbanoPinmuxOutselGpioGpio17 = 20, /**< Peripheral Output 17 */
  kTopVerbanoPinmuxOutselGpioGpio18 = 21, /**< Peripheral Output 18 */
  kTopVerbanoPinmuxOutselGpioGpio19 = 22, /**< Peripheral Output 19 */
  kTopVerbanoPinmuxOutselGpioGpio20 = 23, /**< Peripheral Output 20 */
  kTopVerbanoPinmuxOutselGpioGpio21 = 24, /**< Peripheral Output 21 */
  kTopVerbanoPinmuxOutselGpioGpio22 = 25, /**< Peripheral Output 22 */
  kTopVerbanoPinmuxOutselGpioGpio23 = 26, /**< Peripheral Output 23 */
  kTopVerbanoPinmuxOutselGpioGpio24 = 27, /**< Peripheral Output 24 */
  kTopVerbanoPinmuxOutselGpioGpio25 = 28, /**< Peripheral Output 25 */
  kTopVerbanoPinmuxOutselGpioGpio26 = 29, /**< Peripheral Output 26 */
  kTopVerbanoPinmuxOutselGpioGpio27 = 30, /**< Peripheral Output 27 */
  kTopVerbanoPinmuxOutselGpioGpio28 = 31, /**< Peripheral Output 28 */
  kTopVerbanoPinmuxOutselGpioGpio29 = 32, /**< Peripheral Output 29 */
  kTopVerbanoPinmuxOutselGpioGpio30 = 33, /**< Peripheral Output 30 */
  kTopVerbanoPinmuxOutselGpioGpio31 = 34, /**< Peripheral Output 31 */
  kTopVerbanoPinmuxOutselI2c0Sda = 35, /**< Peripheral Output 32 */
  kTopVerbanoPinmuxOutselI2c0Scl = 36, /**< Peripheral Output 33 */
  kTopVerbanoPinmuxOutselI2c1Sda = 37, /**< Peripheral Output 34 */
  kTopVerbanoPinmuxOutselI2c1Scl = 38, /**< Peripheral Output 35 */
  kTopVerbanoPinmuxOutselI2c2Sda = 39, /**< Peripheral Output 36 */
  kTopVerbanoPinmuxOutselI2c2Scl = 40, /**< Peripheral Output 37 */
  kTopVerbanoPinmuxOutselSpiHost1Sd0 = 41, /**< Peripheral Output 38 */
  kTopVerbanoPinmuxOutselSpiHost1Sd1 = 42, /**< Peripheral Output 39 */
  kTopVerbanoPinmuxOutselSpiHost1Sd2 = 43, /**< Peripheral Output 40 */
  kTopVerbanoPinmuxOutselSpiHost1Sd3 = 44, /**< Peripheral Output 41 */
  kTopVerbanoPinmuxOutselUart0Tx = 45, /**< Peripheral Output 42 */
  kTopVerbanoPinmuxOutselUart1Tx = 46, /**< Peripheral Output 43 */
  kTopVerbanoPinmuxOutselUart2Tx = 47, /**< Peripheral Output 44 */
  kTopVerbanoPinmuxOutselUart3Tx = 48, /**< Peripheral Output 45 */
  kTopVerbanoPinmuxOutselPattgenPda0Tx = 49, /**< Peripheral Output 46 */
  kTopVerbanoPinmuxOutselPattgenPcl0Tx = 50, /**< Peripheral Output 47 */
  kTopVerbanoPinmuxOutselPattgenPda1Tx = 51, /**< Peripheral Output 48 */
  kTopVerbanoPinmuxOutselPattgenPcl1Tx = 52, /**< Peripheral Output 49 */
  kTopVerbanoPinmuxOutselSpiHost1Sck = 53, /**< Peripheral Output 50 */
  kTopVerbanoPinmuxOutselSpiHost1Csb = 54, /**< Peripheral Output 51 */
  kTopVerbanoPinmuxOutselFlashCtrlTdo = 55, /**< Peripheral Output 52 */
  kTopVerbanoPinmuxOutselSensorCtrlAonAstDebugOut0 = 56, /**< Peripheral Output 53 */
  kTopVerbanoPinmuxOutselSensorCtrlAonAstDebugOut1 = 57, /**< Peripheral Output 54 */
  kTopVerbanoPinmuxOutselSensorCtrlAonAstDebugOut2 = 58, /**< Peripheral Output 55 */
  kTopVerbanoPinmuxOutselSensorCtrlAonAstDebugOut3 = 59, /**< Peripheral Output 56 */
  kTopVerbanoPinmuxOutselSensorCtrlAonAstDebugOut4 = 60, /**< Peripheral Output 57 */
  kTopVerbanoPinmuxOutselSensorCtrlAonAstDebugOut5 = 61, /**< Peripheral Output 58 */
  kTopVerbanoPinmuxOutselSensorCtrlAonAstDebugOut6 = 62, /**< Peripheral Output 59 */
  kTopVerbanoPinmuxOutselSensorCtrlAonAstDebugOut7 = 63, /**< Peripheral Output 60 */
  kTopVerbanoPinmuxOutselSensorCtrlAonAstDebugOut8 = 64, /**< Peripheral Output 61 */
  kTopVerbanoPinmuxOutselPwmAonPwm0 = 65, /**< Peripheral Output 62 */
  kTopVerbanoPinmuxOutselPwmAonPwm1 = 66, /**< Peripheral Output 63 */
  kTopVerbanoPinmuxOutselPwmAonPwm2 = 67, /**< Peripheral Output 64 */
  kTopVerbanoPinmuxOutselPwmAonPwm3 = 68, /**< Peripheral Output 65 */
  kTopVerbanoPinmuxOutselPwmAonPwm4 = 69, /**< Peripheral Output 66 */
  kTopVerbanoPinmuxOutselPwmAonPwm5 = 70, /**< Peripheral Output 67 */
  kTopVerbanoPinmuxOutselOtpMacroTest0 = 71, /**< Peripheral Output 68 */
  kTopVerbanoPinmuxOutselSysrstCtrlAonBatDisable = 72, /**< Peripheral Output 69 */
  kTopVerbanoPinmuxOutselSysrstCtrlAonKey0Out = 73, /**< Peripheral Output 70 */
  kTopVerbanoPinmuxOutselSysrstCtrlAonKey1Out = 74, /**< Peripheral Output 71 */
  kTopVerbanoPinmuxOutselSysrstCtrlAonKey2Out = 75, /**< Peripheral Output 72 */
  kTopVerbanoPinmuxOutselSysrstCtrlAonPwrbOut = 76, /**< Peripheral Output 73 */
  kTopVerbanoPinmuxOutselSysrstCtrlAonZ3Wakeup = 77, /**< Peripheral Output 74 */
  kTopVerbanoPinmuxOutselLast = 77, /**< \internal Last valid outsel value */
} top_verbano_pinmux_outsel_t;

/**
 * Dedicated Pad Selects
 */
typedef enum top_verbano_direct_pads {
  kTopVerbanoDirectPadsUsbdevUsbDp = 0, /**<  */
  kTopVerbanoDirectPadsUsbdevUsbDn = 1, /**<  */
  kTopVerbanoDirectPadsSpiHost0Sd0 = 2, /**<  */
  kTopVerbanoDirectPadsSpiHost0Sd1 = 3, /**<  */
  kTopVerbanoDirectPadsSpiHost0Sd2 = 4, /**<  */
  kTopVerbanoDirectPadsSpiHost0Sd3 = 5, /**<  */
  kTopVerbanoDirectPadsSpiDeviceSd0 = 6, /**<  */
  kTopVerbanoDirectPadsSpiDeviceSd1 = 7, /**<  */
  kTopVerbanoDirectPadsSpiDeviceSd2 = 8, /**<  */
  kTopVerbanoDirectPadsSpiDeviceSd3 = 9, /**<  */
  kTopVerbanoDirectPadsSysrstCtrlAonEcRstL = 10, /**<  */
  kTopVerbanoDirectPadsSysrstCtrlAonFlashWpL = 11, /**<  */
  kTopVerbanoDirectPadsSpiDeviceSck = 12, /**<  */
  kTopVerbanoDirectPadsSpiDeviceCsb = 13, /**<  */
  kTopVerbanoDirectPadsSpiHost0Sck = 14, /**<  */
  kTopVerbanoDirectPadsSpiHost0Csb = 15, /**<  */
  kTopVerbanoDirectPadsLast = 15, /**< \internal Last valid direct pad */
} top_verbano_direct_pads_t;

/**
 * Muxed Pad Selects
 */
typedef enum top_verbano_muxed_pads {
  kTopVerbanoMuxedPadsIoa0 = 0, /**<  */
  kTopVerbanoMuxedPadsIoa1 = 1, /**<  */
  kTopVerbanoMuxedPadsIoa2 = 2, /**<  */
  kTopVerbanoMuxedPadsIoa3 = 3, /**<  */
  kTopVerbanoMuxedPadsIoa4 = 4, /**<  */
  kTopVerbanoMuxedPadsIoa5 = 5, /**<  */
  kTopVerbanoMuxedPadsIoa6 = 6, /**<  */
  kTopVerbanoMuxedPadsIoa7 = 7, /**<  */
  kTopVerbanoMuxedPadsIoa8 = 8, /**<  */
  kTopVerbanoMuxedPadsIob0 = 9, /**<  */
  kTopVerbanoMuxedPadsIob1 = 10, /**<  */
  kTopVerbanoMuxedPadsIob2 = 11, /**<  */
  kTopVerbanoMuxedPadsIob3 = 12, /**<  */
  kTopVerbanoMuxedPadsIob4 = 13, /**<  */
  kTopVerbanoMuxedPadsIob5 = 14, /**<  */
  kTopVerbanoMuxedPadsIob6 = 15, /**<  */
  kTopVerbanoMuxedPadsIob7 = 16, /**<  */
  kTopVerbanoMuxedPadsIob8 = 17, /**<  */
  kTopVerbanoMuxedPadsIob9 = 18, /**<  */
  kTopVerbanoMuxedPadsIob10 = 19, /**<  */
  kTopVerbanoMuxedPadsIob11 = 20, /**<  */
  kTopVerbanoMuxedPadsIob12 = 21, /**<  */
  kTopVerbanoMuxedPadsIoc0 = 22, /**<  */
  kTopVerbanoMuxedPadsIoc1 = 23, /**<  */
  kTopVerbanoMuxedPadsIoc2 = 24, /**<  */
  kTopVerbanoMuxedPadsIoc3 = 25, /**<  */
  kTopVerbanoMuxedPadsIoc4 = 26, /**<  */
  kTopVerbanoMuxedPadsIoc5 = 27, /**<  */
  kTopVerbanoMuxedPadsIoc6 = 28, /**<  */
  kTopVerbanoMuxedPadsIoc7 = 29, /**<  */
  kTopVerbanoMuxedPadsIoc8 = 30, /**<  */
  kTopVerbanoMuxedPadsIoc9 = 31, /**<  */
  kTopVerbanoMuxedPadsIoc10 = 32, /**<  */
  kTopVerbanoMuxedPadsIoc11 = 33, /**<  */
  kTopVerbanoMuxedPadsIoc12 = 34, /**<  */
  kTopVerbanoMuxedPadsIor0 = 35, /**<  */
  kTopVerbanoMuxedPadsIor1 = 36, /**<  */
  kTopVerbanoMuxedPadsIor2 = 37, /**<  */
  kTopVerbanoMuxedPadsIor3 = 38, /**<  */
  kTopVerbanoMuxedPadsIor4 = 39, /**<  */
  kTopVerbanoMuxedPadsIor5 = 40, /**<  */
  kTopVerbanoMuxedPadsIor6 = 41, /**<  */
  kTopVerbanoMuxedPadsIor7 = 42, /**<  */
  kTopVerbanoMuxedPadsIor10 = 43, /**<  */
  kTopVerbanoMuxedPadsIor11 = 44, /**<  */
  kTopVerbanoMuxedPadsIor12 = 45, /**<  */
  kTopVerbanoMuxedPadsIor13 = 46, /**<  */
  kTopVerbanoMuxedPadsLast = 46, /**< \internal Last valid muxed pad */
} top_verbano_muxed_pads_t;

/**
 * Power Manager Wakeup Signals
 */
typedef enum top_verbano_power_manager_wake_ups {
  kTopVerbanoPowerManagerWakeUpsSysrstCtrlAonWkupReq = 0, /**<  */
  kTopVerbanoPowerManagerWakeUpsAdcCtrlAonWkupReq = 1, /**<  */
  kTopVerbanoPowerManagerWakeUpsPinmuxAonPinWkupReq = 2, /**<  */
  kTopVerbanoPowerManagerWakeUpsPinmuxAonUsbWkupReq = 3, /**<  */
  kTopVerbanoPowerManagerWakeUpsAonTimerAonWkupReq = 4, /**<  */
  kTopVerbanoPowerManagerWakeUpsSensorCtrlAonWkupReq = 5, /**<  */
  kTopVerbanoPowerManagerWakeUpsLast = 5, /**< \internal Last valid pwrmgr wakeup signal */
} top_verbano_power_manager_wake_ups_t;

/**
 * Reset Manager Software Controlled Resets
 */
typedef enum top_verbano_reset_manager_sw_resets {
  kTopVerbanoResetManagerSwResetsSpiDevice = 0, /**<  */
  kTopVerbanoResetManagerSwResetsSpiHost0 = 1, /**<  */
  kTopVerbanoResetManagerSwResetsSpiHost1 = 2, /**<  */
  kTopVerbanoResetManagerSwResetsUsb = 3, /**<  */
  kTopVerbanoResetManagerSwResetsUsbAon = 4, /**<  */
  kTopVerbanoResetManagerSwResetsI2c0 = 5, /**<  */
  kTopVerbanoResetManagerSwResetsI2c1 = 6, /**<  */
  kTopVerbanoResetManagerSwResetsI2c2 = 7, /**<  */
  kTopVerbanoResetManagerSwResetsLast = 7, /**< \internal Last valid rstmgr software reset request */
} top_verbano_reset_manager_sw_resets_t;

/**
 * Power Manager Reset Request Signals
 */
typedef enum top_verbano_power_manager_reset_requests {
  kTopVerbanoPowerManagerResetRequestsSysrstCtrlAonRstReq = 0, /**<  */
  kTopVerbanoPowerManagerResetRequestsAonTimerAonAonTimerRstReq = 1, /**<  */
  kTopVerbanoPowerManagerResetRequestsLast = 1, /**< \internal Last valid pwrmgr reset_request signal */
} top_verbano_power_manager_reset_requests_t;

/**
 * Clock Manager Software-Controlled ("Gated") Clocks.
 *
 * The Software has full control over these clocks.
 */
typedef enum top_verbano_gateable_clocks {
  kTopVerbanoGateableClocksIoDiv4Peri = 0, /**< Clock clk_io_div4_peri in group peri */
  kTopVerbanoGateableClocksIoDiv2Peri = 1, /**< Clock clk_io_div2_peri in group peri */
  kTopVerbanoGateableClocksIoPeri = 2, /**< Clock clk_io_peri in group peri */
  kTopVerbanoGateableClocksUsbPeri = 3, /**< Clock clk_usb_peri in group peri */
  kTopVerbanoGateableClocksLast = 3, /**< \internal Last Valid Gateable Clock */
} top_verbano_gateable_clocks_t;

/**
 * Clock Manager Software-Hinted Clocks.
 *
 * The Software has partial control over these clocks. It can ask them to stop,
 * but the clock manager is in control of whether the clock actually is stopped.
 */
typedef enum top_verbano_hintable_clocks {
  kTopVerbanoHintableClocksMainAes = 0, /**< Clock clk_main_aes in group trans */
  kTopVerbanoHintableClocksMainHmac = 1, /**< Clock clk_main_hmac in group trans */
  kTopVerbanoHintableClocksMainKmac = 2, /**< Clock clk_main_kmac in group trans */
  kTopVerbanoHintableClocksMainOtbn = 3, /**< Clock clk_main_otbn in group trans */
  kTopVerbanoHintableClocksLast = 3, /**< \internal Last Valid Hintable Clock */
} top_verbano_hintable_clocks_t;

/**
 * MMIO Region
 *
 * MMIO region excludes any memory that is separate from the module
 * configuration space, i.e. ROM, main SRAM, and flash are excluded but
 * retention SRAM, spi_device memory, or usbdev memory are included.
 */
#define TOP_VERBANO_MMIO_BASE_ADDR 0x40000000u
#define TOP_VERBANO_MMIO_SIZE_BYTES 0x10000000u

// Header Extern Guard
#ifdef __cplusplus
}  // extern "C"
#endif

#endif  // OPENTITAN_HW_TOP_VERBANO_SW_AUTOGEN_TOP_VERBANO_H_
