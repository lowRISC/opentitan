// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
// util/topgen.py -t hw/top_earlgrey/data/top_earlgrey.hjson
//                -o hw/top_earlgrey/

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
 * Peripheral base address for uart0 in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_UART0_BASE_ADDR 0x40000000u

/**
 * Peripheral size for uart0 in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_UART0_BASE_ADDR and
 * `TOP_EARLGREY_UART0_BASE_ADDR + TOP_EARLGREY_UART0_SIZE_BYTES`.
 */
#define TOP_EARLGREY_UART0_SIZE_BYTES 0x40u

/**
 * Peripheral base address for uart1 in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_UART1_BASE_ADDR 0x40010000u

/**
 * Peripheral size for uart1 in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_UART1_BASE_ADDR and
 * `TOP_EARLGREY_UART1_BASE_ADDR + TOP_EARLGREY_UART1_SIZE_BYTES`.
 */
#define TOP_EARLGREY_UART1_SIZE_BYTES 0x40u

/**
 * Peripheral base address for uart2 in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_UART2_BASE_ADDR 0x40020000u

/**
 * Peripheral size for uart2 in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_UART2_BASE_ADDR and
 * `TOP_EARLGREY_UART2_BASE_ADDR + TOP_EARLGREY_UART2_SIZE_BYTES`.
 */
#define TOP_EARLGREY_UART2_SIZE_BYTES 0x40u

/**
 * Peripheral base address for uart3 in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_UART3_BASE_ADDR 0x40030000u

/**
 * Peripheral size for uart3 in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_UART3_BASE_ADDR and
 * `TOP_EARLGREY_UART3_BASE_ADDR + TOP_EARLGREY_UART3_SIZE_BYTES`.
 */
#define TOP_EARLGREY_UART3_SIZE_BYTES 0x40u

/**
 * Peripheral base address for gpio0 in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_GPIO0_BASE_ADDR 0x40040000u

/**
 * Peripheral size for gpio0 in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_GPIO0_BASE_ADDR and
 * `TOP_EARLGREY_GPIO0_BASE_ADDR + TOP_EARLGREY_GPIO0_SIZE_BYTES`.
 */
#define TOP_EARLGREY_GPIO0_SIZE_BYTES 0x400u

/**
 * Peripheral base address for gpio1 in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_GPIO1_BASE_ADDR 0x40050000u

/**
 * Peripheral size for gpio1 in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_GPIO1_BASE_ADDR and
 * `TOP_EARLGREY_GPIO1_BASE_ADDR + TOP_EARLGREY_GPIO1_SIZE_BYTES`.
 */
#define TOP_EARLGREY_GPIO1_SIZE_BYTES 0x400u

/**
 * Peripheral base address for spi_device in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_SPI_DEVICE_BASE_ADDR 0x40060000u

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
 * Peripheral base address for i2c0 in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_I2C0_BASE_ADDR 0x40080000u

/**
 * Peripheral size for i2c0 in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_I2C0_BASE_ADDR and
 * `TOP_EARLGREY_I2C0_BASE_ADDR + TOP_EARLGREY_I2C0_SIZE_BYTES`.
 */
#define TOP_EARLGREY_I2C0_SIZE_BYTES 0x80u

/**
 * Peripheral base address for i2c1 in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_I2C1_BASE_ADDR 0x40090000u

/**
 * Peripheral size for i2c1 in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_I2C1_BASE_ADDR and
 * `TOP_EARLGREY_I2C1_BASE_ADDR + TOP_EARLGREY_I2C1_SIZE_BYTES`.
 */
#define TOP_EARLGREY_I2C1_SIZE_BYTES 0x80u

/**
 * Peripheral base address for i2c2 in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_I2C2_BASE_ADDR 0x400A0000u

/**
 * Peripheral size for i2c2 in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_I2C2_BASE_ADDR and
 * `TOP_EARLGREY_I2C2_BASE_ADDR + TOP_EARLGREY_I2C2_SIZE_BYTES`.
 */
#define TOP_EARLGREY_I2C2_SIZE_BYTES 0x80u

/**
 * Peripheral base address for i3c0 in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_I3C0_BASE_ADDR 0x40330000u

/**
 * Peripheral size for i3c0 in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_I3C0_BASE_ADDR and
 * `TOP_EARLGREY_I3C0_BASE_ADDR + TOP_EARLGREY_I3C0_SIZE_BYTES`.
 */
#define TOP_EARLGREY_I3C0_SIZE_BYTES 0x2000u

/**
 * Peripheral base address for i3c1 in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_I3C1_BASE_ADDR 0x40340000u

/**
 * Peripheral size for i3c1 in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_I3C1_BASE_ADDR and
 * `TOP_EARLGREY_I3C1_BASE_ADDR + TOP_EARLGREY_I3C1_SIZE_BYTES`.
 */
#define TOP_EARLGREY_I3C1_SIZE_BYTES 0x2000u

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
#define TOP_EARLGREY_RV_TIMER_SIZE_BYTES 0x200u

/**
 * Peripheral base address for core device on otp_ctrl in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR 0x40130000u

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
 * Peripheral base address for regs device on lc_ctrl in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_LC_CTRL_REGS_BASE_ADDR 0x40140000u

/**
 * Peripheral size for regs device on lc_ctrl in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_LC_CTRL_REGS_BASE_ADDR and
 * `TOP_EARLGREY_LC_CTRL_REGS_BASE_ADDR + TOP_EARLGREY_LC_CTRL_REGS_SIZE_BYTES`.
 */
#define TOP_EARLGREY_LC_CTRL_REGS_SIZE_BYTES 0x100u

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
#define TOP_EARLGREY_ALERT_HANDLER_SIZE_BYTES 0x800u

/**
 * Peripheral base address for spi_host0 in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_SPI_HOST0_BASE_ADDR 0x40300000u

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
#define TOP_EARLGREY_SPI_HOST1_BASE_ADDR 0x40310000u

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
 * Peripheral base address for usbdev in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_USBDEV_BASE_ADDR 0x40320000u

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
#define TOP_EARLGREY_PWRMGR_SIZE_BYTES 0x80u

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
#define TOP_EARLGREY_RSTMGR_SIZE_BYTES 0x80u

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
#define TOP_EARLGREY_CLKMGR_SIZE_BYTES 0x80u

/**
 * Peripheral base address for sysrst_ctrl in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_SYSRST_CTRL_BASE_ADDR 0x40430000u

/**
 * Peripheral size for sysrst_ctrl in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_SYSRST_CTRL_BASE_ADDR and
 * `TOP_EARLGREY_SYSRST_CTRL_BASE_ADDR + TOP_EARLGREY_SYSRST_CTRL_SIZE_BYTES`.
 */
#define TOP_EARLGREY_SYSRST_CTRL_SIZE_BYTES 0x100u

/**
 * Peripheral base address for adc_ctrl in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_ADC_CTRL_BASE_ADDR 0x40440000u

/**
 * Peripheral size for adc_ctrl in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_ADC_CTRL_BASE_ADDR and
 * `TOP_EARLGREY_ADC_CTRL_BASE_ADDR + TOP_EARLGREY_ADC_CTRL_SIZE_BYTES`.
 */
#define TOP_EARLGREY_ADC_CTRL_SIZE_BYTES 0x80u

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
 * Peripheral base address for aon_timer in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_AON_TIMER_BASE_ADDR 0x40470000u

/**
 * Peripheral size for aon_timer in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_AON_TIMER_BASE_ADDR and
 * `TOP_EARLGREY_AON_TIMER_BASE_ADDR + TOP_EARLGREY_AON_TIMER_SIZE_BYTES`.
 */
#define TOP_EARLGREY_AON_TIMER_SIZE_BYTES 0x40u

/**
 * Peripheral base address for ast in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_AST_BASE_ADDR 0x40480000u

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
 * Peripheral base address for sensor_ctrl in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_SENSOR_CTRL_BASE_ADDR 0x40490000u

/**
 * Peripheral size for sensor_ctrl in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_SENSOR_CTRL_BASE_ADDR and
 * `TOP_EARLGREY_SENSOR_CTRL_BASE_ADDR + TOP_EARLGREY_SENSOR_CTRL_SIZE_BYTES`.
 */
#define TOP_EARLGREY_SENSOR_CTRL_SIZE_BYTES 0x80u

/**
 * Peripheral base address for regs device on sram_ctrl_ret in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_SRAM_CTRL_RET_REGS_BASE_ADDR 0x40500000u

/**
 * Peripheral size for regs device on sram_ctrl_ret in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_SRAM_CTRL_RET_REGS_BASE_ADDR and
 * `TOP_EARLGREY_SRAM_CTRL_RET_REGS_BASE_ADDR + TOP_EARLGREY_SRAM_CTRL_RET_REGS_SIZE_BYTES`.
 */
#define TOP_EARLGREY_SRAM_CTRL_RET_REGS_SIZE_BYTES 0x40u

/**
 * Peripheral base address for core device on rram_ctrl in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_RRAM_CTRL_CORE_BASE_ADDR 0x41010000u

/**
 * Peripheral size for core device on rram_ctrl in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_RRAM_CTRL_CORE_BASE_ADDR and
 * `TOP_EARLGREY_RRAM_CTRL_CORE_BASE_ADDR + TOP_EARLGREY_RRAM_CTRL_CORE_SIZE_BYTES`.
 */
#define TOP_EARLGREY_RRAM_CTRL_CORE_SIZE_BYTES 0x400u

/**
 * Peripheral base address for prim device on rram_macro in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_RRAM_MACRO_PRIM_BASE_ADDR 0x41018000u

/**
 * Peripheral size for prim device on rram_macro in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_RRAM_MACRO_PRIM_BASE_ADDR and
 * `TOP_EARLGREY_RRAM_MACRO_PRIM_BASE_ADDR + TOP_EARLGREY_RRAM_MACRO_PRIM_SIZE_BYTES`.
 */
#define TOP_EARLGREY_RRAM_MACRO_PRIM_SIZE_BYTES 0x10u

/**
 * Peripheral base address for regs device on rv_dm in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_RV_DM_REGS_BASE_ADDR 0x41200000u

/**
 * Peripheral size for regs device on rv_dm in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_RV_DM_REGS_BASE_ADDR and
 * `TOP_EARLGREY_RV_DM_REGS_BASE_ADDR + TOP_EARLGREY_RV_DM_REGS_SIZE_BYTES`.
 */
#define TOP_EARLGREY_RV_DM_REGS_SIZE_BYTES 0x10u

/**
 * Peripheral base address for mem device on rv_dm in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_RV_DM_MEM_BASE_ADDR 0x10000u

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
 * Peripheral base address for rv_plic in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_RV_PLIC_BASE_ADDR 0x48000000u

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
#define TOP_EARLGREY_AES_BASE_ADDR 0x41100000u

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
#define TOP_EARLGREY_HMAC_BASE_ADDR 0x41110000u

/**
 * Peripheral size for hmac in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_HMAC_BASE_ADDR and
 * `TOP_EARLGREY_HMAC_BASE_ADDR + TOP_EARLGREY_HMAC_SIZE_BYTES`.
 */
#define TOP_EARLGREY_HMAC_SIZE_BYTES 0x2000u

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
 * Peripheral base address for otbn in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_OTBN_BASE_ADDR 0x41130000u

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
 * Peripheral base address for keymgr_dpe in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_KEYMGR_DPE_BASE_ADDR 0x41140000u

/**
 * Peripheral size for keymgr_dpe in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_KEYMGR_DPE_BASE_ADDR and
 * `TOP_EARLGREY_KEYMGR_DPE_BASE_ADDR + TOP_EARLGREY_KEYMGR_DPE_SIZE_BYTES`.
 */
#define TOP_EARLGREY_KEYMGR_DPE_SIZE_BYTES 0x200u

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
#define TOP_EARLGREY_CSRNG_SIZE_BYTES 0x100u

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
#define TOP_EARLGREY_ENTROPY_SRC_SIZE_BYTES 0x100u

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
#define TOP_EARLGREY_EDN0_SIZE_BYTES 0x80u

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
#define TOP_EARLGREY_EDN1_SIZE_BYTES 0x80u

/**
 * Peripheral base address for regs device on sram_ctrl_main in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR 0x411C0000u

/**
 * Peripheral size for regs device on sram_ctrl_main in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR and
 * `TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR + TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_SIZE_BYTES`.
 */
#define TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_SIZE_BYTES 0x40u

/**
 * Peripheral base address for regs device on sram_ctrl_sec in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_SRAM_CTRL_SEC_REGS_BASE_ADDR 0x411D0000u

/**
 * Peripheral size for regs device on sram_ctrl_sec in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_SRAM_CTRL_SEC_REGS_BASE_ADDR and
 * `TOP_EARLGREY_SRAM_CTRL_SEC_REGS_BASE_ADDR + TOP_EARLGREY_SRAM_CTRL_SEC_REGS_SIZE_BYTES`.
 */
#define TOP_EARLGREY_SRAM_CTRL_SEC_REGS_SIZE_BYTES 0x40u

/**
 * Peripheral base address for regs device on rom_ctrl in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_ROM_CTRL_REGS_BASE_ADDR 0x411E0000u

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
 * Peripheral base address for cfg device on rv_core_ibex in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR 0x411F0000u

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
 * Peripheral base address for regs device on cheriot_mem_sys in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_CHERIOT_MEM_SYS_REGS_BASE_ADDR 0x411B0000u

/**
 * Peripheral size for regs device on cheriot_mem_sys in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_CHERIOT_MEM_SYS_REGS_BASE_ADDR and
 * `TOP_EARLGREY_CHERIOT_MEM_SYS_REGS_BASE_ADDR + TOP_EARLGREY_CHERIOT_MEM_SYS_REGS_SIZE_BYTES`.
 */
#define TOP_EARLGREY_CHERIOT_MEM_SYS_REGS_SIZE_BYTES 0x40u

/**
 * Peripheral base address for regs device on sram_ctrl_meta in top earlgrey.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_EARLGREY_SRAM_CTRL_META_REGS_BASE_ADDR 0x411A0000u

/**
 * Peripheral size for regs device on sram_ctrl_meta in top earlgrey.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_EARLGREY_SRAM_CTRL_META_REGS_BASE_ADDR and
 * `TOP_EARLGREY_SRAM_CTRL_META_REGS_BASE_ADDR + TOP_EARLGREY_SRAM_CTRL_META_REGS_SIZE_BYTES`.
 */
#define TOP_EARLGREY_SRAM_CTRL_META_REGS_SIZE_BYTES 0x40u


/**
 * Memory base address for ram memory on sram_ctrl_ret in top earlgrey.
 */
#define TOP_EARLGREY_SRAM_CTRL_RET_RAM_BASE_ADDR 0x40600000u

/**
 * Memory size for ram memory on sram_ctrl_ret in top earlgrey.
 */
#define TOP_EARLGREY_SRAM_CTRL_RET_RAM_SIZE_BYTES 0x2000u

/**
 * Memory base address for host memory on rram_ctrl in top earlgrey.
 */
#define TOP_EARLGREY_RRAM_CTRL_HOST_BASE_ADDR 0x30000000u

/**
 * Memory size for host memory on rram_ctrl in top earlgrey.
 */
#define TOP_EARLGREY_RRAM_CTRL_HOST_SIZE_BYTES 0x200000u

/**
 * Memory base address for ram memory on sram_ctrl_main in top earlgrey.
 */
#define TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_BASE_ADDR 0x10000000u

/**
 * Memory size for ram memory on sram_ctrl_main in top earlgrey.
 */
#define TOP_EARLGREY_SRAM_CTRL_MAIN_RAM_SIZE_BYTES 0x20000u

/**
 * Memory base address for ram memory on sram_ctrl_sec in top earlgrey.
 */
#define TOP_EARLGREY_SRAM_CTRL_SEC_RAM_BASE_ADDR 0x10020000u

/**
 * Memory size for ram memory on sram_ctrl_sec in top earlgrey.
 */
#define TOP_EARLGREY_SRAM_CTRL_SEC_RAM_SIZE_BYTES 0x10000u

/**
 * Memory base address for rom memory on rom_ctrl in top earlgrey.
 */
#define TOP_EARLGREY_ROM_CTRL_ROM_BASE_ADDR 0x40000u

/**
 * Memory size for rom memory on rom_ctrl in top earlgrey.
 */
#define TOP_EARLGREY_ROM_CTRL_ROM_SIZE_BYTES 0x30000u

/**
 * Memory base address for revbm memory on cheriot_mem_sys in top earlgrey.
 */
#define TOP_EARLGREY_CHERIOT_MEM_SYS_REVBM_BASE_ADDR 0x11000000u

/**
 * Memory size for revbm memory on cheriot_mem_sys in top earlgrey.
 */
#define TOP_EARLGREY_CHERIOT_MEM_SYS_REVBM_SIZE_BYTES 0xC00u

/**
 * Memory base address for ram memory on sram_ctrl_meta in top earlgrey.
 */
#define TOP_EARLGREY_SRAM_CTRL_META_RAM_BASE_ADDR 0x11000000u

/**
 * Memory size for ram memory on sram_ctrl_meta in top earlgrey.
 */
#define TOP_EARLGREY_SRAM_CTRL_META_RAM_SIZE_BYTES 0x9800u


/**
 * PLIC Interrupt Source Peripheral.
 *
 * Enumeration used to determine which peripheral asserted the corresponding
 * interrupt.
 */
typedef enum top_earlgrey_plic_peripheral {
  kTopEarlgreyPlicPeripheralUnknown = 0, /**< Unknown Peripheral */
  kTopEarlgreyPlicPeripheralUart0 = 1, /**< uart0 */
  kTopEarlgreyPlicPeripheralUart1 = 2, /**< uart1 */
  kTopEarlgreyPlicPeripheralUart2 = 3, /**< uart2 */
  kTopEarlgreyPlicPeripheralUart3 = 4, /**< uart3 */
  kTopEarlgreyPlicPeripheralGpio0 = 5, /**< gpio0 */
  kTopEarlgreyPlicPeripheralGpio1 = 6, /**< gpio1 */
  kTopEarlgreyPlicPeripheralSpiDevice = 7, /**< spi_device */
  kTopEarlgreyPlicPeripheralI2c0 = 8, /**< i2c0 */
  kTopEarlgreyPlicPeripheralI2c1 = 9, /**< i2c1 */
  kTopEarlgreyPlicPeripheralI2c2 = 10, /**< i2c2 */
  kTopEarlgreyPlicPeripheralI3c0 = 11, /**< i3c0 */
  kTopEarlgreyPlicPeripheralI3c1 = 12, /**< i3c1 */
  kTopEarlgreyPlicPeripheralRvTimer = 13, /**< rv_timer */
  kTopEarlgreyPlicPeripheralOtpCtrl = 14, /**< otp_ctrl */
  kTopEarlgreyPlicPeripheralAlertHandler = 15, /**< alert_handler */
  kTopEarlgreyPlicPeripheralSpiHost0 = 16, /**< spi_host0 */
  kTopEarlgreyPlicPeripheralSpiHost1 = 17, /**< spi_host1 */
  kTopEarlgreyPlicPeripheralUsbdev = 18, /**< usbdev */
  kTopEarlgreyPlicPeripheralPwrmgr = 19, /**< pwrmgr */
  kTopEarlgreyPlicPeripheralSysrstCtrl = 20, /**< sysrst_ctrl */
  kTopEarlgreyPlicPeripheralAdcCtrl = 21, /**< adc_ctrl */
  kTopEarlgreyPlicPeripheralAonTimer = 22, /**< aon_timer */
  kTopEarlgreyPlicPeripheralSensorCtrl = 23, /**< sensor_ctrl */
  kTopEarlgreyPlicPeripheralRramCtrl = 24, /**< rram_ctrl */
  kTopEarlgreyPlicPeripheralHmac = 25, /**< hmac */
  kTopEarlgreyPlicPeripheralKmac = 26, /**< kmac */
  kTopEarlgreyPlicPeripheralOtbn = 27, /**< otbn */
  kTopEarlgreyPlicPeripheralKeymgrDpe = 28, /**< keymgr_dpe */
  kTopEarlgreyPlicPeripheralCsrng = 29, /**< csrng */
  kTopEarlgreyPlicPeripheralEntropySrc = 30, /**< entropy_src */
  kTopEarlgreyPlicPeripheralEdn0 = 31, /**< edn0 */
  kTopEarlgreyPlicPeripheralEdn1 = 32, /**< edn1 */
  kTopEarlgreyPlicPeripheralCheriotMemSys = 33, /**< cheriot_mem_sys */
  kTopEarlgreyPlicPeripheralLast = 33, /**< \internal Final PLIC peripheral */
} top_earlgrey_plic_peripheral_t;

/**
 * PLIC Interrupt Source.
 *
 * Enumeration of all PLIC interrupt sources. The interrupt sources belonging to
 * the same peripheral are guaranteed to be consecutive.
 */
typedef enum top_earlgrey_plic_irq_id {
  kTopEarlgreyPlicIrqIdNone = 0, /**< No Interrupt */
  kTopEarlgreyPlicIrqIdUart0TxWatermark = 1, /**< uart0_tx_watermark */
  kTopEarlgreyPlicIrqIdUart0RxWatermark = 2, /**< uart0_rx_watermark */
  kTopEarlgreyPlicIrqIdUart0TxDone = 3, /**< uart0_tx_done */
  kTopEarlgreyPlicIrqIdUart0RxOverflow = 4, /**< uart0_rx_overflow */
  kTopEarlgreyPlicIrqIdUart0RxFrameErr = 5, /**< uart0_rx_frame_err */
  kTopEarlgreyPlicIrqIdUart0RxBreakErr = 6, /**< uart0_rx_break_err */
  kTopEarlgreyPlicIrqIdUart0RxTimeout = 7, /**< uart0_rx_timeout */
  kTopEarlgreyPlicIrqIdUart0RxParityErr = 8, /**< uart0_rx_parity_err */
  kTopEarlgreyPlicIrqIdUart0TxEmpty = 9, /**< uart0_tx_empty */
  kTopEarlgreyPlicIrqIdUart1TxWatermark = 10, /**< uart1_tx_watermark */
  kTopEarlgreyPlicIrqIdUart1RxWatermark = 11, /**< uart1_rx_watermark */
  kTopEarlgreyPlicIrqIdUart1TxDone = 12, /**< uart1_tx_done */
  kTopEarlgreyPlicIrqIdUart1RxOverflow = 13, /**< uart1_rx_overflow */
  kTopEarlgreyPlicIrqIdUart1RxFrameErr = 14, /**< uart1_rx_frame_err */
  kTopEarlgreyPlicIrqIdUart1RxBreakErr = 15, /**< uart1_rx_break_err */
  kTopEarlgreyPlicIrqIdUart1RxTimeout = 16, /**< uart1_rx_timeout */
  kTopEarlgreyPlicIrqIdUart1RxParityErr = 17, /**< uart1_rx_parity_err */
  kTopEarlgreyPlicIrqIdUart1TxEmpty = 18, /**< uart1_tx_empty */
  kTopEarlgreyPlicIrqIdUart2TxWatermark = 19, /**< uart2_tx_watermark */
  kTopEarlgreyPlicIrqIdUart2RxWatermark = 20, /**< uart2_rx_watermark */
  kTopEarlgreyPlicIrqIdUart2TxDone = 21, /**< uart2_tx_done */
  kTopEarlgreyPlicIrqIdUart2RxOverflow = 22, /**< uart2_rx_overflow */
  kTopEarlgreyPlicIrqIdUart2RxFrameErr = 23, /**< uart2_rx_frame_err */
  kTopEarlgreyPlicIrqIdUart2RxBreakErr = 24, /**< uart2_rx_break_err */
  kTopEarlgreyPlicIrqIdUart2RxTimeout = 25, /**< uart2_rx_timeout */
  kTopEarlgreyPlicIrqIdUart2RxParityErr = 26, /**< uart2_rx_parity_err */
  kTopEarlgreyPlicIrqIdUart2TxEmpty = 27, /**< uart2_tx_empty */
  kTopEarlgreyPlicIrqIdUart3TxWatermark = 28, /**< uart3_tx_watermark */
  kTopEarlgreyPlicIrqIdUart3RxWatermark = 29, /**< uart3_rx_watermark */
  kTopEarlgreyPlicIrqIdUart3TxDone = 30, /**< uart3_tx_done */
  kTopEarlgreyPlicIrqIdUart3RxOverflow = 31, /**< uart3_rx_overflow */
  kTopEarlgreyPlicIrqIdUart3RxFrameErr = 32, /**< uart3_rx_frame_err */
  kTopEarlgreyPlicIrqIdUart3RxBreakErr = 33, /**< uart3_rx_break_err */
  kTopEarlgreyPlicIrqIdUart3RxTimeout = 34, /**< uart3_rx_timeout */
  kTopEarlgreyPlicIrqIdUart3RxParityErr = 35, /**< uart3_rx_parity_err */
  kTopEarlgreyPlicIrqIdUart3TxEmpty = 36, /**< uart3_tx_empty */
  kTopEarlgreyPlicIrqIdGpio0Gpio0 = 37, /**< gpio0_gpio 0 */
  kTopEarlgreyPlicIrqIdGpio0Gpio1 = 38, /**< gpio0_gpio 1 */
  kTopEarlgreyPlicIrqIdGpio0Gpio2 = 39, /**< gpio0_gpio 2 */
  kTopEarlgreyPlicIrqIdGpio0Gpio3 = 40, /**< gpio0_gpio 3 */
  kTopEarlgreyPlicIrqIdGpio0Gpio4 = 41, /**< gpio0_gpio 4 */
  kTopEarlgreyPlicIrqIdGpio0Gpio5 = 42, /**< gpio0_gpio 5 */
  kTopEarlgreyPlicIrqIdGpio0Gpio6 = 43, /**< gpio0_gpio 6 */
  kTopEarlgreyPlicIrqIdGpio0Gpio7 = 44, /**< gpio0_gpio 7 */
  kTopEarlgreyPlicIrqIdGpio0Gpio8 = 45, /**< gpio0_gpio 8 */
  kTopEarlgreyPlicIrqIdGpio0Gpio9 = 46, /**< gpio0_gpio 9 */
  kTopEarlgreyPlicIrqIdGpio0Gpio10 = 47, /**< gpio0_gpio 10 */
  kTopEarlgreyPlicIrqIdGpio0Gpio11 = 48, /**< gpio0_gpio 11 */
  kTopEarlgreyPlicIrqIdGpio0Gpio12 = 49, /**< gpio0_gpio 12 */
  kTopEarlgreyPlicIrqIdGpio0Gpio13 = 50, /**< gpio0_gpio 13 */
  kTopEarlgreyPlicIrqIdGpio0Gpio14 = 51, /**< gpio0_gpio 14 */
  kTopEarlgreyPlicIrqIdGpio0Gpio15 = 52, /**< gpio0_gpio 15 */
  kTopEarlgreyPlicIrqIdGpio0Gpio16 = 53, /**< gpio0_gpio 16 */
  kTopEarlgreyPlicIrqIdGpio0Gpio17 = 54, /**< gpio0_gpio 17 */
  kTopEarlgreyPlicIrqIdGpio0Gpio18 = 55, /**< gpio0_gpio 18 */
  kTopEarlgreyPlicIrqIdGpio0Gpio19 = 56, /**< gpio0_gpio 19 */
  kTopEarlgreyPlicIrqIdGpio0Gpio20 = 57, /**< gpio0_gpio 20 */
  kTopEarlgreyPlicIrqIdGpio0Gpio21 = 58, /**< gpio0_gpio 21 */
  kTopEarlgreyPlicIrqIdGpio0Gpio22 = 59, /**< gpio0_gpio 22 */
  kTopEarlgreyPlicIrqIdGpio0Gpio23 = 60, /**< gpio0_gpio 23 */
  kTopEarlgreyPlicIrqIdGpio0Gpio24 = 61, /**< gpio0_gpio 24 */
  kTopEarlgreyPlicIrqIdGpio0Gpio25 = 62, /**< gpio0_gpio 25 */
  kTopEarlgreyPlicIrqIdGpio0Gpio26 = 63, /**< gpio0_gpio 26 */
  kTopEarlgreyPlicIrqIdGpio0Gpio27 = 64, /**< gpio0_gpio 27 */
  kTopEarlgreyPlicIrqIdGpio0Gpio28 = 65, /**< gpio0_gpio 28 */
  kTopEarlgreyPlicIrqIdGpio0Gpio29 = 66, /**< gpio0_gpio 29 */
  kTopEarlgreyPlicIrqIdGpio0Gpio30 = 67, /**< gpio0_gpio 30 */
  kTopEarlgreyPlicIrqIdGpio0Gpio31 = 68, /**< gpio0_gpio 31 */
  kTopEarlgreyPlicIrqIdGpio1Gpio0 = 69, /**< gpio1_gpio 0 */
  kTopEarlgreyPlicIrqIdGpio1Gpio1 = 70, /**< gpio1_gpio 1 */
  kTopEarlgreyPlicIrqIdGpio1Gpio2 = 71, /**< gpio1_gpio 2 */
  kTopEarlgreyPlicIrqIdGpio1Gpio3 = 72, /**< gpio1_gpio 3 */
  kTopEarlgreyPlicIrqIdGpio1Gpio4 = 73, /**< gpio1_gpio 4 */
  kTopEarlgreyPlicIrqIdGpio1Gpio5 = 74, /**< gpio1_gpio 5 */
  kTopEarlgreyPlicIrqIdGpio1Gpio6 = 75, /**< gpio1_gpio 6 */
  kTopEarlgreyPlicIrqIdGpio1Gpio7 = 76, /**< gpio1_gpio 7 */
  kTopEarlgreyPlicIrqIdGpio1Gpio8 = 77, /**< gpio1_gpio 8 */
  kTopEarlgreyPlicIrqIdGpio1Gpio9 = 78, /**< gpio1_gpio 9 */
  kTopEarlgreyPlicIrqIdGpio1Gpio10 = 79, /**< gpio1_gpio 10 */
  kTopEarlgreyPlicIrqIdGpio1Gpio11 = 80, /**< gpio1_gpio 11 */
  kTopEarlgreyPlicIrqIdGpio1Gpio12 = 81, /**< gpio1_gpio 12 */
  kTopEarlgreyPlicIrqIdGpio1Gpio13 = 82, /**< gpio1_gpio 13 */
  kTopEarlgreyPlicIrqIdGpio1Gpio14 = 83, /**< gpio1_gpio 14 */
  kTopEarlgreyPlicIrqIdGpio1Gpio15 = 84, /**< gpio1_gpio 15 */
  kTopEarlgreyPlicIrqIdGpio1Gpio16 = 85, /**< gpio1_gpio 16 */
  kTopEarlgreyPlicIrqIdGpio1Gpio17 = 86, /**< gpio1_gpio 17 */
  kTopEarlgreyPlicIrqIdGpio1Gpio18 = 87, /**< gpio1_gpio 18 */
  kTopEarlgreyPlicIrqIdGpio1Gpio19 = 88, /**< gpio1_gpio 19 */
  kTopEarlgreyPlicIrqIdGpio1Gpio20 = 89, /**< gpio1_gpio 20 */
  kTopEarlgreyPlicIrqIdGpio1Gpio21 = 90, /**< gpio1_gpio 21 */
  kTopEarlgreyPlicIrqIdGpio1Gpio22 = 91, /**< gpio1_gpio 22 */
  kTopEarlgreyPlicIrqIdGpio1Gpio23 = 92, /**< gpio1_gpio 23 */
  kTopEarlgreyPlicIrqIdGpio1Gpio24 = 93, /**< gpio1_gpio 24 */
  kTopEarlgreyPlicIrqIdGpio1Gpio25 = 94, /**< gpio1_gpio 25 */
  kTopEarlgreyPlicIrqIdGpio1Gpio26 = 95, /**< gpio1_gpio 26 */
  kTopEarlgreyPlicIrqIdGpio1Gpio27 = 96, /**< gpio1_gpio 27 */
  kTopEarlgreyPlicIrqIdGpio1Gpio28 = 97, /**< gpio1_gpio 28 */
  kTopEarlgreyPlicIrqIdGpio1Gpio29 = 98, /**< gpio1_gpio 29 */
  kTopEarlgreyPlicIrqIdGpio1Gpio30 = 99, /**< gpio1_gpio 30 */
  kTopEarlgreyPlicIrqIdGpio1Gpio31 = 100, /**< gpio1_gpio 31 */
  kTopEarlgreyPlicIrqIdSpiDeviceUploadCmdfifoNotEmpty = 101, /**< spi_device_upload_cmdfifo_not_empty */
  kTopEarlgreyPlicIrqIdSpiDeviceUploadPayloadNotEmpty = 102, /**< spi_device_upload_payload_not_empty */
  kTopEarlgreyPlicIrqIdSpiDeviceUploadPayloadOverflow = 103, /**< spi_device_upload_payload_overflow */
  kTopEarlgreyPlicIrqIdSpiDeviceReadbufWatermark = 104, /**< spi_device_readbuf_watermark */
  kTopEarlgreyPlicIrqIdSpiDeviceReadbufFlip = 105, /**< spi_device_readbuf_flip */
  kTopEarlgreyPlicIrqIdSpiDeviceTpmHeaderNotEmpty = 106, /**< spi_device_tpm_header_not_empty */
  kTopEarlgreyPlicIrqIdSpiDeviceTpmRdfifoCmdEnd = 107, /**< spi_device_tpm_rdfifo_cmd_end */
  kTopEarlgreyPlicIrqIdSpiDeviceTpmRdfifoDrop = 108, /**< spi_device_tpm_rdfifo_drop */
  kTopEarlgreyPlicIrqIdI2c0FmtThreshold = 109, /**< i2c0_fmt_threshold */
  kTopEarlgreyPlicIrqIdI2c0RxThreshold = 110, /**< i2c0_rx_threshold */
  kTopEarlgreyPlicIrqIdI2c0AcqThreshold = 111, /**< i2c0_acq_threshold */
  kTopEarlgreyPlicIrqIdI2c0RxOverflow = 112, /**< i2c0_rx_overflow */
  kTopEarlgreyPlicIrqIdI2c0ControllerHalt = 113, /**< i2c0_controller_halt */
  kTopEarlgreyPlicIrqIdI2c0SclInterference = 114, /**< i2c0_scl_interference */
  kTopEarlgreyPlicIrqIdI2c0SdaInterference = 115, /**< i2c0_sda_interference */
  kTopEarlgreyPlicIrqIdI2c0StretchTimeout = 116, /**< i2c0_stretch_timeout */
  kTopEarlgreyPlicIrqIdI2c0SdaUnstable = 117, /**< i2c0_sda_unstable */
  kTopEarlgreyPlicIrqIdI2c0CmdComplete = 118, /**< i2c0_cmd_complete */
  kTopEarlgreyPlicIrqIdI2c0TxStretch = 119, /**< i2c0_tx_stretch */
  kTopEarlgreyPlicIrqIdI2c0TxThreshold = 120, /**< i2c0_tx_threshold */
  kTopEarlgreyPlicIrqIdI2c0AcqStretch = 121, /**< i2c0_acq_stretch */
  kTopEarlgreyPlicIrqIdI2c0UnexpStop = 122, /**< i2c0_unexp_stop */
  kTopEarlgreyPlicIrqIdI2c0HostTimeout = 123, /**< i2c0_host_timeout */
  kTopEarlgreyPlicIrqIdI2c1FmtThreshold = 124, /**< i2c1_fmt_threshold */
  kTopEarlgreyPlicIrqIdI2c1RxThreshold = 125, /**< i2c1_rx_threshold */
  kTopEarlgreyPlicIrqIdI2c1AcqThreshold = 126, /**< i2c1_acq_threshold */
  kTopEarlgreyPlicIrqIdI2c1RxOverflow = 127, /**< i2c1_rx_overflow */
  kTopEarlgreyPlicIrqIdI2c1ControllerHalt = 128, /**< i2c1_controller_halt */
  kTopEarlgreyPlicIrqIdI2c1SclInterference = 129, /**< i2c1_scl_interference */
  kTopEarlgreyPlicIrqIdI2c1SdaInterference = 130, /**< i2c1_sda_interference */
  kTopEarlgreyPlicIrqIdI2c1StretchTimeout = 131, /**< i2c1_stretch_timeout */
  kTopEarlgreyPlicIrqIdI2c1SdaUnstable = 132, /**< i2c1_sda_unstable */
  kTopEarlgreyPlicIrqIdI2c1CmdComplete = 133, /**< i2c1_cmd_complete */
  kTopEarlgreyPlicIrqIdI2c1TxStretch = 134, /**< i2c1_tx_stretch */
  kTopEarlgreyPlicIrqIdI2c1TxThreshold = 135, /**< i2c1_tx_threshold */
  kTopEarlgreyPlicIrqIdI2c1AcqStretch = 136, /**< i2c1_acq_stretch */
  kTopEarlgreyPlicIrqIdI2c1UnexpStop = 137, /**< i2c1_unexp_stop */
  kTopEarlgreyPlicIrqIdI2c1HostTimeout = 138, /**< i2c1_host_timeout */
  kTopEarlgreyPlicIrqIdI2c2FmtThreshold = 139, /**< i2c2_fmt_threshold */
  kTopEarlgreyPlicIrqIdI2c2RxThreshold = 140, /**< i2c2_rx_threshold */
  kTopEarlgreyPlicIrqIdI2c2AcqThreshold = 141, /**< i2c2_acq_threshold */
  kTopEarlgreyPlicIrqIdI2c2RxOverflow = 142, /**< i2c2_rx_overflow */
  kTopEarlgreyPlicIrqIdI2c2ControllerHalt = 143, /**< i2c2_controller_halt */
  kTopEarlgreyPlicIrqIdI2c2SclInterference = 144, /**< i2c2_scl_interference */
  kTopEarlgreyPlicIrqIdI2c2SdaInterference = 145, /**< i2c2_sda_interference */
  kTopEarlgreyPlicIrqIdI2c2StretchTimeout = 146, /**< i2c2_stretch_timeout */
  kTopEarlgreyPlicIrqIdI2c2SdaUnstable = 147, /**< i2c2_sda_unstable */
  kTopEarlgreyPlicIrqIdI2c2CmdComplete = 148, /**< i2c2_cmd_complete */
  kTopEarlgreyPlicIrqIdI2c2TxStretch = 149, /**< i2c2_tx_stretch */
  kTopEarlgreyPlicIrqIdI2c2TxThreshold = 150, /**< i2c2_tx_threshold */
  kTopEarlgreyPlicIrqIdI2c2AcqStretch = 151, /**< i2c2_acq_stretch */
  kTopEarlgreyPlicIrqIdI2c2UnexpStop = 152, /**< i2c2_unexp_stop */
  kTopEarlgreyPlicIrqIdI2c2HostTimeout = 153, /**< i2c2_host_timeout */
  kTopEarlgreyPlicIrqIdI3c0Hci = 154, /**< i3c0_hci */
  kTopEarlgreyPlicIrqIdI3c0Targ = 155, /**< i3c0_targ */
  kTopEarlgreyPlicIrqIdI3c1Hci = 156, /**< i3c1_hci */
  kTopEarlgreyPlicIrqIdI3c1Targ = 157, /**< i3c1_targ */
  kTopEarlgreyPlicIrqIdRvTimerTimerExpiredHart0Timer0 = 158, /**< rv_timer_timer_expired_hart0_timer0 */
  kTopEarlgreyPlicIrqIdOtpCtrlOtpOperationDone = 159, /**< otp_ctrl_otp_operation_done */
  kTopEarlgreyPlicIrqIdOtpCtrlOtpError = 160, /**< otp_ctrl_otp_error */
  kTopEarlgreyPlicIrqIdAlertHandlerClassa = 161, /**< alert_handler_classa */
  kTopEarlgreyPlicIrqIdAlertHandlerClassb = 162, /**< alert_handler_classb */
  kTopEarlgreyPlicIrqIdAlertHandlerClassc = 163, /**< alert_handler_classc */
  kTopEarlgreyPlicIrqIdAlertHandlerClassd = 164, /**< alert_handler_classd */
  kTopEarlgreyPlicIrqIdSpiHost0Error = 165, /**< spi_host0_error */
  kTopEarlgreyPlicIrqIdSpiHost0SpiEvent = 166, /**< spi_host0_spi_event */
  kTopEarlgreyPlicIrqIdSpiHost1Error = 167, /**< spi_host1_error */
  kTopEarlgreyPlicIrqIdSpiHost1SpiEvent = 168, /**< spi_host1_spi_event */
  kTopEarlgreyPlicIrqIdUsbdevPktReceived = 169, /**< usbdev_pkt_received */
  kTopEarlgreyPlicIrqIdUsbdevPktSent = 170, /**< usbdev_pkt_sent */
  kTopEarlgreyPlicIrqIdUsbdevDisconnected = 171, /**< usbdev_disconnected */
  kTopEarlgreyPlicIrqIdUsbdevHostLost = 172, /**< usbdev_host_lost */
  kTopEarlgreyPlicIrqIdUsbdevLinkReset = 173, /**< usbdev_link_reset */
  kTopEarlgreyPlicIrqIdUsbdevLinkSuspend = 174, /**< usbdev_link_suspend */
  kTopEarlgreyPlicIrqIdUsbdevLinkResume = 175, /**< usbdev_link_resume */
  kTopEarlgreyPlicIrqIdUsbdevAvOutEmpty = 176, /**< usbdev_av_out_empty */
  kTopEarlgreyPlicIrqIdUsbdevRxFull = 177, /**< usbdev_rx_full */
  kTopEarlgreyPlicIrqIdUsbdevAvOverflow = 178, /**< usbdev_av_overflow */
  kTopEarlgreyPlicIrqIdUsbdevLinkInErr = 179, /**< usbdev_link_in_err */
  kTopEarlgreyPlicIrqIdUsbdevRxCrcErr = 180, /**< usbdev_rx_crc_err */
  kTopEarlgreyPlicIrqIdUsbdevRxPidErr = 181, /**< usbdev_rx_pid_err */
  kTopEarlgreyPlicIrqIdUsbdevRxBitstuffErr = 182, /**< usbdev_rx_bitstuff_err */
  kTopEarlgreyPlicIrqIdUsbdevFrame = 183, /**< usbdev_frame */
  kTopEarlgreyPlicIrqIdUsbdevPowered = 184, /**< usbdev_powered */
  kTopEarlgreyPlicIrqIdUsbdevLinkOutErr = 185, /**< usbdev_link_out_err */
  kTopEarlgreyPlicIrqIdUsbdevAvSetupEmpty = 186, /**< usbdev_av_setup_empty */
  kTopEarlgreyPlicIrqIdPwrmgrWakeup = 187, /**< pwrmgr_wakeup */
  kTopEarlgreyPlicIrqIdSysrstCtrlEventDetected = 188, /**< sysrst_ctrl_event_detected */
  kTopEarlgreyPlicIrqIdAdcCtrlMatchPending = 189, /**< adc_ctrl_match_pending */
  kTopEarlgreyPlicIrqIdAonTimerWkupTimerExpired = 190, /**< aon_timer_wkup_timer_expired */
  kTopEarlgreyPlicIrqIdAonTimerWdogTimerBark = 191, /**< aon_timer_wdog_timer_bark */
  kTopEarlgreyPlicIrqIdSensorCtrlIoStatusChange = 192, /**< sensor_ctrl_io_status_change */
  kTopEarlgreyPlicIrqIdSensorCtrlInitStatusChange = 193, /**< sensor_ctrl_init_status_change */
  kTopEarlgreyPlicIrqIdRramCtrlWrEmpty = 194, /**< rram_ctrl_wr_empty */
  kTopEarlgreyPlicIrqIdRramCtrlWrLvl = 195, /**< rram_ctrl_wr_lvl */
  kTopEarlgreyPlicIrqIdRramCtrlRdFull = 196, /**< rram_ctrl_rd_full */
  kTopEarlgreyPlicIrqIdRramCtrlRdLvl = 197, /**< rram_ctrl_rd_lvl */
  kTopEarlgreyPlicIrqIdRramCtrlOpDone = 198, /**< rram_ctrl_op_done */
  kTopEarlgreyPlicIrqIdRramCtrlCorr1Err = 199, /**< rram_ctrl_corr1_err */
  kTopEarlgreyPlicIrqIdRramCtrlCorr2Err = 200, /**< rram_ctrl_corr2_err */
  kTopEarlgreyPlicIrqIdHmacHmacDone = 201, /**< hmac_hmac_done */
  kTopEarlgreyPlicIrqIdHmacFifoEmpty = 202, /**< hmac_fifo_empty */
  kTopEarlgreyPlicIrqIdHmacHmacErr = 203, /**< hmac_hmac_err */
  kTopEarlgreyPlicIrqIdKmacKmacDone = 204, /**< kmac_kmac_done */
  kTopEarlgreyPlicIrqIdKmacFifoEmpty = 205, /**< kmac_fifo_empty */
  kTopEarlgreyPlicIrqIdKmacKmacErr = 206, /**< kmac_kmac_err */
  kTopEarlgreyPlicIrqIdOtbnDone = 207, /**< otbn_done */
  kTopEarlgreyPlicIrqIdKeymgrDpeOpDone = 208, /**< keymgr_dpe_op_done */
  kTopEarlgreyPlicIrqIdCsrngCsCmdReqDone = 209, /**< csrng_cs_cmd_req_done */
  kTopEarlgreyPlicIrqIdCsrngCsEntropyReq = 210, /**< csrng_cs_entropy_req */
  kTopEarlgreyPlicIrqIdCsrngCsHwInstExc = 211, /**< csrng_cs_hw_inst_exc */
  kTopEarlgreyPlicIrqIdCsrngCsFatalErr = 212, /**< csrng_cs_fatal_err */
  kTopEarlgreyPlicIrqIdEntropySrcEsEntropyValid = 213, /**< entropy_src_es_entropy_valid */
  kTopEarlgreyPlicIrqIdEntropySrcEsHealthTestFailed = 214, /**< entropy_src_es_health_test_failed */
  kTopEarlgreyPlicIrqIdEntropySrcEsObserveFifoReady = 215, /**< entropy_src_es_observe_fifo_ready */
  kTopEarlgreyPlicIrqIdEntropySrcEsFatalErr = 216, /**< entropy_src_es_fatal_err */
  kTopEarlgreyPlicIrqIdEdn0EdnCmdReqDone = 217, /**< edn0_edn_cmd_req_done */
  kTopEarlgreyPlicIrqIdEdn0EdnFatalErr = 218, /**< edn0_edn_fatal_err */
  kTopEarlgreyPlicIrqIdEdn1EdnCmdReqDone = 219, /**< edn1_edn_cmd_req_done */
  kTopEarlgreyPlicIrqIdEdn1EdnFatalErr = 220, /**< edn1_edn_fatal_err */
  kTopEarlgreyPlicIrqIdCheriotMemSysTbreDone = 221, /**< cheriot_mem_sys_tbre_done */
  kTopEarlgreyPlicIrqIdLast = 221, /**< \internal The Last Valid Interrupt ID. */
} top_earlgrey_plic_irq_id_t;

/**
 * PLIC Interrupt Source to Peripheral Map
 *
 * This array is a mapping from `top_earlgrey_plic_irq_id_t` to
 * `top_earlgrey_plic_peripheral_t`.
 */
extern const top_earlgrey_plic_peripheral_t
    top_earlgrey_plic_interrupt_for_peripheral[222];

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
  kTopEarlgreyAlertPeripheralExternal = 0, /**< External Peripheral */
  kTopEarlgreyAlertPeripheralUart0 = 1, /**< uart0 */
  kTopEarlgreyAlertPeripheralUart1 = 2, /**< uart1 */
  kTopEarlgreyAlertPeripheralUart2 = 3, /**< uart2 */
  kTopEarlgreyAlertPeripheralUart3 = 4, /**< uart3 */
  kTopEarlgreyAlertPeripheralGpio0 = 5, /**< gpio0 */
  kTopEarlgreyAlertPeripheralGpio1 = 6, /**< gpio1 */
  kTopEarlgreyAlertPeripheralSpiDevice = 7, /**< spi_device */
  kTopEarlgreyAlertPeripheralI2c0 = 8, /**< i2c0 */
  kTopEarlgreyAlertPeripheralI2c1 = 9, /**< i2c1 */
  kTopEarlgreyAlertPeripheralI2c2 = 10, /**< i2c2 */
  kTopEarlgreyAlertPeripheralI3c0 = 11, /**< i3c0 */
  kTopEarlgreyAlertPeripheralI3c1 = 12, /**< i3c1 */
  kTopEarlgreyAlertPeripheralRvTimer = 13, /**< rv_timer */
  kTopEarlgreyAlertPeripheralOtpCtrl = 14, /**< otp_ctrl */
  kTopEarlgreyAlertPeripheralLcCtrl = 15, /**< lc_ctrl */
  kTopEarlgreyAlertPeripheralSpiHost0 = 16, /**< spi_host0 */
  kTopEarlgreyAlertPeripheralSpiHost1 = 17, /**< spi_host1 */
  kTopEarlgreyAlertPeripheralUsbdev = 18, /**< usbdev */
  kTopEarlgreyAlertPeripheralPwrmgr = 19, /**< pwrmgr */
  kTopEarlgreyAlertPeripheralRstmgr = 20, /**< rstmgr */
  kTopEarlgreyAlertPeripheralClkmgr = 21, /**< clkmgr */
  kTopEarlgreyAlertPeripheralSysrstCtrl = 22, /**< sysrst_ctrl */
  kTopEarlgreyAlertPeripheralAdcCtrl = 23, /**< adc_ctrl */
  kTopEarlgreyAlertPeripheralPinmux = 24, /**< pinmux */
  kTopEarlgreyAlertPeripheralAonTimer = 25, /**< aon_timer */
  kTopEarlgreyAlertPeripheralSensorCtrl = 26, /**< sensor_ctrl */
  kTopEarlgreyAlertPeripheralSramCtrlRet = 27, /**< sram_ctrl_ret */
  kTopEarlgreyAlertPeripheralRramCtrl = 28, /**< rram_ctrl */
  kTopEarlgreyAlertPeripheralRvDm = 29, /**< rv_dm */
  kTopEarlgreyAlertPeripheralRvPlic = 30, /**< rv_plic */
  kTopEarlgreyAlertPeripheralAes = 31, /**< aes */
  kTopEarlgreyAlertPeripheralHmac = 32, /**< hmac */
  kTopEarlgreyAlertPeripheralKmac = 33, /**< kmac */
  kTopEarlgreyAlertPeripheralOtbn = 34, /**< otbn */
  kTopEarlgreyAlertPeripheralKeymgrDpe = 35, /**< keymgr_dpe */
  kTopEarlgreyAlertPeripheralCsrng = 36, /**< csrng */
  kTopEarlgreyAlertPeripheralEntropySrc = 37, /**< entropy_src */
  kTopEarlgreyAlertPeripheralEdn0 = 38, /**< edn0 */
  kTopEarlgreyAlertPeripheralEdn1 = 39, /**< edn1 */
  kTopEarlgreyAlertPeripheralSramCtrlMain = 40, /**< sram_ctrl_main */
  kTopEarlgreyAlertPeripheralSramCtrlSec = 41, /**< sram_ctrl_sec */
  kTopEarlgreyAlertPeripheralRomCtrl = 42, /**< rom_ctrl */
  kTopEarlgreyAlertPeripheralRvCoreIbex = 43, /**< rv_core_ibex */
  kTopEarlgreyAlertPeripheralCheriotMemSys = 44, /**< cheriot_mem_sys */
  kTopEarlgreyAlertPeripheralSramCtrlMeta = 45, /**< sram_ctrl_meta */
  kTopEarlgreyAlertPeripheralLast = 45, /**< \internal Final Alert peripheral */
} top_earlgrey_alert_peripheral_t;

/**
 * Alert Handler Alert Source.
 *
 * Enumeration of all Alert Handler Alert Sources. The alert sources belonging to
 * the same peripheral are guaranteed to be consecutive.
 */
typedef enum top_earlgrey_alert_id {
  kTopEarlgreyAlertIdUart0FatalFault = 0, /**< uart0_fatal_fault */
  kTopEarlgreyAlertIdUart1FatalFault = 1, /**< uart1_fatal_fault */
  kTopEarlgreyAlertIdUart2FatalFault = 2, /**< uart2_fatal_fault */
  kTopEarlgreyAlertIdUart3FatalFault = 3, /**< uart3_fatal_fault */
  kTopEarlgreyAlertIdGpio0FatalFault = 4, /**< gpio0_fatal_fault */
  kTopEarlgreyAlertIdGpio1FatalFault = 5, /**< gpio1_fatal_fault */
  kTopEarlgreyAlertIdSpiDeviceFatalFault = 6, /**< spi_device_fatal_fault */
  kTopEarlgreyAlertIdI2c0FatalFault = 7, /**< i2c0_fatal_fault */
  kTopEarlgreyAlertIdI2c1FatalFault = 8, /**< i2c1_fatal_fault */
  kTopEarlgreyAlertIdI2c2FatalFault = 9, /**< i2c2_fatal_fault */
  kTopEarlgreyAlertIdI3c0FatalFault = 10, /**< i3c0_fatal_fault */
  kTopEarlgreyAlertIdI3c1FatalFault = 11, /**< i3c1_fatal_fault */
  kTopEarlgreyAlertIdRvTimerFatalFault = 12, /**< rv_timer_fatal_fault */
  kTopEarlgreyAlertIdOtpCtrlFatalMacroError = 13, /**< otp_ctrl_fatal_macro_error */
  kTopEarlgreyAlertIdOtpCtrlFatalCheckError = 14, /**< otp_ctrl_fatal_check_error */
  kTopEarlgreyAlertIdOtpCtrlFatalBusIntegError = 15, /**< otp_ctrl_fatal_bus_integ_error */
  kTopEarlgreyAlertIdOtpCtrlFatalPrimOtpAlert = 16, /**< otp_ctrl_fatal_prim_otp_alert */
  kTopEarlgreyAlertIdOtpCtrlRecovPrimOtpAlert = 17, /**< otp_ctrl_recov_prim_otp_alert */
  kTopEarlgreyAlertIdLcCtrlFatalProgError = 18, /**< lc_ctrl_fatal_prog_error */
  kTopEarlgreyAlertIdLcCtrlFatalStateError = 19, /**< lc_ctrl_fatal_state_error */
  kTopEarlgreyAlertIdLcCtrlFatalBusIntegError = 20, /**< lc_ctrl_fatal_bus_integ_error */
  kTopEarlgreyAlertIdSpiHost0FatalFault = 21, /**< spi_host0_fatal_fault */
  kTopEarlgreyAlertIdSpiHost1FatalFault = 22, /**< spi_host1_fatal_fault */
  kTopEarlgreyAlertIdUsbdevFatalFault = 23, /**< usbdev_fatal_fault */
  kTopEarlgreyAlertIdPwrmgrFatalFault = 24, /**< pwrmgr_fatal_fault */
  kTopEarlgreyAlertIdRstmgrFatalFault = 25, /**< rstmgr_fatal_fault */
  kTopEarlgreyAlertIdRstmgrFatalCnstyFault = 26, /**< rstmgr_fatal_cnsty_fault */
  kTopEarlgreyAlertIdClkmgrRecovFault = 27, /**< clkmgr_recov_fault */
  kTopEarlgreyAlertIdClkmgrFatalFault = 28, /**< clkmgr_fatal_fault */
  kTopEarlgreyAlertIdSysrstCtrlFatalFault = 29, /**< sysrst_ctrl_fatal_fault */
  kTopEarlgreyAlertIdAdcCtrlFatalFault = 30, /**< adc_ctrl_fatal_fault */
  kTopEarlgreyAlertIdPinmuxFatalFault = 31, /**< pinmux_fatal_fault */
  kTopEarlgreyAlertIdAonTimerFatalFault = 32, /**< aon_timer_fatal_fault */
  kTopEarlgreyAlertIdSensorCtrlRecovAlert = 33, /**< sensor_ctrl_recov_alert */
  kTopEarlgreyAlertIdSensorCtrlFatalAlert = 34, /**< sensor_ctrl_fatal_alert */
  kTopEarlgreyAlertIdSramCtrlRetFatalError = 35, /**< sram_ctrl_ret_fatal_error */
  kTopEarlgreyAlertIdRramCtrlRecovErr = 36, /**< rram_ctrl_recov_err */
  kTopEarlgreyAlertIdRramCtrlFatalStdErr = 37, /**< rram_ctrl_fatal_std_err */
  kTopEarlgreyAlertIdRramCtrlFatalErr = 38, /**< rram_ctrl_fatal_err */
  kTopEarlgreyAlertIdRramCtrlFatalMacroErr = 39, /**< rram_ctrl_fatal_macro_err */
  kTopEarlgreyAlertIdRramCtrlRecovMacroErr = 40, /**< rram_ctrl_recov_macro_err */
  kTopEarlgreyAlertIdRvDmFatalFault = 41, /**< rv_dm_fatal_fault */
  kTopEarlgreyAlertIdRvPlicFatalFault = 42, /**< rv_plic_fatal_fault */
  kTopEarlgreyAlertIdAesRecovCtrlUpdateErr = 43, /**< aes_recov_ctrl_update_err */
  kTopEarlgreyAlertIdAesFatalFault = 44, /**< aes_fatal_fault */
  kTopEarlgreyAlertIdHmacFatalFault = 45, /**< hmac_fatal_fault */
  kTopEarlgreyAlertIdKmacRecovOperationErr = 46, /**< kmac_recov_operation_err */
  kTopEarlgreyAlertIdKmacFatalFaultErr = 47, /**< kmac_fatal_fault_err */
  kTopEarlgreyAlertIdOtbnFatal = 48, /**< otbn_fatal */
  kTopEarlgreyAlertIdOtbnRecov = 49, /**< otbn_recov */
  kTopEarlgreyAlertIdKeymgrDpeRecovOperationErr = 50, /**< keymgr_dpe_recov_operation_err */
  kTopEarlgreyAlertIdKeymgrDpeFatalFaultErr = 51, /**< keymgr_dpe_fatal_fault_err */
  kTopEarlgreyAlertIdCsrngRecovAlert = 52, /**< csrng_recov_alert */
  kTopEarlgreyAlertIdCsrngFatalAlert = 53, /**< csrng_fatal_alert */
  kTopEarlgreyAlertIdEntropySrcRecovAlert = 54, /**< entropy_src_recov_alert */
  kTopEarlgreyAlertIdEntropySrcFatalAlert = 55, /**< entropy_src_fatal_alert */
  kTopEarlgreyAlertIdEdn0RecovAlert = 56, /**< edn0_recov_alert */
  kTopEarlgreyAlertIdEdn0FatalAlert = 57, /**< edn0_fatal_alert */
  kTopEarlgreyAlertIdEdn1RecovAlert = 58, /**< edn1_recov_alert */
  kTopEarlgreyAlertIdEdn1FatalAlert = 59, /**< edn1_fatal_alert */
  kTopEarlgreyAlertIdSramCtrlMainFatalError = 60, /**< sram_ctrl_main_fatal_error */
  kTopEarlgreyAlertIdSramCtrlSecFatalError = 61, /**< sram_ctrl_sec_fatal_error */
  kTopEarlgreyAlertIdRomCtrlFatal = 62, /**< rom_ctrl_fatal */
  kTopEarlgreyAlertIdRvCoreIbexFatalSwErr = 63, /**< rv_core_ibex_fatal_sw_err */
  kTopEarlgreyAlertIdRvCoreIbexRecovSwErr = 64, /**< rv_core_ibex_recov_sw_err */
  kTopEarlgreyAlertIdRvCoreIbexFatalHwErr = 65, /**< rv_core_ibex_fatal_hw_err */
  kTopEarlgreyAlertIdRvCoreIbexRecovHwErr = 66, /**< rv_core_ibex_recov_hw_err */
  kTopEarlgreyAlertIdCheriotMemSysFatalFault = 67, /**< cheriot_mem_sys_fatal_fault */
  kTopEarlgreyAlertIdCheriotMemSysRecovCtrlUpdateErr = 68, /**< cheriot_mem_sys_recov_ctrl_update_err */
  kTopEarlgreyAlertIdSramCtrlMetaFatalError = 69, /**< sram_ctrl_meta_fatal_error */
  kTopEarlgreyAlertIdLast = 69, /**< \internal The Last Valid Alert ID. */
} top_earlgrey_alert_id_t;

/**
 * Alert Handler Alert Source to Peripheral Map
 *
 * This array is a mapping from `top_earlgrey_alert_id_t` to
 * `top_earlgrey_alert_peripheral_t`.
 */
extern const top_earlgrey_alert_peripheral_t
    top_earlgrey_alert_for_peripheral[70];

#define PINMUX_MIO_PERIPH_INSEL_IDX_OFFSET 2

// PERIPH_INSEL ranges from 0 to NUM_MIO_PADS + 2 -1}
//  0 and 1 are tied to value 0 and 1
#define NUM_MIO_PADS 61
#define NUM_DIO_PADS 2

#define PINMUX_PERIPH_OUTSEL_IDX_OFFSET 3

/**
 * Pinmux Peripheral Input.
 */
typedef enum top_earlgrey_pinmux_peripheral_in {
  kTopEarlgreyPinmuxPeripheralInSpiHost0Sd0 = 0, /**< Peripheral Input 0 */
  kTopEarlgreyPinmuxPeripheralInSpiHost0Sd1 = 1, /**< Peripheral Input 1 */
  kTopEarlgreyPinmuxPeripheralInSpiHost0Sd2 = 2, /**< Peripheral Input 2 */
  kTopEarlgreyPinmuxPeripheralInSpiHost0Sd3 = 3, /**< Peripheral Input 3 */
  kTopEarlgreyPinmuxPeripheralInSpiHost1Sd0 = 4, /**< Peripheral Input 4 */
  kTopEarlgreyPinmuxPeripheralInSpiHost1Sd1 = 5, /**< Peripheral Input 5 */
  kTopEarlgreyPinmuxPeripheralInSpiHost1Sd2 = 6, /**< Peripheral Input 6 */
  kTopEarlgreyPinmuxPeripheralInSpiHost1Sd3 = 7, /**< Peripheral Input 7 */
  kTopEarlgreyPinmuxPeripheralInSpiDeviceSd0 = 8, /**< Peripheral Input 8 */
  kTopEarlgreyPinmuxPeripheralInSpiDeviceSd1 = 9, /**< Peripheral Input 9 */
  kTopEarlgreyPinmuxPeripheralInSpiDeviceSd2 = 10, /**< Peripheral Input 10 */
  kTopEarlgreyPinmuxPeripheralInSpiDeviceSd3 = 11, /**< Peripheral Input 11 */
  kTopEarlgreyPinmuxPeripheralInGpio0Gpio0 = 12, /**< Peripheral Input 12 */
  kTopEarlgreyPinmuxPeripheralInGpio0Gpio1 = 13, /**< Peripheral Input 13 */
  kTopEarlgreyPinmuxPeripheralInGpio0Gpio2 = 14, /**< Peripheral Input 14 */
  kTopEarlgreyPinmuxPeripheralInGpio0Gpio3 = 15, /**< Peripheral Input 15 */
  kTopEarlgreyPinmuxPeripheralInGpio0Gpio4 = 16, /**< Peripheral Input 16 */
  kTopEarlgreyPinmuxPeripheralInGpio0Gpio5 = 17, /**< Peripheral Input 17 */
  kTopEarlgreyPinmuxPeripheralInGpio0Gpio6 = 18, /**< Peripheral Input 18 */
  kTopEarlgreyPinmuxPeripheralInGpio0Gpio7 = 19, /**< Peripheral Input 19 */
  kTopEarlgreyPinmuxPeripheralInGpio0Gpio8 = 20, /**< Peripheral Input 20 */
  kTopEarlgreyPinmuxPeripheralInGpio0Gpio9 = 21, /**< Peripheral Input 21 */
  kTopEarlgreyPinmuxPeripheralInGpio0Gpio10 = 22, /**< Peripheral Input 22 */
  kTopEarlgreyPinmuxPeripheralInGpio0Gpio11 = 23, /**< Peripheral Input 23 */
  kTopEarlgreyPinmuxPeripheralInGpio0Gpio12 = 24, /**< Peripheral Input 24 */
  kTopEarlgreyPinmuxPeripheralInGpio0Gpio13 = 25, /**< Peripheral Input 25 */
  kTopEarlgreyPinmuxPeripheralInGpio0Gpio14 = 26, /**< Peripheral Input 26 */
  kTopEarlgreyPinmuxPeripheralInGpio0Gpio15 = 27, /**< Peripheral Input 27 */
  kTopEarlgreyPinmuxPeripheralInGpio0Gpio16 = 28, /**< Peripheral Input 28 */
  kTopEarlgreyPinmuxPeripheralInGpio0Gpio17 = 29, /**< Peripheral Input 29 */
  kTopEarlgreyPinmuxPeripheralInGpio0Gpio18 = 30, /**< Peripheral Input 30 */
  kTopEarlgreyPinmuxPeripheralInGpio0Gpio19 = 31, /**< Peripheral Input 31 */
  kTopEarlgreyPinmuxPeripheralInGpio0Gpio20 = 32, /**< Peripheral Input 32 */
  kTopEarlgreyPinmuxPeripheralInGpio0Gpio21 = 33, /**< Peripheral Input 33 */
  kTopEarlgreyPinmuxPeripheralInGpio0Gpio22 = 34, /**< Peripheral Input 34 */
  kTopEarlgreyPinmuxPeripheralInGpio0Gpio23 = 35, /**< Peripheral Input 35 */
  kTopEarlgreyPinmuxPeripheralInGpio0Gpio24 = 36, /**< Peripheral Input 36 */
  kTopEarlgreyPinmuxPeripheralInGpio0Gpio25 = 37, /**< Peripheral Input 37 */
  kTopEarlgreyPinmuxPeripheralInGpio0Gpio26 = 38, /**< Peripheral Input 38 */
  kTopEarlgreyPinmuxPeripheralInGpio0Gpio27 = 39, /**< Peripheral Input 39 */
  kTopEarlgreyPinmuxPeripheralInGpio0Gpio28 = 40, /**< Peripheral Input 40 */
  kTopEarlgreyPinmuxPeripheralInGpio0Gpio29 = 41, /**< Peripheral Input 41 */
  kTopEarlgreyPinmuxPeripheralInGpio0Gpio30 = 42, /**< Peripheral Input 42 */
  kTopEarlgreyPinmuxPeripheralInGpio0Gpio31 = 43, /**< Peripheral Input 43 */
  kTopEarlgreyPinmuxPeripheralInGpio1Gpio0 = 44, /**< Peripheral Input 44 */
  kTopEarlgreyPinmuxPeripheralInGpio1Gpio1 = 45, /**< Peripheral Input 45 */
  kTopEarlgreyPinmuxPeripheralInGpio1Gpio2 = 46, /**< Peripheral Input 46 */
  kTopEarlgreyPinmuxPeripheralInGpio1Gpio3 = 47, /**< Peripheral Input 47 */
  kTopEarlgreyPinmuxPeripheralInGpio1Gpio4 = 48, /**< Peripheral Input 48 */
  kTopEarlgreyPinmuxPeripheralInGpio1Gpio5 = 49, /**< Peripheral Input 49 */
  kTopEarlgreyPinmuxPeripheralInGpio1Gpio6 = 50, /**< Peripheral Input 50 */
  kTopEarlgreyPinmuxPeripheralInGpio1Gpio7 = 51, /**< Peripheral Input 51 */
  kTopEarlgreyPinmuxPeripheralInGpio1Gpio8 = 52, /**< Peripheral Input 52 */
  kTopEarlgreyPinmuxPeripheralInGpio1Gpio9 = 53, /**< Peripheral Input 53 */
  kTopEarlgreyPinmuxPeripheralInGpio1Gpio10 = 54, /**< Peripheral Input 54 */
  kTopEarlgreyPinmuxPeripheralInGpio1Gpio11 = 55, /**< Peripheral Input 55 */
  kTopEarlgreyPinmuxPeripheralInGpio1Gpio12 = 56, /**< Peripheral Input 56 */
  kTopEarlgreyPinmuxPeripheralInGpio1Gpio13 = 57, /**< Peripheral Input 57 */
  kTopEarlgreyPinmuxPeripheralInGpio1Gpio14 = 58, /**< Peripheral Input 58 */
  kTopEarlgreyPinmuxPeripheralInGpio1Gpio15 = 59, /**< Peripheral Input 59 */
  kTopEarlgreyPinmuxPeripheralInGpio1Gpio16 = 60, /**< Peripheral Input 60 */
  kTopEarlgreyPinmuxPeripheralInGpio1Gpio17 = 61, /**< Peripheral Input 61 */
  kTopEarlgreyPinmuxPeripheralInGpio1Gpio18 = 62, /**< Peripheral Input 62 */
  kTopEarlgreyPinmuxPeripheralInGpio1Gpio19 = 63, /**< Peripheral Input 63 */
  kTopEarlgreyPinmuxPeripheralInGpio1Gpio20 = 64, /**< Peripheral Input 64 */
  kTopEarlgreyPinmuxPeripheralInGpio1Gpio21 = 65, /**< Peripheral Input 65 */
  kTopEarlgreyPinmuxPeripheralInGpio1Gpio22 = 66, /**< Peripheral Input 66 */
  kTopEarlgreyPinmuxPeripheralInGpio1Gpio23 = 67, /**< Peripheral Input 67 */
  kTopEarlgreyPinmuxPeripheralInGpio1Gpio24 = 68, /**< Peripheral Input 68 */
  kTopEarlgreyPinmuxPeripheralInGpio1Gpio25 = 69, /**< Peripheral Input 69 */
  kTopEarlgreyPinmuxPeripheralInGpio1Gpio26 = 70, /**< Peripheral Input 70 */
  kTopEarlgreyPinmuxPeripheralInGpio1Gpio27 = 71, /**< Peripheral Input 71 */
  kTopEarlgreyPinmuxPeripheralInGpio1Gpio28 = 72, /**< Peripheral Input 72 */
  kTopEarlgreyPinmuxPeripheralInGpio1Gpio29 = 73, /**< Peripheral Input 73 */
  kTopEarlgreyPinmuxPeripheralInGpio1Gpio30 = 74, /**< Peripheral Input 74 */
  kTopEarlgreyPinmuxPeripheralInGpio1Gpio31 = 75, /**< Peripheral Input 75 */
  kTopEarlgreyPinmuxPeripheralInI2c0Sda = 76, /**< Peripheral Input 76 */
  kTopEarlgreyPinmuxPeripheralInI2c0Scl = 77, /**< Peripheral Input 77 */
  kTopEarlgreyPinmuxPeripheralInI2c1Sda = 78, /**< Peripheral Input 78 */
  kTopEarlgreyPinmuxPeripheralInI2c1Scl = 79, /**< Peripheral Input 79 */
  kTopEarlgreyPinmuxPeripheralInI2c2Sda = 80, /**< Peripheral Input 80 */
  kTopEarlgreyPinmuxPeripheralInI2c2Scl = 81, /**< Peripheral Input 81 */
  kTopEarlgreyPinmuxPeripheralInI3c0Scl = 82, /**< Peripheral Input 82 */
  kTopEarlgreyPinmuxPeripheralInI3c0Sda = 83, /**< Peripheral Input 83 */
  kTopEarlgreyPinmuxPeripheralInI3c1Scl = 84, /**< Peripheral Input 84 */
  kTopEarlgreyPinmuxPeripheralInI3c1Sda = 85, /**< Peripheral Input 85 */
  kTopEarlgreyPinmuxPeripheralInSysrstCtrlEcRstL = 86, /**< Peripheral Input 86 */
  kTopEarlgreyPinmuxPeripheralInSysrstCtrlFlashWpL = 87, /**< Peripheral Input 87 */
  kTopEarlgreyPinmuxPeripheralInUsbdevSense = 88, /**< Peripheral Input 88 */
  kTopEarlgreyPinmuxPeripheralInSpiDeviceSck = 89, /**< Peripheral Input 89 */
  kTopEarlgreyPinmuxPeripheralInSpiDeviceCsb = 90, /**< Peripheral Input 90 */
  kTopEarlgreyPinmuxPeripheralInSpiDeviceTpmCsb = 91, /**< Peripheral Input 91 */
  kTopEarlgreyPinmuxPeripheralInUart0Rx = 92, /**< Peripheral Input 92 */
  kTopEarlgreyPinmuxPeripheralInUart1Rx = 93, /**< Peripheral Input 93 */
  kTopEarlgreyPinmuxPeripheralInUart2Rx = 94, /**< Peripheral Input 94 */
  kTopEarlgreyPinmuxPeripheralInUart3Rx = 95, /**< Peripheral Input 95 */
  kTopEarlgreyPinmuxPeripheralInI3c0RstdetScl = 96, /**< Peripheral Input 96 */
  kTopEarlgreyPinmuxPeripheralInI3c0RstdetSda = 97, /**< Peripheral Input 97 */
  kTopEarlgreyPinmuxPeripheralInI3c1RstdetScl = 98, /**< Peripheral Input 98 */
  kTopEarlgreyPinmuxPeripheralInI3c1RstdetSda = 99, /**< Peripheral Input 99 */
  kTopEarlgreyPinmuxPeripheralInSysrstCtrlAcPresent = 100, /**< Peripheral Input 100 */
  kTopEarlgreyPinmuxPeripheralInSysrstCtrlKey0In = 101, /**< Peripheral Input 101 */
  kTopEarlgreyPinmuxPeripheralInSysrstCtrlKey1In = 102, /**< Peripheral Input 102 */
  kTopEarlgreyPinmuxPeripheralInSysrstCtrlKey2In = 103, /**< Peripheral Input 103 */
  kTopEarlgreyPinmuxPeripheralInSysrstCtrlPwrbIn = 104, /**< Peripheral Input 104 */
  kTopEarlgreyPinmuxPeripheralInSysrstCtrlLidOpen = 105, /**< Peripheral Input 105 */
  kTopEarlgreyPinmuxPeripheralInLast = 105, /**< \internal Last valid peripheral input */
} top_earlgrey_pinmux_peripheral_in_t;

/**
 * Pinmux MIO Input Selector.
 */
typedef enum top_earlgrey_pinmux_insel {
  kTopEarlgreyPinmuxInselConstantZero = 0, /**< Tie constantly to zero */
  kTopEarlgreyPinmuxInselConstantOne = 1, /**< Tie constantly to one */
  kTopEarlgreyPinmuxInselSpiHostD0 = 2, /**< MIO Pad 0 */
  kTopEarlgreyPinmuxInselSpiHostD1 = 3, /**< MIO Pad 1 */
  kTopEarlgreyPinmuxInselSpiHostD2 = 4, /**< MIO Pad 2 */
  kTopEarlgreyPinmuxInselSpiHostD3 = 5, /**< MIO Pad 3 */
  kTopEarlgreyPinmuxInselSpiHostClk = 6, /**< MIO Pad 4 */
  kTopEarlgreyPinmuxInselSpiHostCsL = 7, /**< MIO Pad 5 */
  kTopEarlgreyPinmuxInselSpiDevD0 = 8, /**< MIO Pad 6 */
  kTopEarlgreyPinmuxInselSpiDevD1 = 9, /**< MIO Pad 7 */
  kTopEarlgreyPinmuxInselSpiDevD2 = 10, /**< MIO Pad 8 */
  kTopEarlgreyPinmuxInselSpiDevD3 = 11, /**< MIO Pad 9 */
  kTopEarlgreyPinmuxInselSpiDevClk = 12, /**< MIO Pad 10 */
  kTopEarlgreyPinmuxInselSpiDevCsL = 13, /**< MIO Pad 11 */
  kTopEarlgreyPinmuxInselIoa0 = 14, /**< MIO Pad 12 */
  kTopEarlgreyPinmuxInselIoa1 = 15, /**< MIO Pad 13 */
  kTopEarlgreyPinmuxInselIoa2 = 16, /**< MIO Pad 14 */
  kTopEarlgreyPinmuxInselIoa3 = 17, /**< MIO Pad 15 */
  kTopEarlgreyPinmuxInselIoa4 = 18, /**< MIO Pad 16 */
  kTopEarlgreyPinmuxInselIoa5 = 19, /**< MIO Pad 17 */
  kTopEarlgreyPinmuxInselIoa6 = 20, /**< MIO Pad 18 */
  kTopEarlgreyPinmuxInselIoa7 = 21, /**< MIO Pad 19 */
  kTopEarlgreyPinmuxInselIoa8 = 22, /**< MIO Pad 20 */
  kTopEarlgreyPinmuxInselIob0 = 23, /**< MIO Pad 21 */
  kTopEarlgreyPinmuxInselIob1 = 24, /**< MIO Pad 22 */
  kTopEarlgreyPinmuxInselIob2 = 25, /**< MIO Pad 23 */
  kTopEarlgreyPinmuxInselIob3 = 26, /**< MIO Pad 24 */
  kTopEarlgreyPinmuxInselIob4 = 27, /**< MIO Pad 25 */
  kTopEarlgreyPinmuxInselIob5 = 28, /**< MIO Pad 26 */
  kTopEarlgreyPinmuxInselIob6 = 29, /**< MIO Pad 27 */
  kTopEarlgreyPinmuxInselIob7 = 30, /**< MIO Pad 28 */
  kTopEarlgreyPinmuxInselIob8 = 31, /**< MIO Pad 29 */
  kTopEarlgreyPinmuxInselIob9 = 32, /**< MIO Pad 30 */
  kTopEarlgreyPinmuxInselIob10 = 33, /**< MIO Pad 31 */
  kTopEarlgreyPinmuxInselIob11 = 34, /**< MIO Pad 32 */
  kTopEarlgreyPinmuxInselIob12 = 35, /**< MIO Pad 33 */
  kTopEarlgreyPinmuxInselIoc0 = 36, /**< MIO Pad 34 */
  kTopEarlgreyPinmuxInselIoc1 = 37, /**< MIO Pad 35 */
  kTopEarlgreyPinmuxInselIoc2 = 38, /**< MIO Pad 36 */
  kTopEarlgreyPinmuxInselIoc3 = 39, /**< MIO Pad 37 */
  kTopEarlgreyPinmuxInselIoc4 = 40, /**< MIO Pad 38 */
  kTopEarlgreyPinmuxInselIoc5 = 41, /**< MIO Pad 39 */
  kTopEarlgreyPinmuxInselIoc6 = 42, /**< MIO Pad 40 */
  kTopEarlgreyPinmuxInselIoc7 = 43, /**< MIO Pad 41 */
  kTopEarlgreyPinmuxInselIoc8 = 44, /**< MIO Pad 42 */
  kTopEarlgreyPinmuxInselIoc9 = 45, /**< MIO Pad 43 */
  kTopEarlgreyPinmuxInselIoc10 = 46, /**< MIO Pad 44 */
  kTopEarlgreyPinmuxInselIoc11 = 47, /**< MIO Pad 45 */
  kTopEarlgreyPinmuxInselIoc12 = 48, /**< MIO Pad 46 */
  kTopEarlgreyPinmuxInselIor0 = 49, /**< MIO Pad 47 */
  kTopEarlgreyPinmuxInselIor1 = 50, /**< MIO Pad 48 */
  kTopEarlgreyPinmuxInselIor2 = 51, /**< MIO Pad 49 */
  kTopEarlgreyPinmuxInselIor3 = 52, /**< MIO Pad 50 */
  kTopEarlgreyPinmuxInselIor4 = 53, /**< MIO Pad 51 */
  kTopEarlgreyPinmuxInselIor5 = 54, /**< MIO Pad 52 */
  kTopEarlgreyPinmuxInselIor6 = 55, /**< MIO Pad 53 */
  kTopEarlgreyPinmuxInselIor7 = 56, /**< MIO Pad 54 */
  kTopEarlgreyPinmuxInselIor8 = 57, /**< MIO Pad 55 */
  kTopEarlgreyPinmuxInselIor9 = 58, /**< MIO Pad 56 */
  kTopEarlgreyPinmuxInselIor10 = 59, /**< MIO Pad 57 */
  kTopEarlgreyPinmuxInselIor11 = 60, /**< MIO Pad 58 */
  kTopEarlgreyPinmuxInselIor12 = 61, /**< MIO Pad 59 */
  kTopEarlgreyPinmuxInselIor13 = 62, /**< MIO Pad 60 */
  kTopEarlgreyPinmuxInselLast = 62, /**< \internal Last valid insel value */
} top_earlgrey_pinmux_insel_t;

/**
 * Pinmux MIO Output.
 */
typedef enum top_earlgrey_pinmux_mio_out {
  kTopEarlgreyPinmuxMioOutSpiHostD0 = 0, /**< MIO Pad 0 */
  kTopEarlgreyPinmuxMioOutSpiHostD1 = 1, /**< MIO Pad 1 */
  kTopEarlgreyPinmuxMioOutSpiHostD2 = 2, /**< MIO Pad 2 */
  kTopEarlgreyPinmuxMioOutSpiHostD3 = 3, /**< MIO Pad 3 */
  kTopEarlgreyPinmuxMioOutSpiHostClk = 4, /**< MIO Pad 4 */
  kTopEarlgreyPinmuxMioOutSpiHostCsL = 5, /**< MIO Pad 5 */
  kTopEarlgreyPinmuxMioOutSpiDevD0 = 6, /**< MIO Pad 6 */
  kTopEarlgreyPinmuxMioOutSpiDevD1 = 7, /**< MIO Pad 7 */
  kTopEarlgreyPinmuxMioOutSpiDevD2 = 8, /**< MIO Pad 8 */
  kTopEarlgreyPinmuxMioOutSpiDevD3 = 9, /**< MIO Pad 9 */
  kTopEarlgreyPinmuxMioOutSpiDevClk = 10, /**< MIO Pad 10 */
  kTopEarlgreyPinmuxMioOutSpiDevCsL = 11, /**< MIO Pad 11 */
  kTopEarlgreyPinmuxMioOutIoa0 = 12, /**< MIO Pad 12 */
  kTopEarlgreyPinmuxMioOutIoa1 = 13, /**< MIO Pad 13 */
  kTopEarlgreyPinmuxMioOutIoa2 = 14, /**< MIO Pad 14 */
  kTopEarlgreyPinmuxMioOutIoa3 = 15, /**< MIO Pad 15 */
  kTopEarlgreyPinmuxMioOutIoa4 = 16, /**< MIO Pad 16 */
  kTopEarlgreyPinmuxMioOutIoa5 = 17, /**< MIO Pad 17 */
  kTopEarlgreyPinmuxMioOutIoa6 = 18, /**< MIO Pad 18 */
  kTopEarlgreyPinmuxMioOutIoa7 = 19, /**< MIO Pad 19 */
  kTopEarlgreyPinmuxMioOutIoa8 = 20, /**< MIO Pad 20 */
  kTopEarlgreyPinmuxMioOutIob0 = 21, /**< MIO Pad 21 */
  kTopEarlgreyPinmuxMioOutIob1 = 22, /**< MIO Pad 22 */
  kTopEarlgreyPinmuxMioOutIob2 = 23, /**< MIO Pad 23 */
  kTopEarlgreyPinmuxMioOutIob3 = 24, /**< MIO Pad 24 */
  kTopEarlgreyPinmuxMioOutIob4 = 25, /**< MIO Pad 25 */
  kTopEarlgreyPinmuxMioOutIob5 = 26, /**< MIO Pad 26 */
  kTopEarlgreyPinmuxMioOutIob6 = 27, /**< MIO Pad 27 */
  kTopEarlgreyPinmuxMioOutIob7 = 28, /**< MIO Pad 28 */
  kTopEarlgreyPinmuxMioOutIob8 = 29, /**< MIO Pad 29 */
  kTopEarlgreyPinmuxMioOutIob9 = 30, /**< MIO Pad 30 */
  kTopEarlgreyPinmuxMioOutIob10 = 31, /**< MIO Pad 31 */
  kTopEarlgreyPinmuxMioOutIob11 = 32, /**< MIO Pad 32 */
  kTopEarlgreyPinmuxMioOutIob12 = 33, /**< MIO Pad 33 */
  kTopEarlgreyPinmuxMioOutIoc0 = 34, /**< MIO Pad 34 */
  kTopEarlgreyPinmuxMioOutIoc1 = 35, /**< MIO Pad 35 */
  kTopEarlgreyPinmuxMioOutIoc2 = 36, /**< MIO Pad 36 */
  kTopEarlgreyPinmuxMioOutIoc3 = 37, /**< MIO Pad 37 */
  kTopEarlgreyPinmuxMioOutIoc4 = 38, /**< MIO Pad 38 */
  kTopEarlgreyPinmuxMioOutIoc5 = 39, /**< MIO Pad 39 */
  kTopEarlgreyPinmuxMioOutIoc6 = 40, /**< MIO Pad 40 */
  kTopEarlgreyPinmuxMioOutIoc7 = 41, /**< MIO Pad 41 */
  kTopEarlgreyPinmuxMioOutIoc8 = 42, /**< MIO Pad 42 */
  kTopEarlgreyPinmuxMioOutIoc9 = 43, /**< MIO Pad 43 */
  kTopEarlgreyPinmuxMioOutIoc10 = 44, /**< MIO Pad 44 */
  kTopEarlgreyPinmuxMioOutIoc11 = 45, /**< MIO Pad 45 */
  kTopEarlgreyPinmuxMioOutIoc12 = 46, /**< MIO Pad 46 */
  kTopEarlgreyPinmuxMioOutIor0 = 47, /**< MIO Pad 47 */
  kTopEarlgreyPinmuxMioOutIor1 = 48, /**< MIO Pad 48 */
  kTopEarlgreyPinmuxMioOutIor2 = 49, /**< MIO Pad 49 */
  kTopEarlgreyPinmuxMioOutIor3 = 50, /**< MIO Pad 50 */
  kTopEarlgreyPinmuxMioOutIor4 = 51, /**< MIO Pad 51 */
  kTopEarlgreyPinmuxMioOutIor5 = 52, /**< MIO Pad 52 */
  kTopEarlgreyPinmuxMioOutIor6 = 53, /**< MIO Pad 53 */
  kTopEarlgreyPinmuxMioOutIor7 = 54, /**< MIO Pad 54 */
  kTopEarlgreyPinmuxMioOutIor8 = 55, /**< MIO Pad 55 */
  kTopEarlgreyPinmuxMioOutIor9 = 56, /**< MIO Pad 56 */
  kTopEarlgreyPinmuxMioOutIor10 = 57, /**< MIO Pad 57 */
  kTopEarlgreyPinmuxMioOutIor11 = 58, /**< MIO Pad 58 */
  kTopEarlgreyPinmuxMioOutIor12 = 59, /**< MIO Pad 59 */
  kTopEarlgreyPinmuxMioOutIor13 = 60, /**< MIO Pad 60 */
  kTopEarlgreyPinmuxMioOutLast = 60, /**< \internal Last valid mio output */
} top_earlgrey_pinmux_mio_out_t;

/**
 * Pinmux Peripheral Output Selector.
 */
typedef enum top_earlgrey_pinmux_outsel {
  kTopEarlgreyPinmuxOutselConstantZero = 0, /**< Tie constantly to zero */
  kTopEarlgreyPinmuxOutselConstantOne = 1, /**< Tie constantly to one */
  kTopEarlgreyPinmuxOutselConstantHighZ = 2, /**< Tie constantly to high-Z */
  kTopEarlgreyPinmuxOutselSpiHost0Sd0 = 3, /**< Peripheral Output 0 */
  kTopEarlgreyPinmuxOutselSpiHost0Sd1 = 4, /**< Peripheral Output 1 */
  kTopEarlgreyPinmuxOutselSpiHost0Sd2 = 5, /**< Peripheral Output 2 */
  kTopEarlgreyPinmuxOutselSpiHost0Sd3 = 6, /**< Peripheral Output 3 */
  kTopEarlgreyPinmuxOutselSpiHost1Sd0 = 7, /**< Peripheral Output 4 */
  kTopEarlgreyPinmuxOutselSpiHost1Sd1 = 8, /**< Peripheral Output 5 */
  kTopEarlgreyPinmuxOutselSpiHost1Sd2 = 9, /**< Peripheral Output 6 */
  kTopEarlgreyPinmuxOutselSpiHost1Sd3 = 10, /**< Peripheral Output 7 */
  kTopEarlgreyPinmuxOutselSpiDeviceSd0 = 11, /**< Peripheral Output 8 */
  kTopEarlgreyPinmuxOutselSpiDeviceSd1 = 12, /**< Peripheral Output 9 */
  kTopEarlgreyPinmuxOutselSpiDeviceSd2 = 13, /**< Peripheral Output 10 */
  kTopEarlgreyPinmuxOutselSpiDeviceSd3 = 14, /**< Peripheral Output 11 */
  kTopEarlgreyPinmuxOutselGpio0Gpio0 = 15, /**< Peripheral Output 12 */
  kTopEarlgreyPinmuxOutselGpio0Gpio1 = 16, /**< Peripheral Output 13 */
  kTopEarlgreyPinmuxOutselGpio0Gpio2 = 17, /**< Peripheral Output 14 */
  kTopEarlgreyPinmuxOutselGpio0Gpio3 = 18, /**< Peripheral Output 15 */
  kTopEarlgreyPinmuxOutselGpio0Gpio4 = 19, /**< Peripheral Output 16 */
  kTopEarlgreyPinmuxOutselGpio0Gpio5 = 20, /**< Peripheral Output 17 */
  kTopEarlgreyPinmuxOutselGpio0Gpio6 = 21, /**< Peripheral Output 18 */
  kTopEarlgreyPinmuxOutselGpio0Gpio7 = 22, /**< Peripheral Output 19 */
  kTopEarlgreyPinmuxOutselGpio0Gpio8 = 23, /**< Peripheral Output 20 */
  kTopEarlgreyPinmuxOutselGpio0Gpio9 = 24, /**< Peripheral Output 21 */
  kTopEarlgreyPinmuxOutselGpio0Gpio10 = 25, /**< Peripheral Output 22 */
  kTopEarlgreyPinmuxOutselGpio0Gpio11 = 26, /**< Peripheral Output 23 */
  kTopEarlgreyPinmuxOutselGpio0Gpio12 = 27, /**< Peripheral Output 24 */
  kTopEarlgreyPinmuxOutselGpio0Gpio13 = 28, /**< Peripheral Output 25 */
  kTopEarlgreyPinmuxOutselGpio0Gpio14 = 29, /**< Peripheral Output 26 */
  kTopEarlgreyPinmuxOutselGpio0Gpio15 = 30, /**< Peripheral Output 27 */
  kTopEarlgreyPinmuxOutselGpio0Gpio16 = 31, /**< Peripheral Output 28 */
  kTopEarlgreyPinmuxOutselGpio0Gpio17 = 32, /**< Peripheral Output 29 */
  kTopEarlgreyPinmuxOutselGpio0Gpio18 = 33, /**< Peripheral Output 30 */
  kTopEarlgreyPinmuxOutselGpio0Gpio19 = 34, /**< Peripheral Output 31 */
  kTopEarlgreyPinmuxOutselGpio0Gpio20 = 35, /**< Peripheral Output 32 */
  kTopEarlgreyPinmuxOutselGpio0Gpio21 = 36, /**< Peripheral Output 33 */
  kTopEarlgreyPinmuxOutselGpio0Gpio22 = 37, /**< Peripheral Output 34 */
  kTopEarlgreyPinmuxOutselGpio0Gpio23 = 38, /**< Peripheral Output 35 */
  kTopEarlgreyPinmuxOutselGpio0Gpio24 = 39, /**< Peripheral Output 36 */
  kTopEarlgreyPinmuxOutselGpio0Gpio25 = 40, /**< Peripheral Output 37 */
  kTopEarlgreyPinmuxOutselGpio0Gpio26 = 41, /**< Peripheral Output 38 */
  kTopEarlgreyPinmuxOutselGpio0Gpio27 = 42, /**< Peripheral Output 39 */
  kTopEarlgreyPinmuxOutselGpio0Gpio28 = 43, /**< Peripheral Output 40 */
  kTopEarlgreyPinmuxOutselGpio0Gpio29 = 44, /**< Peripheral Output 41 */
  kTopEarlgreyPinmuxOutselGpio0Gpio30 = 45, /**< Peripheral Output 42 */
  kTopEarlgreyPinmuxOutselGpio0Gpio31 = 46, /**< Peripheral Output 43 */
  kTopEarlgreyPinmuxOutselGpio1Gpio0 = 47, /**< Peripheral Output 44 */
  kTopEarlgreyPinmuxOutselGpio1Gpio1 = 48, /**< Peripheral Output 45 */
  kTopEarlgreyPinmuxOutselGpio1Gpio2 = 49, /**< Peripheral Output 46 */
  kTopEarlgreyPinmuxOutselGpio1Gpio3 = 50, /**< Peripheral Output 47 */
  kTopEarlgreyPinmuxOutselGpio1Gpio4 = 51, /**< Peripheral Output 48 */
  kTopEarlgreyPinmuxOutselGpio1Gpio5 = 52, /**< Peripheral Output 49 */
  kTopEarlgreyPinmuxOutselGpio1Gpio6 = 53, /**< Peripheral Output 50 */
  kTopEarlgreyPinmuxOutselGpio1Gpio7 = 54, /**< Peripheral Output 51 */
  kTopEarlgreyPinmuxOutselGpio1Gpio8 = 55, /**< Peripheral Output 52 */
  kTopEarlgreyPinmuxOutselGpio1Gpio9 = 56, /**< Peripheral Output 53 */
  kTopEarlgreyPinmuxOutselGpio1Gpio10 = 57, /**< Peripheral Output 54 */
  kTopEarlgreyPinmuxOutselGpio1Gpio11 = 58, /**< Peripheral Output 55 */
  kTopEarlgreyPinmuxOutselGpio1Gpio12 = 59, /**< Peripheral Output 56 */
  kTopEarlgreyPinmuxOutselGpio1Gpio13 = 60, /**< Peripheral Output 57 */
  kTopEarlgreyPinmuxOutselGpio1Gpio14 = 61, /**< Peripheral Output 58 */
  kTopEarlgreyPinmuxOutselGpio1Gpio15 = 62, /**< Peripheral Output 59 */
  kTopEarlgreyPinmuxOutselGpio1Gpio16 = 63, /**< Peripheral Output 60 */
  kTopEarlgreyPinmuxOutselGpio1Gpio17 = 64, /**< Peripheral Output 61 */
  kTopEarlgreyPinmuxOutselGpio1Gpio18 = 65, /**< Peripheral Output 62 */
  kTopEarlgreyPinmuxOutselGpio1Gpio19 = 66, /**< Peripheral Output 63 */
  kTopEarlgreyPinmuxOutselGpio1Gpio20 = 67, /**< Peripheral Output 64 */
  kTopEarlgreyPinmuxOutselGpio1Gpio21 = 68, /**< Peripheral Output 65 */
  kTopEarlgreyPinmuxOutselGpio1Gpio22 = 69, /**< Peripheral Output 66 */
  kTopEarlgreyPinmuxOutselGpio1Gpio23 = 70, /**< Peripheral Output 67 */
  kTopEarlgreyPinmuxOutselGpio1Gpio24 = 71, /**< Peripheral Output 68 */
  kTopEarlgreyPinmuxOutselGpio1Gpio25 = 72, /**< Peripheral Output 69 */
  kTopEarlgreyPinmuxOutselGpio1Gpio26 = 73, /**< Peripheral Output 70 */
  kTopEarlgreyPinmuxOutselGpio1Gpio27 = 74, /**< Peripheral Output 71 */
  kTopEarlgreyPinmuxOutselGpio1Gpio28 = 75, /**< Peripheral Output 72 */
  kTopEarlgreyPinmuxOutselGpio1Gpio29 = 76, /**< Peripheral Output 73 */
  kTopEarlgreyPinmuxOutselGpio1Gpio30 = 77, /**< Peripheral Output 74 */
  kTopEarlgreyPinmuxOutselGpio1Gpio31 = 78, /**< Peripheral Output 75 */
  kTopEarlgreyPinmuxOutselI2c0Sda = 79, /**< Peripheral Output 76 */
  kTopEarlgreyPinmuxOutselI2c0Scl = 80, /**< Peripheral Output 77 */
  kTopEarlgreyPinmuxOutselI2c1Sda = 81, /**< Peripheral Output 78 */
  kTopEarlgreyPinmuxOutselI2c1Scl = 82, /**< Peripheral Output 79 */
  kTopEarlgreyPinmuxOutselI2c2Sda = 83, /**< Peripheral Output 80 */
  kTopEarlgreyPinmuxOutselI2c2Scl = 84, /**< Peripheral Output 81 */
  kTopEarlgreyPinmuxOutselI3c0Scl = 85, /**< Peripheral Output 82 */
  kTopEarlgreyPinmuxOutselI3c0Sda = 86, /**< Peripheral Output 83 */
  kTopEarlgreyPinmuxOutselI3c1Scl = 87, /**< Peripheral Output 84 */
  kTopEarlgreyPinmuxOutselI3c1Sda = 88, /**< Peripheral Output 85 */
  kTopEarlgreyPinmuxOutselSysrstCtrlEcRstL = 89, /**< Peripheral Output 86 */
  kTopEarlgreyPinmuxOutselSysrstCtrlFlashWpL = 90, /**< Peripheral Output 87 */
  kTopEarlgreyPinmuxOutselSpiHost0Sck = 91, /**< Peripheral Output 88 */
  kTopEarlgreyPinmuxOutselSpiHost0Csb0 = 92, /**< Peripheral Output 89 */
  kTopEarlgreyPinmuxOutselSpiHost0Csb1 = 93, /**< Peripheral Output 90 */
  kTopEarlgreyPinmuxOutselSpiHost0Csb2 = 94, /**< Peripheral Output 91 */
  kTopEarlgreyPinmuxOutselSpiHost1Sck = 95, /**< Peripheral Output 92 */
  kTopEarlgreyPinmuxOutselSpiHost1Csb0 = 96, /**< Peripheral Output 93 */
  kTopEarlgreyPinmuxOutselSpiHost1Csb1 = 97, /**< Peripheral Output 94 */
  kTopEarlgreyPinmuxOutselSpiHost1Csb2 = 98, /**< Peripheral Output 95 */
  kTopEarlgreyPinmuxOutselUart0Tx = 99, /**< Peripheral Output 96 */
  kTopEarlgreyPinmuxOutselUart1Tx = 100, /**< Peripheral Output 97 */
  kTopEarlgreyPinmuxOutselUart2Tx = 101, /**< Peripheral Output 98 */
  kTopEarlgreyPinmuxOutselUart3Tx = 102, /**< Peripheral Output 99 */
  kTopEarlgreyPinmuxOutselI3c0CtrlSdaPu = 103, /**< Peripheral Output 100 */
  kTopEarlgreyPinmuxOutselI3c1CtrlSdaPu = 104, /**< Peripheral Output 101 */
  kTopEarlgreyPinmuxOutselSensorCtrlAstDebugOut0 = 105, /**< Peripheral Output 102 */
  kTopEarlgreyPinmuxOutselSensorCtrlAstDebugOut1 = 106, /**< Peripheral Output 103 */
  kTopEarlgreyPinmuxOutselSensorCtrlAstDebugOut2 = 107, /**< Peripheral Output 104 */
  kTopEarlgreyPinmuxOutselSensorCtrlAstDebugOut3 = 108, /**< Peripheral Output 105 */
  kTopEarlgreyPinmuxOutselSensorCtrlAstDebugOut4 = 109, /**< Peripheral Output 106 */
  kTopEarlgreyPinmuxOutselSensorCtrlAstDebugOut5 = 110, /**< Peripheral Output 107 */
  kTopEarlgreyPinmuxOutselSensorCtrlAstDebugOut6 = 111, /**< Peripheral Output 108 */
  kTopEarlgreyPinmuxOutselSensorCtrlAstDebugOut7 = 112, /**< Peripheral Output 109 */
  kTopEarlgreyPinmuxOutselSysrstCtrlBatDisable = 113, /**< Peripheral Output 110 */
  kTopEarlgreyPinmuxOutselSysrstCtrlKey0Out = 114, /**< Peripheral Output 111 */
  kTopEarlgreyPinmuxOutselSysrstCtrlKey1Out = 115, /**< Peripheral Output 112 */
  kTopEarlgreyPinmuxOutselSysrstCtrlKey2Out = 116, /**< Peripheral Output 113 */
  kTopEarlgreyPinmuxOutselSysrstCtrlPwrbOut = 117, /**< Peripheral Output 114 */
  kTopEarlgreyPinmuxOutselSysrstCtrlZ3Wakeup = 118, /**< Peripheral Output 115 */
  kTopEarlgreyPinmuxOutselLast = 118, /**< \internal Last valid outsel value */
} top_earlgrey_pinmux_outsel_t;

/**
 * Dedicated Pad Selects
 */
typedef enum top_earlgrey_direct_pads {
  kTopEarlgreyDirectPadsUsbdevUsbDp = 0, /**<  */
  kTopEarlgreyDirectPadsUsbdevUsbDn = 1, /**<  */
  kTopEarlgreyDirectPadsLast = 1, /**< \internal Last valid direct pad */
} top_earlgrey_direct_pads_t;

/**
 * Muxed Pad Selects
 */
typedef enum top_earlgrey_muxed_pads {
  kTopEarlgreyMuxedPadsSpiHostD0 = 0, /**<  */
  kTopEarlgreyMuxedPadsSpiHostD1 = 1, /**<  */
  kTopEarlgreyMuxedPadsSpiHostD2 = 2, /**<  */
  kTopEarlgreyMuxedPadsSpiHostD3 = 3, /**<  */
  kTopEarlgreyMuxedPadsSpiHostClk = 4, /**<  */
  kTopEarlgreyMuxedPadsSpiHostCsL = 5, /**<  */
  kTopEarlgreyMuxedPadsSpiDevD0 = 6, /**<  */
  kTopEarlgreyMuxedPadsSpiDevD1 = 7, /**<  */
  kTopEarlgreyMuxedPadsSpiDevD2 = 8, /**<  */
  kTopEarlgreyMuxedPadsSpiDevD3 = 9, /**<  */
  kTopEarlgreyMuxedPadsSpiDevClk = 10, /**<  */
  kTopEarlgreyMuxedPadsSpiDevCsL = 11, /**<  */
  kTopEarlgreyMuxedPadsIoa0 = 12, /**<  */
  kTopEarlgreyMuxedPadsIoa1 = 13, /**<  */
  kTopEarlgreyMuxedPadsIoa2 = 14, /**<  */
  kTopEarlgreyMuxedPadsIoa3 = 15, /**<  */
  kTopEarlgreyMuxedPadsIoa4 = 16, /**<  */
  kTopEarlgreyMuxedPadsIoa5 = 17, /**<  */
  kTopEarlgreyMuxedPadsIoa6 = 18, /**<  */
  kTopEarlgreyMuxedPadsIoa7 = 19, /**<  */
  kTopEarlgreyMuxedPadsIoa8 = 20, /**<  */
  kTopEarlgreyMuxedPadsIob0 = 21, /**<  */
  kTopEarlgreyMuxedPadsIob1 = 22, /**<  */
  kTopEarlgreyMuxedPadsIob2 = 23, /**<  */
  kTopEarlgreyMuxedPadsIob3 = 24, /**<  */
  kTopEarlgreyMuxedPadsIob4 = 25, /**<  */
  kTopEarlgreyMuxedPadsIob5 = 26, /**<  */
  kTopEarlgreyMuxedPadsIob6 = 27, /**<  */
  kTopEarlgreyMuxedPadsIob7 = 28, /**<  */
  kTopEarlgreyMuxedPadsIob8 = 29, /**<  */
  kTopEarlgreyMuxedPadsIob9 = 30, /**<  */
  kTopEarlgreyMuxedPadsIob10 = 31, /**<  */
  kTopEarlgreyMuxedPadsIob11 = 32, /**<  */
  kTopEarlgreyMuxedPadsIob12 = 33, /**<  */
  kTopEarlgreyMuxedPadsIoc0 = 34, /**<  */
  kTopEarlgreyMuxedPadsIoc1 = 35, /**<  */
  kTopEarlgreyMuxedPadsIoc2 = 36, /**<  */
  kTopEarlgreyMuxedPadsIoc3 = 37, /**<  */
  kTopEarlgreyMuxedPadsIoc4 = 38, /**<  */
  kTopEarlgreyMuxedPadsIoc5 = 39, /**<  */
  kTopEarlgreyMuxedPadsIoc6 = 40, /**<  */
  kTopEarlgreyMuxedPadsIoc7 = 41, /**<  */
  kTopEarlgreyMuxedPadsIoc8 = 42, /**<  */
  kTopEarlgreyMuxedPadsIoc9 = 43, /**<  */
  kTopEarlgreyMuxedPadsIoc10 = 44, /**<  */
  kTopEarlgreyMuxedPadsIoc11 = 45, /**<  */
  kTopEarlgreyMuxedPadsIoc12 = 46, /**<  */
  kTopEarlgreyMuxedPadsIor0 = 47, /**<  */
  kTopEarlgreyMuxedPadsIor1 = 48, /**<  */
  kTopEarlgreyMuxedPadsIor2 = 49, /**<  */
  kTopEarlgreyMuxedPadsIor3 = 50, /**<  */
  kTopEarlgreyMuxedPadsIor4 = 51, /**<  */
  kTopEarlgreyMuxedPadsIor5 = 52, /**<  */
  kTopEarlgreyMuxedPadsIor6 = 53, /**<  */
  kTopEarlgreyMuxedPadsIor7 = 54, /**<  */
  kTopEarlgreyMuxedPadsIor8 = 55, /**<  */
  kTopEarlgreyMuxedPadsIor9 = 56, /**<  */
  kTopEarlgreyMuxedPadsIor10 = 57, /**<  */
  kTopEarlgreyMuxedPadsIor11 = 58, /**<  */
  kTopEarlgreyMuxedPadsIor12 = 59, /**<  */
  kTopEarlgreyMuxedPadsIor13 = 60, /**<  */
  kTopEarlgreyMuxedPadsLast = 60, /**< \internal Last valid muxed pad */
} top_earlgrey_muxed_pads_t;

/**
 * Power Manager Wakeup Signals
 */
typedef enum top_earlgrey_power_manager_wake_ups {
  kTopEarlgreyPowerManagerWakeUpsI3c0RstdetWkupReq = 0, /**<  */
  kTopEarlgreyPowerManagerWakeUpsI3c1RstdetWkupReq = 1, /**<  */
  kTopEarlgreyPowerManagerWakeUpsSysrstCtrlWkupReq = 2, /**<  */
  kTopEarlgreyPowerManagerWakeUpsAdcCtrlWkupReq = 3, /**<  */
  kTopEarlgreyPowerManagerWakeUpsPinmuxPinWkupReq = 4, /**<  */
  kTopEarlgreyPowerManagerWakeUpsPinmuxUsbWkupReq = 5, /**<  */
  kTopEarlgreyPowerManagerWakeUpsAonTimerWkupReq = 6, /**<  */
  kTopEarlgreyPowerManagerWakeUpsSensorCtrlWkupReq = 7, /**<  */
  kTopEarlgreyPowerManagerWakeUpsLast = 7, /**< \internal Last valid pwrmgr wakeup signal */
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
  kTopEarlgreyResetManagerSwResetsI3c0 = 8, /**<  */
  kTopEarlgreyResetManagerSwResetsI3c1 = 9, /**<  */
  kTopEarlgreyResetManagerSwResetsLast = 9, /**< \internal Last valid rstmgr software reset request */
} top_earlgrey_reset_manager_sw_resets_t;

/**
 * Power Manager Reset Request Signals
 */
typedef enum top_earlgrey_power_manager_reset_requests {
  kTopEarlgreyPowerManagerResetRequestsSysrstCtrlRstReq = 0, /**<  */
  kTopEarlgreyPowerManagerResetRequestsAonTimerAonTimerRstReq = 1, /**<  */
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
  kTopEarlgreyGateableClocksUsbPeri = 2, /**< Clock clk_usb_peri in group peri */
  kTopEarlgreyGateableClocksIoSpiHost1 = 3, /**< Clock clk_io_spi_host1 in group spi_host1 */
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
 * configuration space, i.e. ROM, main SRAM, and RRAM are excluded but retention
 * SRAM, spi_device memory, or usbdev memory are included.
 */
#define TOP_EARLGREY_MMIO_BASE_ADDR 0x40000000u
#define TOP_EARLGREY_MMIO_SIZE_BYTES 0x10000000u

// Header Extern Guard
#ifdef __cplusplus
}  // extern "C"
#endif

#endif  // OPENTITAN_HW_TOP_EARLGREY_SW_AUTOGEN_TOP_EARLGREY_H_
