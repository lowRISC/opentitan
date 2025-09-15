// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
// util/topgen.py -t hw/top_verbano/data/top_verbano.hjson \
//                -o hw/top_verbano/

#ifndef OPENTITAN_HW_TOP_VERBANO_SW_AUTOGEN_TOP_VERBANO_MEMORY_H_
#define OPENTITAN_HW_TOP_VERBANO_SW_AUTOGEN_TOP_VERBANO_MEMORY_H_

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
 * Memory base for sram_ctrl_ret_aon_ram_ret_aon in top verbano.
 */
#define TOP_VERBANO_RAM_RET_AON_BASE_ADDR 0x40600000

/**
 * Memory size for sram_ctrl_ret_aon_ram_ret_aon in top verbano.
 */
#define TOP_VERBANO_RAM_RET_AON_SIZE_BYTES 0x1000

/**
 * Memory base for flash_ctrl_eflash in top verbano.
 */
#define TOP_VERBANO_EFLASH_BASE_ADDR 0x20000000

/**
 * Memory size for flash_ctrl_eflash in top verbano.
 */
#define TOP_VERBANO_EFLASH_SIZE_BYTES 0x100000

/**
 * Memory base for sram_ctrl_main_ram_main in top verbano.
 */
#define TOP_VERBANO_RAM_MAIN_BASE_ADDR 0x10000000

/**
 * Memory size for sram_ctrl_main_ram_main in top verbano.
 */
#define TOP_VERBANO_RAM_MAIN_SIZE_BYTES 0x20000

/**
 * Memory base for rom_ctrl_rom in top verbano.
 */
#define TOP_VERBANO_ROM_BASE_ADDR 0x00008000

/**
 * Memory size for rom_ctrl_rom in top verbano.
 */
#define TOP_VERBANO_ROM_SIZE_BYTES 0x8000



/**
 * Peripheral base address for uart0 in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_UART0_BASE_ADDR 0x40000000

/**
 * Peripheral size for uart0 in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_UART0_BASE_ADDR and
 * `TOP_VERBANO_UART0_BASE_ADDR + TOP_VERBANO_UART0_SIZE_BYTES`.
 */
#define TOP_VERBANO_UART0_SIZE_BYTES 0x40
/**
 * Peripheral base address for uart1 in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_UART1_BASE_ADDR 0x40010000

/**
 * Peripheral size for uart1 in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_UART1_BASE_ADDR and
 * `TOP_VERBANO_UART1_BASE_ADDR + TOP_VERBANO_UART1_SIZE_BYTES`.
 */
#define TOP_VERBANO_UART1_SIZE_BYTES 0x40
/**
 * Peripheral base address for uart2 in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_UART2_BASE_ADDR 0x40020000

/**
 * Peripheral size for uart2 in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_UART2_BASE_ADDR and
 * `TOP_VERBANO_UART2_BASE_ADDR + TOP_VERBANO_UART2_SIZE_BYTES`.
 */
#define TOP_VERBANO_UART2_SIZE_BYTES 0x40
/**
 * Peripheral base address for uart3 in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_UART3_BASE_ADDR 0x40030000

/**
 * Peripheral size for uart3 in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_UART3_BASE_ADDR and
 * `TOP_VERBANO_UART3_BASE_ADDR + TOP_VERBANO_UART3_SIZE_BYTES`.
 */
#define TOP_VERBANO_UART3_SIZE_BYTES 0x40
/**
 * Peripheral base address for gpio in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_GPIO_BASE_ADDR 0x40040000

/**
 * Peripheral size for gpio in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_GPIO_BASE_ADDR and
 * `TOP_VERBANO_GPIO_BASE_ADDR + TOP_VERBANO_GPIO_SIZE_BYTES`.
 */
#define TOP_VERBANO_GPIO_SIZE_BYTES 0x80
/**
 * Peripheral base address for spi_device in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_SPI_DEVICE_BASE_ADDR 0x40050000

/**
 * Peripheral size for spi_device in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_SPI_DEVICE_BASE_ADDR and
 * `TOP_VERBANO_SPI_DEVICE_BASE_ADDR + TOP_VERBANO_SPI_DEVICE_SIZE_BYTES`.
 */
#define TOP_VERBANO_SPI_DEVICE_SIZE_BYTES 0x2000
/**
 * Peripheral base address for i2c0 in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_I2C0_BASE_ADDR 0x40080000

/**
 * Peripheral size for i2c0 in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_I2C0_BASE_ADDR and
 * `TOP_VERBANO_I2C0_BASE_ADDR + TOP_VERBANO_I2C0_SIZE_BYTES`.
 */
#define TOP_VERBANO_I2C0_SIZE_BYTES 0x80
/**
 * Peripheral base address for i2c1 in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_I2C1_BASE_ADDR 0x40090000

/**
 * Peripheral size for i2c1 in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_I2C1_BASE_ADDR and
 * `TOP_VERBANO_I2C1_BASE_ADDR + TOP_VERBANO_I2C1_SIZE_BYTES`.
 */
#define TOP_VERBANO_I2C1_SIZE_BYTES 0x80
/**
 * Peripheral base address for i2c2 in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_I2C2_BASE_ADDR 0x400A0000

/**
 * Peripheral size for i2c2 in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_I2C2_BASE_ADDR and
 * `TOP_VERBANO_I2C2_BASE_ADDR + TOP_VERBANO_I2C2_SIZE_BYTES`.
 */
#define TOP_VERBANO_I2C2_SIZE_BYTES 0x80
/**
 * Peripheral base address for pattgen in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_PATTGEN_BASE_ADDR 0x400E0000

/**
 * Peripheral size for pattgen in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_PATTGEN_BASE_ADDR and
 * `TOP_VERBANO_PATTGEN_BASE_ADDR + TOP_VERBANO_PATTGEN_SIZE_BYTES`.
 */
#define TOP_VERBANO_PATTGEN_SIZE_BYTES 0x40
/**
 * Peripheral base address for rv_timer in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_RV_TIMER_BASE_ADDR 0x40100000

/**
 * Peripheral size for rv_timer in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_RV_TIMER_BASE_ADDR and
 * `TOP_VERBANO_RV_TIMER_BASE_ADDR + TOP_VERBANO_RV_TIMER_SIZE_BYTES`.
 */
#define TOP_VERBANO_RV_TIMER_SIZE_BYTES 0x200
/**
 * Peripheral base address for core device on otp_ctrl in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_OTP_CTRL_CORE_BASE_ADDR 0x40130000

/**
 * Peripheral size for core device on otp_ctrl in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_OTP_CTRL_CORE_BASE_ADDR and
 * `TOP_VERBANO_OTP_CTRL_CORE_BASE_ADDR + TOP_VERBANO_OTP_CTRL_CORE_SIZE_BYTES`.
 */
#define TOP_VERBANO_OTP_CTRL_CORE_SIZE_BYTES 0x1000
/**
 * Peripheral base address for prim device on otp_macro in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_OTP_MACRO_PRIM_BASE_ADDR 0x40138000

/**
 * Peripheral size for prim device on otp_macro in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_OTP_MACRO_PRIM_BASE_ADDR and
 * `TOP_VERBANO_OTP_MACRO_PRIM_BASE_ADDR + TOP_VERBANO_OTP_MACRO_PRIM_SIZE_BYTES`.
 */
#define TOP_VERBANO_OTP_MACRO_PRIM_SIZE_BYTES 0x20
/**
 * Peripheral base address for regs device on lc_ctrl in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_LC_CTRL_REGS_BASE_ADDR 0x40140000

/**
 * Peripheral size for regs device on lc_ctrl in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_LC_CTRL_REGS_BASE_ADDR and
 * `TOP_VERBANO_LC_CTRL_REGS_BASE_ADDR + TOP_VERBANO_LC_CTRL_REGS_SIZE_BYTES`.
 */
#define TOP_VERBANO_LC_CTRL_REGS_SIZE_BYTES 0x100
/**
 * Peripheral base address for dmi device on lc_ctrl in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_LC_CTRL_DMI_BASE_ADDR 0x0

/**
 * Peripheral size for dmi device on lc_ctrl in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_LC_CTRL_DMI_BASE_ADDR and
 * `TOP_VERBANO_LC_CTRL_DMI_BASE_ADDR + TOP_VERBANO_LC_CTRL_DMI_SIZE_BYTES`.
 */
#define TOP_VERBANO_LC_CTRL_DMI_SIZE_BYTES 0x1000
/**
 * Peripheral base address for alert_handler in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_ALERT_HANDLER_BASE_ADDR 0x40150000

/**
 * Peripheral size for alert_handler in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_ALERT_HANDLER_BASE_ADDR and
 * `TOP_VERBANO_ALERT_HANDLER_BASE_ADDR + TOP_VERBANO_ALERT_HANDLER_SIZE_BYTES`.
 */
#define TOP_VERBANO_ALERT_HANDLER_SIZE_BYTES 0x800
/**
 * Peripheral base address for spi_host0 in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_SPI_HOST0_BASE_ADDR 0x40300000

/**
 * Peripheral size for spi_host0 in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_SPI_HOST0_BASE_ADDR and
 * `TOP_VERBANO_SPI_HOST0_BASE_ADDR + TOP_VERBANO_SPI_HOST0_SIZE_BYTES`.
 */
#define TOP_VERBANO_SPI_HOST0_SIZE_BYTES 0x40
/**
 * Peripheral base address for spi_host1 in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_SPI_HOST1_BASE_ADDR 0x40310000

/**
 * Peripheral size for spi_host1 in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_SPI_HOST1_BASE_ADDR and
 * `TOP_VERBANO_SPI_HOST1_BASE_ADDR + TOP_VERBANO_SPI_HOST1_SIZE_BYTES`.
 */
#define TOP_VERBANO_SPI_HOST1_SIZE_BYTES 0x40
/**
 * Peripheral base address for usbdev in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_USBDEV_BASE_ADDR 0x40320000

/**
 * Peripheral size for usbdev in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_USBDEV_BASE_ADDR and
 * `TOP_VERBANO_USBDEV_BASE_ADDR + TOP_VERBANO_USBDEV_SIZE_BYTES`.
 */
#define TOP_VERBANO_USBDEV_SIZE_BYTES 0x1000
/**
 * Peripheral base address for pwrmgr_aon in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_PWRMGR_AON_BASE_ADDR 0x40400000

/**
 * Peripheral size for pwrmgr_aon in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_PWRMGR_AON_BASE_ADDR and
 * `TOP_VERBANO_PWRMGR_AON_BASE_ADDR + TOP_VERBANO_PWRMGR_AON_SIZE_BYTES`.
 */
#define TOP_VERBANO_PWRMGR_AON_SIZE_BYTES 0x80
/**
 * Peripheral base address for rstmgr_aon in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_RSTMGR_AON_BASE_ADDR 0x40410000

/**
 * Peripheral size for rstmgr_aon in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_RSTMGR_AON_BASE_ADDR and
 * `TOP_VERBANO_RSTMGR_AON_BASE_ADDR + TOP_VERBANO_RSTMGR_AON_SIZE_BYTES`.
 */
#define TOP_VERBANO_RSTMGR_AON_SIZE_BYTES 0x80
/**
 * Peripheral base address for clkmgr_aon in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_CLKMGR_AON_BASE_ADDR 0x40420000

/**
 * Peripheral size for clkmgr_aon in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_CLKMGR_AON_BASE_ADDR and
 * `TOP_VERBANO_CLKMGR_AON_BASE_ADDR + TOP_VERBANO_CLKMGR_AON_SIZE_BYTES`.
 */
#define TOP_VERBANO_CLKMGR_AON_SIZE_BYTES 0x80
/**
 * Peripheral base address for sysrst_ctrl_aon in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_SYSRST_CTRL_AON_BASE_ADDR 0x40430000

/**
 * Peripheral size for sysrst_ctrl_aon in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_SYSRST_CTRL_AON_BASE_ADDR and
 * `TOP_VERBANO_SYSRST_CTRL_AON_BASE_ADDR + TOP_VERBANO_SYSRST_CTRL_AON_SIZE_BYTES`.
 */
#define TOP_VERBANO_SYSRST_CTRL_AON_SIZE_BYTES 0x100
/**
 * Peripheral base address for adc_ctrl_aon in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_ADC_CTRL_AON_BASE_ADDR 0x40440000

/**
 * Peripheral size for adc_ctrl_aon in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_ADC_CTRL_AON_BASE_ADDR and
 * `TOP_VERBANO_ADC_CTRL_AON_BASE_ADDR + TOP_VERBANO_ADC_CTRL_AON_SIZE_BYTES`.
 */
#define TOP_VERBANO_ADC_CTRL_AON_SIZE_BYTES 0x80
/**
 * Peripheral base address for pwm_aon in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_PWM_AON_BASE_ADDR 0x40450000

/**
 * Peripheral size for pwm_aon in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_PWM_AON_BASE_ADDR and
 * `TOP_VERBANO_PWM_AON_BASE_ADDR + TOP_VERBANO_PWM_AON_SIZE_BYTES`.
 */
#define TOP_VERBANO_PWM_AON_SIZE_BYTES 0x80
/**
 * Peripheral base address for pinmux_aon in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_PINMUX_AON_BASE_ADDR 0x40460000

/**
 * Peripheral size for pinmux_aon in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_PINMUX_AON_BASE_ADDR and
 * `TOP_VERBANO_PINMUX_AON_BASE_ADDR + TOP_VERBANO_PINMUX_AON_SIZE_BYTES`.
 */
#define TOP_VERBANO_PINMUX_AON_SIZE_BYTES 0x1000
/**
 * Peripheral base address for aon_timer_aon in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_AON_TIMER_AON_BASE_ADDR 0x40470000

/**
 * Peripheral size for aon_timer_aon in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_AON_TIMER_AON_BASE_ADDR and
 * `TOP_VERBANO_AON_TIMER_AON_BASE_ADDR + TOP_VERBANO_AON_TIMER_AON_SIZE_BYTES`.
 */
#define TOP_VERBANO_AON_TIMER_AON_SIZE_BYTES 0x40
/**
 * Peripheral base address for ast in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_AST_BASE_ADDR 0x40480000

/**
 * Peripheral size for ast in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_AST_BASE_ADDR and
 * `TOP_VERBANO_AST_BASE_ADDR + TOP_VERBANO_AST_SIZE_BYTES`.
 */
#define TOP_VERBANO_AST_SIZE_BYTES 0x400
/**
 * Peripheral base address for sensor_ctrl_aon in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_SENSOR_CTRL_AON_BASE_ADDR 0x40490000

/**
 * Peripheral size for sensor_ctrl_aon in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_SENSOR_CTRL_AON_BASE_ADDR and
 * `TOP_VERBANO_SENSOR_CTRL_AON_BASE_ADDR + TOP_VERBANO_SENSOR_CTRL_AON_SIZE_BYTES`.
 */
#define TOP_VERBANO_SENSOR_CTRL_AON_SIZE_BYTES 0x80
/**
 * Peripheral base address for regs device on sram_ctrl_ret_aon in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_SRAM_CTRL_RET_AON_REGS_BASE_ADDR 0x40500000

/**
 * Peripheral size for regs device on sram_ctrl_ret_aon in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_SRAM_CTRL_RET_AON_REGS_BASE_ADDR and
 * `TOP_VERBANO_SRAM_CTRL_RET_AON_REGS_BASE_ADDR + TOP_VERBANO_SRAM_CTRL_RET_AON_REGS_SIZE_BYTES`.
 */
#define TOP_VERBANO_SRAM_CTRL_RET_AON_REGS_SIZE_BYTES 0x40
/**
 * Peripheral base address for ram device on sram_ctrl_ret_aon in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_SRAM_CTRL_RET_AON_RAM_BASE_ADDR 0x40600000

/**
 * Peripheral size for ram device on sram_ctrl_ret_aon in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_SRAM_CTRL_RET_AON_RAM_BASE_ADDR and
 * `TOP_VERBANO_SRAM_CTRL_RET_AON_RAM_BASE_ADDR + TOP_VERBANO_SRAM_CTRL_RET_AON_RAM_SIZE_BYTES`.
 */
#define TOP_VERBANO_SRAM_CTRL_RET_AON_RAM_SIZE_BYTES 0x1000
/**
 * Peripheral base address for core device on flash_ctrl in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_FLASH_CTRL_CORE_BASE_ADDR 0x41000000

/**
 * Peripheral size for core device on flash_ctrl in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_FLASH_CTRL_CORE_BASE_ADDR and
 * `TOP_VERBANO_FLASH_CTRL_CORE_BASE_ADDR + TOP_VERBANO_FLASH_CTRL_CORE_SIZE_BYTES`.
 */
#define TOP_VERBANO_FLASH_CTRL_CORE_SIZE_BYTES 0x200
/**
 * Peripheral base address for prim device on flash_ctrl in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_FLASH_CTRL_PRIM_BASE_ADDR 0x41008000

/**
 * Peripheral size for prim device on flash_ctrl in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_FLASH_CTRL_PRIM_BASE_ADDR and
 * `TOP_VERBANO_FLASH_CTRL_PRIM_BASE_ADDR + TOP_VERBANO_FLASH_CTRL_PRIM_SIZE_BYTES`.
 */
#define TOP_VERBANO_FLASH_CTRL_PRIM_SIZE_BYTES 0x80
/**
 * Peripheral base address for mem device on flash_ctrl in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_FLASH_CTRL_MEM_BASE_ADDR 0x20000000

/**
 * Peripheral size for mem device on flash_ctrl in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_FLASH_CTRL_MEM_BASE_ADDR and
 * `TOP_VERBANO_FLASH_CTRL_MEM_BASE_ADDR + TOP_VERBANO_FLASH_CTRL_MEM_SIZE_BYTES`.
 */
#define TOP_VERBANO_FLASH_CTRL_MEM_SIZE_BYTES 0x100000
/**
 * Peripheral base address for regs device on rv_dm in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_RV_DM_REGS_BASE_ADDR 0x41200000

/**
 * Peripheral size for regs device on rv_dm in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_RV_DM_REGS_BASE_ADDR and
 * `TOP_VERBANO_RV_DM_REGS_BASE_ADDR + TOP_VERBANO_RV_DM_REGS_SIZE_BYTES`.
 */
#define TOP_VERBANO_RV_DM_REGS_SIZE_BYTES 0x10
/**
 * Peripheral base address for mem device on rv_dm in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_RV_DM_MEM_BASE_ADDR 0x10000

/**
 * Peripheral size for mem device on rv_dm in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_RV_DM_MEM_BASE_ADDR and
 * `TOP_VERBANO_RV_DM_MEM_BASE_ADDR + TOP_VERBANO_RV_DM_MEM_SIZE_BYTES`.
 */
#define TOP_VERBANO_RV_DM_MEM_SIZE_BYTES 0x1000
/**
 * Peripheral base address for dbg device on rv_dm in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_RV_DM_DBG_BASE_ADDR 0x1000

/**
 * Peripheral size for dbg device on rv_dm in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_RV_DM_DBG_BASE_ADDR and
 * `TOP_VERBANO_RV_DM_DBG_BASE_ADDR + TOP_VERBANO_RV_DM_DBG_SIZE_BYTES`.
 */
#define TOP_VERBANO_RV_DM_DBG_SIZE_BYTES 0x200
/**
 * Peripheral base address for rv_plic in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_RV_PLIC_BASE_ADDR 0x48000000

/**
 * Peripheral size for rv_plic in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_RV_PLIC_BASE_ADDR and
 * `TOP_VERBANO_RV_PLIC_BASE_ADDR + TOP_VERBANO_RV_PLIC_SIZE_BYTES`.
 */
#define TOP_VERBANO_RV_PLIC_SIZE_BYTES 0x8000000
/**
 * Peripheral base address for aes in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_AES_BASE_ADDR 0x41100000

/**
 * Peripheral size for aes in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_AES_BASE_ADDR and
 * `TOP_VERBANO_AES_BASE_ADDR + TOP_VERBANO_AES_SIZE_BYTES`.
 */
#define TOP_VERBANO_AES_SIZE_BYTES 0x100
/**
 * Peripheral base address for hmac in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_HMAC_BASE_ADDR 0x41110000

/**
 * Peripheral size for hmac in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_HMAC_BASE_ADDR and
 * `TOP_VERBANO_HMAC_BASE_ADDR + TOP_VERBANO_HMAC_SIZE_BYTES`.
 */
#define TOP_VERBANO_HMAC_SIZE_BYTES 0x2000
/**
 * Peripheral base address for kmac in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_KMAC_BASE_ADDR 0x41120000

/**
 * Peripheral size for kmac in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_KMAC_BASE_ADDR and
 * `TOP_VERBANO_KMAC_BASE_ADDR + TOP_VERBANO_KMAC_SIZE_BYTES`.
 */
#define TOP_VERBANO_KMAC_SIZE_BYTES 0x1000
/**
 * Peripheral base address for otbn in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_OTBN_BASE_ADDR 0x41130000

/**
 * Peripheral size for otbn in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_OTBN_BASE_ADDR and
 * `TOP_VERBANO_OTBN_BASE_ADDR + TOP_VERBANO_OTBN_SIZE_BYTES`.
 */
#define TOP_VERBANO_OTBN_SIZE_BYTES 0x10000
/**
 * Peripheral base address for keymgr in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_KEYMGR_BASE_ADDR 0x41140000

/**
 * Peripheral size for keymgr in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_KEYMGR_BASE_ADDR and
 * `TOP_VERBANO_KEYMGR_BASE_ADDR + TOP_VERBANO_KEYMGR_SIZE_BYTES`.
 */
#define TOP_VERBANO_KEYMGR_SIZE_BYTES 0x100
/**
 * Peripheral base address for csrng in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_CSRNG_BASE_ADDR 0x41150000

/**
 * Peripheral size for csrng in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_CSRNG_BASE_ADDR and
 * `TOP_VERBANO_CSRNG_BASE_ADDR + TOP_VERBANO_CSRNG_SIZE_BYTES`.
 */
#define TOP_VERBANO_CSRNG_SIZE_BYTES 0x80
/**
 * Peripheral base address for entropy_src in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_ENTROPY_SRC_BASE_ADDR 0x41160000

/**
 * Peripheral size for entropy_src in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_ENTROPY_SRC_BASE_ADDR and
 * `TOP_VERBANO_ENTROPY_SRC_BASE_ADDR + TOP_VERBANO_ENTROPY_SRC_SIZE_BYTES`.
 */
#define TOP_VERBANO_ENTROPY_SRC_SIZE_BYTES 0x100
/**
 * Peripheral base address for edn0 in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_EDN0_BASE_ADDR 0x41170000

/**
 * Peripheral size for edn0 in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_EDN0_BASE_ADDR and
 * `TOP_VERBANO_EDN0_BASE_ADDR + TOP_VERBANO_EDN0_SIZE_BYTES`.
 */
#define TOP_VERBANO_EDN0_SIZE_BYTES 0x80
/**
 * Peripheral base address for edn1 in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_EDN1_BASE_ADDR 0x41180000

/**
 * Peripheral size for edn1 in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_EDN1_BASE_ADDR and
 * `TOP_VERBANO_EDN1_BASE_ADDR + TOP_VERBANO_EDN1_SIZE_BYTES`.
 */
#define TOP_VERBANO_EDN1_SIZE_BYTES 0x80
/**
 * Peripheral base address for regs device on sram_ctrl_main in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_SRAM_CTRL_MAIN_REGS_BASE_ADDR 0x411C0000

/**
 * Peripheral size for regs device on sram_ctrl_main in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_SRAM_CTRL_MAIN_REGS_BASE_ADDR and
 * `TOP_VERBANO_SRAM_CTRL_MAIN_REGS_BASE_ADDR + TOP_VERBANO_SRAM_CTRL_MAIN_REGS_SIZE_BYTES`.
 */
#define TOP_VERBANO_SRAM_CTRL_MAIN_REGS_SIZE_BYTES 0x40
/**
 * Peripheral base address for ram device on sram_ctrl_main in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_SRAM_CTRL_MAIN_RAM_BASE_ADDR 0x10000000

/**
 * Peripheral size for ram device on sram_ctrl_main in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_SRAM_CTRL_MAIN_RAM_BASE_ADDR and
 * `TOP_VERBANO_SRAM_CTRL_MAIN_RAM_BASE_ADDR + TOP_VERBANO_SRAM_CTRL_MAIN_RAM_SIZE_BYTES`.
 */
#define TOP_VERBANO_SRAM_CTRL_MAIN_RAM_SIZE_BYTES 0x20000
/**
 * Peripheral base address for regs device on rom_ctrl in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_ROM_CTRL_REGS_BASE_ADDR 0x411E0000

/**
 * Peripheral size for regs device on rom_ctrl in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_ROM_CTRL_REGS_BASE_ADDR and
 * `TOP_VERBANO_ROM_CTRL_REGS_BASE_ADDR + TOP_VERBANO_ROM_CTRL_REGS_SIZE_BYTES`.
 */
#define TOP_VERBANO_ROM_CTRL_REGS_SIZE_BYTES 0x80
/**
 * Peripheral base address for rom device on rom_ctrl in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_ROM_CTRL_ROM_BASE_ADDR 0x8000

/**
 * Peripheral size for rom device on rom_ctrl in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_ROM_CTRL_ROM_BASE_ADDR and
 * `TOP_VERBANO_ROM_CTRL_ROM_BASE_ADDR + TOP_VERBANO_ROM_CTRL_ROM_SIZE_BYTES`.
 */
#define TOP_VERBANO_ROM_CTRL_ROM_SIZE_BYTES 0x8000
/**
 * Peripheral base address for cfg device on rv_core_ibex in top verbano.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_VERBANO_RV_CORE_IBEX_CFG_BASE_ADDR 0x411F0000

/**
 * Peripheral size for cfg device on rv_core_ibex in top verbano.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_VERBANO_RV_CORE_IBEX_CFG_BASE_ADDR and
 * `TOP_VERBANO_RV_CORE_IBEX_CFG_BASE_ADDR + TOP_VERBANO_RV_CORE_IBEX_CFG_SIZE_BYTES`.
 */
#define TOP_VERBANO_RV_CORE_IBEX_CFG_SIZE_BYTES 0x100

/**
 * MMIO Region
 *
 * MMIO region excludes any memory that is separate from the module
 * configuration space, i.e. ROM, main SRAM, and flash are excluded but
 * retention SRAM, spi_device memory, or usbdev memory are included.
 */
#define TOP_VERBANO_MMIO_BASE_ADDR 0x40000000
#define TOP_VERBANO_MMIO_SIZE_BYTES 0x10000000

#endif  // __ASSEMBLER__

#endif  // OPENTITAN_HW_TOP_VERBANO_SW_AUTOGEN_TOP_VERBANO_MEMORY_H_
