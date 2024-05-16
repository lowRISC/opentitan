// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_TOP_DARJEELING_SW_AUTOGEN_TOP_DARJEELING_SOC_MBX_H_
#define OPENTITAN_HW_TOP_DARJEELING_SW_AUTOGEN_TOP_DARJEELING_SOC_MBX_H_

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
 * Peripheral base address for soc device on mbx0 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_MBX0_SOC_BASE_ADDR 0x1465000u

/**
 * Peripheral size for soc device on mbx0 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_MBX0_SOC_BASE_ADDR and
 * `TOP_DARJEELING_MBX0_SOC_BASE_ADDR + TOP_DARJEELING_MBX0_SOC_SIZE_BYTES`.
 */
#define TOP_DARJEELING_MBX0_SOC_SIZE_BYTES 0x20u

/**
 * Peripheral base address for soc device on mbx1 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_MBX1_SOC_BASE_ADDR 0x1465100u

/**
 * Peripheral size for soc device on mbx1 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_MBX1_SOC_BASE_ADDR and
 * `TOP_DARJEELING_MBX1_SOC_BASE_ADDR + TOP_DARJEELING_MBX1_SOC_SIZE_BYTES`.
 */
#define TOP_DARJEELING_MBX1_SOC_SIZE_BYTES 0x20u

/**
 * Peripheral base address for soc device on mbx2 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_MBX2_SOC_BASE_ADDR 0x1465200u

/**
 * Peripheral size for soc device on mbx2 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_MBX2_SOC_BASE_ADDR and
 * `TOP_DARJEELING_MBX2_SOC_BASE_ADDR + TOP_DARJEELING_MBX2_SOC_SIZE_BYTES`.
 */
#define TOP_DARJEELING_MBX2_SOC_SIZE_BYTES 0x20u

/**
 * Peripheral base address for soc device on mbx3 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_MBX3_SOC_BASE_ADDR 0x1465300u

/**
 * Peripheral size for soc device on mbx3 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_MBX3_SOC_BASE_ADDR and
 * `TOP_DARJEELING_MBX3_SOC_BASE_ADDR + TOP_DARJEELING_MBX3_SOC_SIZE_BYTES`.
 */
#define TOP_DARJEELING_MBX3_SOC_SIZE_BYTES 0x20u

/**
 * Peripheral base address for soc device on mbx4 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_MBX4_SOC_BASE_ADDR 0x1465400u

/**
 * Peripheral size for soc device on mbx4 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_MBX4_SOC_BASE_ADDR and
 * `TOP_DARJEELING_MBX4_SOC_BASE_ADDR + TOP_DARJEELING_MBX4_SOC_SIZE_BYTES`.
 */
#define TOP_DARJEELING_MBX4_SOC_SIZE_BYTES 0x20u

/**
 * Peripheral base address for soc device on mbx5 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_MBX5_SOC_BASE_ADDR 0x1465500u

/**
 * Peripheral size for soc device on mbx5 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_MBX5_SOC_BASE_ADDR and
 * `TOP_DARJEELING_MBX5_SOC_BASE_ADDR + TOP_DARJEELING_MBX5_SOC_SIZE_BYTES`.
 */
#define TOP_DARJEELING_MBX5_SOC_SIZE_BYTES 0x20u

/**
 * Peripheral base address for soc device on mbx6 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_MBX6_SOC_BASE_ADDR 0x1465600u

/**
 * Peripheral size for soc device on mbx6 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_MBX6_SOC_BASE_ADDR and
 * `TOP_DARJEELING_MBX6_SOC_BASE_ADDR + TOP_DARJEELING_MBX6_SOC_SIZE_BYTES`.
 */
#define TOP_DARJEELING_MBX6_SOC_SIZE_BYTES 0x20u

/**
 * Peripheral base address for soc device on mbx_pcie0 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_MBX_PCIE0_SOC_BASE_ADDR 0x1460100u

/**
 * Peripheral size for soc device on mbx_pcie0 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_MBX_PCIE0_SOC_BASE_ADDR and
 * `TOP_DARJEELING_MBX_PCIE0_SOC_BASE_ADDR + TOP_DARJEELING_MBX_PCIE0_SOC_SIZE_BYTES`.
 */
#define TOP_DARJEELING_MBX_PCIE0_SOC_SIZE_BYTES 0x20u

/**
 * Peripheral base address for soc device on mbx_pcie1 in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_MBX_PCIE1_SOC_BASE_ADDR 0x1460200u

/**
 * Peripheral size for soc device on mbx_pcie1 in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_MBX_PCIE1_SOC_BASE_ADDR and
 * `TOP_DARJEELING_MBX_PCIE1_SOC_BASE_ADDR + TOP_DARJEELING_MBX_PCIE1_SOC_SIZE_BYTES`.
 */
#define TOP_DARJEELING_MBX_PCIE1_SOC_SIZE_BYTES 0x20u








/**
 * MMIO Region
 *
 * MMIO region excludes any memory that is separate from the module
 * configuration space, i.e. ROM, main SRAM, and flash are excluded but
 * retention SRAM, spi_device memory, or usbdev memory are included.
 */
#define TOP_DARJEELING_MMIO_BASE_ADDR 0x1460100u
#define TOP_DARJEELING_MMIO_SIZE_BYTES 0x5520u

// Header Extern Guard
#ifdef __cplusplus
}  // extern "C"
#endif

#endif  // OPENTITAN_HW_TOP_DARJEELING_SW_AUTOGEN_TOP_DARJEELING_SOC_MBX_H_
