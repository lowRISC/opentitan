// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_TOP_DARJEELING_SW_AUTOGEN_TOP_DARJEELING_SOC_DBG_H_
#define OPENTITAN_HW_TOP_DARJEELING_SW_AUTOGEN_TOP_DARJEELING_SOC_DBG_H_

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
 * Peripheral base address for dmi device on lc_ctrl in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_LC_CTRL_DMI_BASE_ADDR 0x20000u

/**
 * Peripheral size for dmi device on lc_ctrl in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_LC_CTRL_DMI_BASE_ADDR and
 * `TOP_DARJEELING_LC_CTRL_DMI_BASE_ADDR + TOP_DARJEELING_LC_CTRL_DMI_SIZE_BYTES`.
 */
#define TOP_DARJEELING_LC_CTRL_DMI_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for dbg device on rv_dm in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_RV_DM_DBG_BASE_ADDR 0x0u

/**
 * Peripheral size for dbg device on rv_dm in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_RV_DM_DBG_BASE_ADDR and
 * `TOP_DARJEELING_RV_DM_DBG_BASE_ADDR + TOP_DARJEELING_RV_DM_DBG_SIZE_BYTES`.
 */
#define TOP_DARJEELING_RV_DM_DBG_SIZE_BYTES 0x200u

/**
 * Peripheral base address for soc device on mbx_jtag in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_MBX_JTAG_SOC_BASE_ADDR 0x1000u

/**
 * Peripheral size for soc device on mbx_jtag in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_MBX_JTAG_SOC_BASE_ADDR and
 * `TOP_DARJEELING_MBX_JTAG_SOC_BASE_ADDR + TOP_DARJEELING_MBX_JTAG_SOC_SIZE_BYTES`.
 */
#define TOP_DARJEELING_MBX_JTAG_SOC_SIZE_BYTES 0x20u








/**
 * MMIO Region
 *
 * MMIO region excludes any memory that is separate from the module
 * configuration space, i.e. ROM, main SRAM, and flash are excluded but
 * retention SRAM, spi_device memory, or usbdev memory are included.
 */
#define TOP_DARJEELING_MMIO_BASE_ADDR 0x1000u
#define TOP_DARJEELING_MMIO_SIZE_BYTES 0x20000u

// Header Extern Guard
#ifdef __cplusplus
}  // extern "C"
#endif

#endif  // OPENTITAN_HW_TOP_DARJEELING_SW_AUTOGEN_TOP_DARJEELING_SOC_DBG_H_
