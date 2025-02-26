// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
// util/topgen.py -t hw/top_darjeeling/data/top_darjeeling.hjson
// -o hw/top_darjeeling

#ifndef OPENTITAN_HW_TOP_DARJEELING_SW_AUTOGEN_TOP_DARJEELING_SOC_DBG_H_
#define OPENTITAN_HW_TOP_DARJEELING_SW_AUTOGEN_TOP_DARJEELING_SOC_DBG_H_

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
#define TOP_DARJEELING_SOC_DBG_LC_CTRL_DMI_BASE_ADDR 0x3000u

/**
 * Peripheral size for dmi device on lc_ctrl in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_SOC_DBG_LC_CTRL_DMI_BASE_ADDR and
 * `TOP_DARJEELING_SOC_DBG_LC_CTRL_DMI_BASE_ADDR + TOP_DARJEELING_SOC_DBG_LC_CTRL_DMI_SIZE_BYTES`.
 */
#define TOP_DARJEELING_SOC_DBG_LC_CTRL_DMI_SIZE_BYTES 0x1000u

/**
 * Peripheral base address for dbg device on rv_dm in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_SOC_DBG_RV_DM_DBG_BASE_ADDR 0x0u

/**
 * Peripheral size for dbg device on rv_dm in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_SOC_DBG_RV_DM_DBG_BASE_ADDR and
 * `TOP_DARJEELING_SOC_DBG_RV_DM_DBG_BASE_ADDR + TOP_DARJEELING_SOC_DBG_RV_DM_DBG_SIZE_BYTES`.
 */
#define TOP_DARJEELING_SOC_DBG_RV_DM_DBG_SIZE_BYTES 0x200u

/**
 * Peripheral base address for soc device on mbx_jtag in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_SOC_DBG_MBX_JTAG_SOC_BASE_ADDR 0x2200u

/**
 * Peripheral size for soc device on mbx_jtag in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_SOC_DBG_MBX_JTAG_SOC_BASE_ADDR and
 * `TOP_DARJEELING_SOC_DBG_MBX_JTAG_SOC_BASE_ADDR + TOP_DARJEELING_SOC_DBG_MBX_JTAG_SOC_SIZE_BYTES`.
 */
#define TOP_DARJEELING_SOC_DBG_MBX_JTAG_SOC_SIZE_BYTES 0x20u

/**
 * Peripheral base address for jtag device on soc_dbg_ctrl in top darjeeling.
 *
 * This should be used with #mmio_region_from_addr to access the memory-mapped
 * registers associated with the peripheral (usually via a DIF).
 */
#define TOP_DARJEELING_SOC_DBG_SOC_DBG_CTRL_JTAG_BASE_ADDR 0x2300u

/**
 * Peripheral size for jtag device on soc_dbg_ctrl in top darjeeling.
 *
 * This is the size (in bytes) of the peripheral's reserved memory area. All
 * memory-mapped registers associated with this peripheral should have an
 * address between #TOP_DARJEELING_SOC_DBG_SOC_DBG_CTRL_JTAG_BASE_ADDR and
 * `TOP_DARJEELING_SOC_DBG_SOC_DBG_CTRL_JTAG_BASE_ADDR + TOP_DARJEELING_SOC_DBG_SOC_DBG_CTRL_JTAG_SIZE_BYTES`.
 */
#define TOP_DARJEELING_SOC_DBG_SOC_DBG_CTRL_JTAG_SIZE_BYTES 0x20u



// Header Extern Guard
#ifdef __cplusplus
}  // extern "C"
#endif

#endif  // OPENTITAN_HW_TOP_DARJEELING_SW_AUTOGEN_TOP_DARJEELING_SOC_DBG_H_
