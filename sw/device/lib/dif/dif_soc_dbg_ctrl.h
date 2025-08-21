// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_SOC_DBG_CTRL_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_SOC_DBG_CTRL_H_

/**
 * @file
 * @brief <a href="/book/hw/ip/soc_dbg_ctrl/">SoC Debug Control</a> Device
 * Interface Functions
 */

#include "hw/top/soc_dbg_ctrl_regs.h"  // Generated.

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Valid debug categories. These values MUST be kept in sync with the
 * `dbg_category_e` enum in `hw/ip/soc_dbg_ctrl/rtl/soc_dbg_ctrl_pkg.sv`.
 */
typedef enum dif_soc_dbg_ctrl_debug_category {
  kDebugCategoryLocked = 0x50,  // 7'b1010000
  kDebugCategory2 = 0x4D,       // 7'b1001101
  kDebugCategory3 = 0x0A,       // 7'b0001010
  kDebugCategory4 = 0x63        // 7'b1100011
} dif_soc_dbg_ctrl_debug_category_t;

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_SOC_DBG_CTRL_H_
