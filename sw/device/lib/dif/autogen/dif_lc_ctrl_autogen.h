// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_LC_CTRL_AUTOGEN_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_LC_CTRL_AUTOGEN_H_

// This file is auto-generated.

/**
 * @file
 * @brief <a href="/hw/ip/lc_ctrl/doc/">LC_CTRL</a> Device Interface Functions
 */

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * A handle to lc_ctrl.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_lc_ctrl {
  /**
   * The base address for the lc_ctrl hardware registers.
   */
  mmio_region_t base_addr;
} dif_lc_ctrl_t;

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_LC_CTRL_AUTOGEN_H_
