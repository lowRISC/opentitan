// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_CLKMGR_AUTOGEN_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_CLKMGR_AUTOGEN_H_

// This file is auto-generated.

/**
 * @file
 * @brief <a href="/hw/ip/clkmgr/doc/">CLKMGR</a> Device Interface Functions
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
 * A handle to clkmgr.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_clkmgr {
  /**
   * The base address for the clkmgr hardware registers.
   */
  mmio_region_t base_addr;
} dif_clkmgr_t;

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_CLKMGR_AUTOGEN_H_
