// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_RV_PLIC_AUTOGEN_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_RV_PLIC_AUTOGEN_H_

// This file is auto-generated.

/**
 * @file
 * @brief <a href="/hw/ip/rv_plic/doc/">RV_PLIC</a> Device Interface Functions
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
 * A handle to rv_plic.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_rv_plic {
  /**
   * The base address for the rv_plic hardware registers.
   */
  mmio_region_t base_addr;
} dif_rv_plic_t;

/**
 * Creates a new handle for a(n) rv_plic peripheral.
 *
 * This function does not actuate the hardware.
 *
 * @param base_addr The MMIO base address of the rv_plic peripheral.
 * @param[out] rv_plic Out param for the initialized handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_plic_init(mmio_region_t base_addr, dif_rv_plic_t *rv_plic);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_RV_PLIC_AUTOGEN_H_
