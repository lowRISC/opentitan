// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_MBX_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_MBX_H_

/**
 * @file
 * @brief <a href="/hw/ip/mbx/doc/">DOE Mailbox</a> Device Interface
 * Functions
 */
#include <stdint.h>

#include "sw/device/lib/dif/autogen/dif_mbx_autogen.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Inbound and outbound range for DOE Mailbox.
 */
typedef struct dif_mbx_range_config {
  uint32_t imbx_base_addr;
  uint32_t imbx_limit_addr;
  uint32_t ombx_base_addr;
  uint32_t ombx_limit_addr;
} dif_mbx_range_config_t;

/**
 * Configures the mailbox inbound and outbound ranges and validates them.
 *
 * @param mbx A DOE Mailbox handle.
 * @param config Mailbox inbound and outbound range configuration.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_mbx_range_set(const dif_mbx_t *mbx,
                               dif_mbx_range_config_t config);

/**
 * Reads the mailbox range configuration.
 *
 * @param mbx A DOE Mailbox handle.
 * @param[out] config Mailbox inbound and outbound range configuration.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_mbx_range_get(const dif_mbx_t *mbx,
                               dif_mbx_range_config_t *config);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_MBX_H_
