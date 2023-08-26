// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_IP_SOC_PROXY_DIF_AUTOGEN_DIF_SOC_PROXY_AUTOGEN_H_
#define OPENTITAN_SW_IP_SOC_PROXY_DIF_AUTOGEN_DIF_SOC_PROXY_AUTOGEN_H_

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

/**
 * @file
 * @brief <a href="/hw/ip/soc_proxy/doc/">SOC_PROXY</a> Device Interface
 * Functions
 */

#include <stdbool.h>
#include <stdint.h>

#include "sw/ip/base/dif/dif_base.h"
#include "sw/lib/sw/device/base/macros.h"
#include "sw/lib/sw/device/base/mmio.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * A handle to soc_proxy.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_soc_proxy {
  /**
   * The base address for the soc_proxy hardware registers.
   */
  mmio_region_t base_addr;
} dif_soc_proxy_t;

/**
 * Creates a new handle for a(n) soc_proxy peripheral.
 *
 * This function does not actuate the hardware.
 *
 * @param base_addr The MMIO base address of the soc_proxy peripheral.
 * @param[out] soc_proxy Out param for the initialized handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_soc_proxy_init(mmio_region_t base_addr,
                                dif_soc_proxy_t *soc_proxy);

/**
 * A soc_proxy alert type.
 */
typedef enum dif_soc_proxy_alert {
  /**
   * Fatal bus integrity alert
   */
  kDifSocProxyAlertFatalAlertIntg = 0,
} dif_soc_proxy_alert_t;

/**
 * Forces a particular alert, causing it to be escalated as if the hardware
 * had raised it.
 *
 * @param soc_proxy A soc_proxy handle.
 * @param alert The alert to force.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_soc_proxy_alert_force(const dif_soc_proxy_t *soc_proxy,
                                       dif_soc_proxy_alert_t alert);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_IP_SOC_PROXY_DIF_AUTOGEN_DIF_SOC_PROXY_AUTOGEN_H_
