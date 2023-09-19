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
  /**
   * Fatal external alert channel 0
   */
  kDifSocProxyAlertFatalAlertExternal0 = 1,
  /**
   * Fatal external alert channel 1
   */
  kDifSocProxyAlertFatalAlertExternal1 = 2,
  /**
   * Fatal external alert channel 2
   */
  kDifSocProxyAlertFatalAlertExternal2 = 3,
  /**
   * Fatal external alert channel 3
   */
  kDifSocProxyAlertFatalAlertExternal3 = 4,
  /**
   * Recoverable external alert channel 0
   */
  kDifSocProxyAlertRecovAlertExternal0 = 5,
  /**
   * Recoverable external alert channel 1
   */
  kDifSocProxyAlertRecovAlertExternal1 = 6,
  /**
   * Recoverable external alert channel 2
   */
  kDifSocProxyAlertRecovAlertExternal2 = 7,
  /**
   * Recoverable external alert channel 3
   */
  kDifSocProxyAlertRecovAlertExternal3 = 8,
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

/**
 * A soc_proxy interrupt request type.
 */
typedef enum dif_soc_proxy_irq {
  /**
   * External interrupt request
   */
  kDifSocProxyIrqExternal0 = 0,
  kDifSocProxyIrqExternal1 = 1,
  kDifSocProxyIrqExternal2 = 2,
  kDifSocProxyIrqExternal3 = 3,
  kDifSocProxyIrqExternal4 = 4,
  kDifSocProxyIrqExternal5 = 5,
  kDifSocProxyIrqExternal6 = 6,
  kDifSocProxyIrqExternal7 = 7,
} dif_soc_proxy_irq_t;

/**
 * A snapshot of the state of the interrupts for this IP.
 *
 * This is an opaque type, to be used with the `dif_soc_proxy_irq_get_state()`
 * and `dif_soc_proxy_irq_acknowledge_state()` functions.
 */
typedef uint32_t dif_soc_proxy_irq_state_snapshot_t;

/**
 * Returns the type of a given interrupt (i.e., event or status) for this IP.
 *
 * @param soc_proxy A soc_proxy handle.
 * @param irq An interrupt request.
 * @param[out] type Out-param for the interrupt type.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_soc_proxy_irq_get_type(const dif_soc_proxy_t *soc_proxy,
                                        dif_soc_proxy_irq_t irq,
                                        dif_irq_type_t *type);

/**
 * Returns the state of all interrupts (i.e., pending or not) for this IP.
 *
 * @param soc_proxy A soc_proxy handle.
 * @param[out] snapshot Out-param for interrupt state snapshot.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_soc_proxy_irq_get_state(
    const dif_soc_proxy_t *soc_proxy,
    dif_soc_proxy_irq_state_snapshot_t *snapshot);

/**
 * Returns whether a particular interrupt is currently pending.
 *
 * @param soc_proxy A soc_proxy handle.
 * @param irq An interrupt request.
 * @param[out] is_pending Out-param for whether the interrupt is pending.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_soc_proxy_irq_is_pending(const dif_soc_proxy_t *soc_proxy,
                                          dif_soc_proxy_irq_t irq,
                                          bool *is_pending);

/**
 * Acknowledges all interrupts that were pending at the time of the state
 * snapshot.
 *
 * @param soc_proxy A soc_proxy handle.
 * @param snapshot Interrupt state snapshot.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_soc_proxy_irq_acknowledge_state(
    const dif_soc_proxy_t *soc_proxy,
    dif_soc_proxy_irq_state_snapshot_t snapshot);

/**
 * Acknowledges all interrupts, indicating to the hardware that all
 * interrupts have been successfully serviced.
 *
 * @param soc_proxy A soc_proxy handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_soc_proxy_irq_acknowledge_all(
    const dif_soc_proxy_t *soc_proxy);

/**
 * Acknowledges a particular interrupt, indicating to the hardware that it has
 * been successfully serviced.
 *
 * @param soc_proxy A soc_proxy handle.
 * @param irq An interrupt request.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_soc_proxy_irq_acknowledge(const dif_soc_proxy_t *soc_proxy,
                                           dif_soc_proxy_irq_t irq);

/**
 * Forces a particular interrupt, causing it to be serviced as if hardware had
 * asserted it.
 *
 * @param soc_proxy A soc_proxy handle.
 * @param irq An interrupt request.
 * @param val Value to be set.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_soc_proxy_irq_force(const dif_soc_proxy_t *soc_proxy,
                                     dif_soc_proxy_irq_t irq, const bool val);

/**
 * A snapshot of the enablement state of the interrupts for this IP.
 *
 * This is an opaque type, to be used with the
 * `dif_soc_proxy_irq_disable_all()` and `dif_soc_proxy_irq_restore_all()`
 * functions.
 */
typedef uint32_t dif_soc_proxy_irq_enable_snapshot_t;

/**
 * Checks whether a particular interrupt is currently enabled or disabled.
 *
 * @param soc_proxy A soc_proxy handle.
 * @param irq An interrupt request.
 * @param[out] state Out-param toggle state of the interrupt.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_soc_proxy_irq_get_enabled(const dif_soc_proxy_t *soc_proxy,
                                           dif_soc_proxy_irq_t irq,
                                           dif_toggle_t *state);

/**
 * Sets whether a particular interrupt is currently enabled or disabled.
 *
 * @param soc_proxy A soc_proxy handle.
 * @param irq An interrupt request.
 * @param state The new toggle state for the interrupt.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_soc_proxy_irq_set_enabled(const dif_soc_proxy_t *soc_proxy,
                                           dif_soc_proxy_irq_t irq,
                                           dif_toggle_t state);

/**
 * Disables all interrupts, optionally snapshotting all enable states for later
 * restoration.
 *
 * @param soc_proxy A soc_proxy handle.
 * @param[out] snapshot Out-param for the snapshot; may be `NULL`.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_soc_proxy_irq_disable_all(
    const dif_soc_proxy_t *soc_proxy,
    dif_soc_proxy_irq_enable_snapshot_t *snapshot);

/**
 * Restores interrupts from the given (enable) snapshot.
 *
 * @param soc_proxy A soc_proxy handle.
 * @param snapshot A snapshot to restore from.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_soc_proxy_irq_restore_all(
    const dif_soc_proxy_t *soc_proxy,
    const dif_soc_proxy_irq_enable_snapshot_t *snapshot);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_IP_SOC_PROXY_DIF_AUTOGEN_DIF_SOC_PROXY_AUTOGEN_H_
