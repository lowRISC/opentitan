// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_IP_SOCDBG_CTRL_DIF_AUTOGEN_DIF_SOC_PROXY_AUTOGEN_H_
#define OPENTITAN_SW_IP_SOCDBG_CTRL_DIF_AUTOGEN_DIF_SOC_PROXY_AUTOGEN_H_

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
   * Fatal external alert channel 4
   */
  kDifSocProxyAlertFatalAlertExternal4 = 5,
  /**
   * Fatal external alert channel 5
   */
  kDifSocProxyAlertFatalAlertExternal5 = 6,
  /**
   * Fatal external alert channel 6
   */
  kDifSocProxyAlertFatalAlertExternal6 = 7,
  /**
   * Fatal external alert channel 7
   */
  kDifSocProxyAlertFatalAlertExternal7 = 8,
  /**
   * Fatal external alert channel 8
   */
  kDifSocProxyAlertFatalAlertExternal8 = 9,
  /**
   * Fatal external alert channel 9
   */
  kDifSocProxyAlertFatalAlertExternal9 = 10,
  /**
   * Fatal external alert channel 10
   */
  kDifSocProxyAlertFatalAlertExternal10 = 11,
  /**
   * Fatal external alert channel 11
   */
  kDifSocProxyAlertFatalAlertExternal11 = 12,
  /**
   * Fatal external alert channel 12
   */
  kDifSocProxyAlertFatalAlertExternal12 = 13,
  /**
   * Fatal external alert channel 13
   */
  kDifSocProxyAlertFatalAlertExternal13 = 14,
  /**
   * Fatal external alert channel 14
   */
  kDifSocProxyAlertFatalAlertExternal14 = 15,
  /**
   * Fatal external alert channel 15
   */
  kDifSocProxyAlertFatalAlertExternal15 = 16,
  /**
   * Fatal external alert channel 16
   */
  kDifSocProxyAlertFatalAlertExternal16 = 17,
  /**
   * Fatal external alert channel 17
   */
  kDifSocProxyAlertFatalAlertExternal17 = 18,
  /**
   * Fatal external alert channel 18
   */
  kDifSocProxyAlertFatalAlertExternal18 = 19,
  /**
   * Fatal external alert channel 19
   */
  kDifSocProxyAlertFatalAlertExternal19 = 20,
  /**
   * Fatal external alert channel 20
   */
  kDifSocProxyAlertFatalAlertExternal20 = 21,
  /**
   * Fatal external alert channel 21
   */
  kDifSocProxyAlertFatalAlertExternal21 = 22,
  /**
   * Fatal external alert channel 22
   */
  kDifSocProxyAlertFatalAlertExternal22 = 23,
  /**
   * Fatal external alert channel 23
   */
  kDifSocProxyAlertFatalAlertExternal23 = 24,
  /**
   * Recoverable external alert channel 0
   */
  kDifSocProxyAlertRecovAlertExternal0 = 25,
  /**
   * Recoverable external alert channel 1
   */
  kDifSocProxyAlertRecovAlertExternal1 = 26,
  /**
   * Recoverable external alert channel 2
   */
  kDifSocProxyAlertRecovAlertExternal2 = 27,
  /**
   * Recoverable external alert channel 3
   */
  kDifSocProxyAlertRecovAlertExternal3 = 28,
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
  kDifSocProxyIrqExternal8 = 8,
  kDifSocProxyIrqExternal9 = 9,
  kDifSocProxyIrqExternal10 = 10,
  kDifSocProxyIrqExternal11 = 11,
  kDifSocProxyIrqExternal12 = 12,
  kDifSocProxyIrqExternal13 = 13,
  kDifSocProxyIrqExternal14 = 14,
  kDifSocProxyIrqExternal15 = 15,
  kDifSocProxyIrqExternal16 = 16,
  kDifSocProxyIrqExternal17 = 17,
  kDifSocProxyIrqExternal18 = 18,
  kDifSocProxyIrqExternal19 = 19,
  kDifSocProxyIrqExternal20 = 20,
  kDifSocProxyIrqExternal21 = 21,
  kDifSocProxyIrqExternal22 = 22,
  kDifSocProxyIrqExternal23 = 23,
  kDifSocProxyIrqExternal24 = 24,
  kDifSocProxyIrqExternal25 = 25,
  kDifSocProxyIrqExternal26 = 26,
  kDifSocProxyIrqExternal27 = 27,
  kDifSocProxyIrqExternal28 = 28,
  kDifSocProxyIrqExternal29 = 29,
  kDifSocProxyIrqExternal30 = 30,
  kDifSocProxyIrqExternal31 = 31,
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

#endif  // OPENTITAN_SW_IP_SOCDBG_CTRL_DIF_AUTOGEN_DIF_SOC_PROXY_AUTOGEN_H_
