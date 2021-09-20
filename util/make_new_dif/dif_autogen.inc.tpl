// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

<%doc>
    This file is the "auto-generated DIF library header template", which
    provides some mandatory DIFs prototypes, that are similar across all IPs.
    This template is rendered into a .inc file that is included by the semi-
    auto-generated DIF header file (see util/make_new_dif/dif_template.h.tpl).
    Note, since this template is designed to manifest as a non-standalone header
    it has the file extension, .inc.

    For more information, see: https://github.com/lowRISC/opentitan/issues/8142

    Note, this template requires the following Python objects to be passed:

    1. ip: See util/make_new_dif.py for the definition of the `ip` obj.
    2. list[irq]: See util/make_new_dif.py for the definition of the `irq` obj.
</%doc>

// This file is auto-generated.

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_${ip.name_upper}_AUTOGEN_INC_
#define OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_${ip.name_upper}_AUTOGEN_INC_

/**
 * @file
 * @brief <a href="/hw/ip/${ip.name_snake}/doc/">${ip.name_upper}</a> Device Interface Functions
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
 * A handle to ${ip.name_snake}.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_${ip.name_snake} { 
  /**
   * The base address for the ${ip.name_upper} hardware registers.
   */
  mmio_region_t base_addr;
} dif_${ip.name_snake}_t;

/**
 * A ${ip.name_snake} interrupt request type.
 */
typedef enum dif_${ip.name_snake}_irq {
% for irq in irqs:
  /**
   * ${irq.description}
   */
  kDif${ip.name_camel}Irq${irq.name_camel} = ${loop.index},
% endfor
} dif_${ip.name_snake}_irq_t;

/**
 * A snapshot of the state of the interrupts for this IP.
 *
 * This is an opaque type, to be used with the `dif_${ip.name_snake}_irq_get_state()`
 * function.
 */
typedef uint32_t dif_${ip.name_snake}_irq_state_snapshot_t;

/**
 * A snapshot of the enablement state of the interrupts for this IP.
 *
 * This is an opaque type, to be used with the
 * `dif_${ip.name_snake}_irq_disable_all()` and `dif_${ip.name_snake}_irq_restore_all()`
 * functions.
 */
typedef uint32_t dif_${ip.name_snake}_irq_enable_snapshot_t;

/**
 * Returns whether a particular interrupt is currently pending.
 *
 * @param ${ip.name_snake} A ${ip.name_snake} handle.
 * @param irq An interrupt request.
 * @param[out] is_pending Out-param for whether the interrupt is pending.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_${ip.name_snake}_irq_get_state(
  const dif_${ip.name_snake}_t *${ip.name_snake},
  dif_${ip.name_snake}_irq_state_snapshot_t *snapshot);

/**
 * Returns whether a particular interrupt is currently pending.
 *
 * @param ${ip.name_snake} A ${ip.name_snake} handle.
 * @param irq An interrupt request.
 * @param[out] is_pending Out-param for whether the interrupt is pending.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_${ip.name_snake}_irq_is_pending(
  const dif_${ip.name_snake}_t *${ip.name_snake},
  dif_${ip.name_snake}_irq_t irq,
  bool *is_pending);

/**
 * Acknowledges a particular interrupt, indicating to the hardware that it has
 * been successfully serviced.
 *
 * @param ${ip.name_snake} A ${ip.name_snake} handle.
 * @param irq An interrupt request.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_${ip.name_snake}_irq_acknowledge(
  const dif_${ip.name_snake}_t *${ip.name_snake},
  dif_${ip.name_snake}_irq_t irq);

/**
 * Checks whether a particular interrupt is currently enabled or disabled.
 *
 * @param ${ip.name_snake} A ${ip.name_snake} handle.
 * @param irq An interrupt request.
 * @param[out] state Out-param toggle state of the interrupt.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_${ip.name_snake}_irq_get_enabled(
  const dif_${ip.name_snake}_t *${ip.name_snake},
  dif_${ip.name_snake}_irq_t irq,
  dif_toggle_t *state);

/**
 * Sets whether a particular interrupt is currently enabled or disabled.
 *
 * @param ${ip.name_snake} A ${ip.name_snake} handle.
 * @param irq An interrupt request.
 * @param state The new toggle state for the interrupt.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_${ip.name_snake}_irq_set_enabled(
  const dif_${ip.name_snake}_t *${ip.name_snake},
  dif_${ip.name_snake}_irq_t irq,
  dif_toggle_t state);

/**
 * Forces a particular interrupt, causing it to be serviced as if hardware had
 * asserted it.
 *
 * @param ${ip.name_snake} A ${ip.name_snake} handle.
 * @param irq An interrupt request.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_${ip.name_snake}_irq_force(
  const dif_${ip.name_snake}_t *${ip.name_snake},
  dif_${ip.name_snake}_irq_t irq);

/**
 * Disables all interrupts, optionally snapshotting all enable states for later
 * restoration.
 *
 * @param ${ip.name_snake} A ${ip.name_snake} handle.
 * @param[out] snapshot Out-param for the snapshot; may be `NULL`.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_${ip.name_snake}_irq_disable_all(
  const dif_${ip.name_snake}_t *${ip.name_snake},
  dif_${ip.name_snake}_irq_enable_snapshot_t *snapshot);

/**
 * Restores interrupts from the given (enable) snapshot.
 *
 * @param ${ip.name_snake} A ${ip.name_snake} handle.
 * @param snapshot A snapshot to restore from.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_${ip.name_snake}_irq_restore_all(
  const dif_${ip.name_snake}_t *${ip.name_snake},
  const dif_${ip.name_snake}_irq_enable_snapshot_t *snapshot);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_${ip.name_upper}_AUTOGEN_INC_
