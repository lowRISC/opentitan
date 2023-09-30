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
</%doc>

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_${ip.name_upper}_AUTOGEN_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_${ip.name_upper}_AUTOGEN_H_

${autogen_banner}

/**
 * @file
 * @brief <a href="/book/hw/ip/${ip.name_snake}/">${ip.name_upper}</a> Device Interface Functions
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
   * The base address for the ${ip.name_snake} hardware registers.
   */
  mmio_region_t base_addr;
} dif_${ip.name_snake}_t;

/**
 * Creates a new handle for a(n) ${ip.name_snake} peripheral.
 *
 * This function does not actuate the hardware.
 *
 * @param base_addr The MMIO base address of the ${ip.name_snake} peripheral.
 * @param[out] ${ip.name_snake} Out param for the initialized handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_${ip.name_snake}_init(
  mmio_region_t base_addr,
  dif_${ip.name_snake}_t *${ip.name_snake});

% if ip.alerts:
  /**
   * A ${ip.name_snake} alert type.
   */
  typedef enum dif_${ip.name_snake}_alert {
  % for alert in ip.alerts:
    /**
     * ${alert.description}
     */
      kDif${ip.name_camel}Alert${alert.name_camel} = ${loop.index},
  % endfor
  } dif_${ip.name_snake}_alert_t;

  /**
   * Forces a particular alert, causing it to be escalated as if the hardware
   * had raised it.
   *
   * @param ${ip.name_snake} A ${ip.name_snake} handle.
   * @param alert The alert to force.
   * @return The result of the operation.
   */
  OT_WARN_UNUSED_RESULT
  dif_result_t dif_${ip.name_snake}_alert_force(
    const dif_${ip.name_snake}_t *${ip.name_snake},
    dif_${ip.name_snake}_alert_t alert);
% endif

% if ip.irqs:
  /**
   * A ${ip.name_snake} interrupt request type.
   */
  typedef enum dif_${ip.name_snake}_irq {
  % for irq in ip.irqs:
    /**
     * ${irq.description}
     */
    ## This handles the GPIO IP case where there is a multi-bit interrupt.
    % if irq.width > 1:
      % for irq_idx in range(irq.width):
        kDif${ip.name_camel}Irq${irq.name_camel}${irq_idx} = ${loop.index},
      % endfor
    ## This handles the RV Timer IP where there are different ENABLE/STATE/TEST
    ## IRQ registers per hart.
    % elif ip.name_snake == "rv_timer":
      kDif${ip.name_camel}Irq${irq.name_camel} = ${loop.index % int(ip.parameters["N_TIMERS"].default)},
    ## This handles all other IPs.
    % else:
      kDif${ip.name_camel}Irq${irq.name_camel} = ${loop.index},
    % endif
  % endfor
  } dif_${ip.name_snake}_irq_t;

  /**
   * A snapshot of the state of the interrupts for this IP.
   *
   * This is an opaque type, to be used with the `dif_${ip.name_snake}_irq_get_state()`
   * and `dif_${ip.name_snake}_irq_acknowledge_state()` functions.
   */
  typedef uint32_t dif_${ip.name_snake}_irq_state_snapshot_t;

  /**
   * Returns the type of a given interrupt (i.e., event or status) for this IP.
   *
   * @param ${ip.name_snake} A ${ip.name_snake} handle.
   * @param irq An interrupt request.
   * @param[out] type Out-param for the interrupt type.
   * @return The result of the operation.
   */
  OT_WARN_UNUSED_RESULT
  dif_result_t dif_${ip.name_snake}_irq_get_type(
    const dif_${ip.name_snake}_t *${ip.name_snake},
    dif_${ip.name_snake}_irq_t irq,
    dif_irq_type_t *type);

  /**
   * Returns the state of all interrupts (i.e., pending or not) for this IP.
   *
   * @param ${ip.name_snake} A ${ip.name_snake} handle.
  % if ip.name_snake == "rv_timer":
   * @param hart_id The hart to manipulate.
  % endif
   * @param[out] snapshot Out-param for interrupt state snapshot.
   * @return The result of the operation.
   */
  OT_WARN_UNUSED_RESULT
  dif_result_t dif_${ip.name_snake}_irq_get_state(
    const dif_${ip.name_snake}_t *${ip.name_snake},
  % if ip.name_snake == "rv_timer":
    uint32_t hart_id,
  % endif
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
   * Acknowledges all interrupts that were pending at the time of the state
   * snapshot.
   *
   * @param ${ip.name_snake} A ${ip.name_snake} handle.
  % if ip.name_snake == "rv_timer":
   * @param hart_id The hart to manipulate.
  % endif
   * @param snapshot Interrupt state snapshot.
   * @return The result of the operation.
   */
  OT_WARN_UNUSED_RESULT
  dif_result_t dif_${ip.name_snake}_irq_acknowledge_state(
    const dif_${ip.name_snake}_t *${ip.name_snake},
  % if ip.name_snake == "rv_timer":
    uint32_t hart_id,
  % endif
    dif_${ip.name_snake}_irq_state_snapshot_t snapshot);

  /**
   * Acknowledges all interrupts, indicating to the hardware that all
   * interrupts have been successfully serviced.
   *
   * @param ${ip.name_snake} A ${ip.name_snake} handle.
   * @return The result of the operation.
   */
  OT_WARN_UNUSED_RESULT
  dif_result_t dif_${ip.name_snake}_irq_acknowledge_all(
    const dif_${ip.name_snake}_t *${ip.name_snake}
  % if ip.name_snake == "rv_timer":
    , uint32_t hart_id
  % endif
    );

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
   * Forces a particular interrupt, causing it to be serviced as if hardware had
   * asserted it.
   *
   * @param ${ip.name_snake} A ${ip.name_snake} handle.
   * @param irq An interrupt request.
   * @param val Value to be set.
   * @return The result of the operation.
   */
  OT_WARN_UNUSED_RESULT
  dif_result_t dif_${ip.name_snake}_irq_force(
    const dif_${ip.name_snake}_t *${ip.name_snake},
    dif_${ip.name_snake}_irq_t irq,
    const bool val);

% if ip.name_snake != "aon_timer":
  /**
   * A snapshot of the enablement state of the interrupts for this IP.
   *
   * This is an opaque type, to be used with the
   * `dif_${ip.name_snake}_irq_disable_all()` and `dif_${ip.name_snake}_irq_restore_all()`
   * functions.
   */
  typedef uint32_t dif_${ip.name_snake}_irq_enable_snapshot_t;

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
   * Disables all interrupts, optionally snapshotting all enable states for later
   * restoration.
   *
   * @param ${ip.name_snake} A ${ip.name_snake} handle.
  % if ip.name_snake == "rv_timer":
   * @param hart_id The hart to manipulate.
  % endif
   * @param[out] snapshot Out-param for the snapshot; may be `NULL`.
   * @return The result of the operation.
   */
  OT_WARN_UNUSED_RESULT
  dif_result_t dif_${ip.name_snake}_irq_disable_all(
    const dif_${ip.name_snake}_t *${ip.name_snake},
  % if ip.name_snake == "rv_timer":
    uint32_t hart_id,
  % endif
    dif_${ip.name_snake}_irq_enable_snapshot_t *snapshot);

  /**
   * Restores interrupts from the given (enable) snapshot.
   *
   * @param ${ip.name_snake} A ${ip.name_snake} handle.
  % if ip.name_snake == "rv_timer":
   * @param hart_id The hart to manipulate.
  % endif
   * @param snapshot A snapshot to restore from.
   * @return The result of the operation.
   */
  OT_WARN_UNUSED_RESULT
  dif_result_t dif_${ip.name_snake}_irq_restore_all(
    const dif_${ip.name_snake}_t *${ip.name_snake},
  % if ip.name_snake == "rv_timer":
    uint32_t hart_id,
  % endif
    const dif_${ip.name_snake}_irq_enable_snapshot_t *snapshot);
% endif

% endif

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_${ip.name_upper}_AUTOGEN_H_
