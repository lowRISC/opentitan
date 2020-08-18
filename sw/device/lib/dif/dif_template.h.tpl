// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_TEMPLATE_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_TEMPLATE_H_

// This file is the "DIF Library header template", which provides a base for
// building a DIF for a new peripheral, defining all of the declarations that
// would be expected of a DIF library as described in the README.md.
//
// To instantiate this for a new IP named my_ip, simply:
// - Copy this file into dif_my_ip.h.
// - Replace all occurrences of `<ip>` with `my_ip`.
// - Replace all occurrences of `<IP>` with `MyIp`.
// - Replace all occurrences of `<Peripheral>` and `<peripheral>` with a
//   documentation-appropriate name for my_ip, like "my peripheral"; mind the
//   capitalization. Proof-reading the comments may be necessary.
// - Replace the `handle` function parameter, if you want.
// - Delete any definitions that are not required for your peripheral.
// - Fix up the header guards using util/fix_include_guard.py.
// - Delete this comment and the guard #error below.
//
// Note that this file is unlikely to parse as real C at all.

#error "This file is a template, and not real code."

/**
 * @file
 * @brief <a href="/hw/ip/<ip>/doc/"><Peripheral></a> Device Interface Functions
 */

#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_warn_unused_result.h"

// Header Extern Guard (so header can be used from C and C++)
#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * A toggle state: enabled, or disabled.
 *
 * This enum may be used instead of a `bool` when describing an enabled/disabled
 * state.
 */
typedef enum dif_<ip>_toggle {
  /**
   * The "enabled" state.
   */
  kDif<IP>ToggleEnabled,
  /**
   * The "disabled" state.
   */
  kDif<IP>ToggleDisabled,
} dif_<ip>_toggle_t;

/**
 * Hardware instantiation parameters for <peripheral>.
 *
 * This struct describes information about the underlying hardware that is
 * not determined until the hardware design is used as part of a top-level
 * design.
 */
typedef struct dif_<ip>_param {
  /**
   * The base address for the <peripheral> hardware registers.
   */
  mmio_region_t base_addr;

  // Other fields, if necessary.
} dif_<ip>_param_t;

/**
 * Runtime configuration for <peripheral>.
 *
 * This struct describes runtime information for one-time configuration of the
 * hardware.
 */
typedef struct dif_<ip>_config {
  // Fields, if necessary.
} dif_<ip>_config_t;

/**
 * A handle to <peripheral>.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_<ip> {
  dif_param_<ip>_t params;

  // Other fields, if necessary.
} dif_<ip>_t;

/**
 * The result of a <peripheral> operation.
 */
typedef enum dif_<ip>_result {
  /**
   * Indicates that the operation succeeded.
   */
  kDif<IP>Ok = 0,
  /**
   * Indicates some unspecified failure.
   */
  kDif<IP>Error = 1,
  /**
   * Indicates that some parameter passed into a function failed a
   * precondition.
   *
   * When this value is returned, no hardware operations occured.
   */
  kDif<IP>BadArg = 2,
  /**
   * Indicates that this operation has been locked out, and can never
   * succeed until hardware reset.
   */
  // Remove this variant if you don't need it.
  kDif<IP>Locked = 3,
} dif_<ip>_result_t;


/**
 * Parameters for a <peripheral> transaction.
 */
typedef struct dif_<ip>_transaction {
  // Your fields here.
} dif_<ip>_transaction_t;

/**
 * An output location for a <peripheral> transaction.
 */
typedef struct dif_<ip>_output {
  // Your fields here.
} dif_<ip>_output_t;

/**
 * A <peripheral> interrupt request type.
 */
typedef enum dif_<ip>_irq {
  // Your IRQs here!
} dif_<ip>_irq_t;

/**
 * A snapshot of the enablement state of the interrupts for <peripheral>.
 *
 * This is an opaque type, to be used with the `dif_<ip>_irq_disable_all()` and
 * `dif_<ip>_irq_restore_all()` functions.
 */
typedef uint32_t dif_<ip>_irq_snapshot_t;

/**
 * Creates a new handle for <peripheral>.
 *
 * This function does not actuate the hardware.
 *
 * @param params Hardware instantiation parameters.
 * @param handle Out param for the initialized handle.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_<ip>_result_t dif_<ip>_init(dif_<ip>_params_t params, dif_<ip>_t *handle);

/**
 * Configures <peripheral> with runtime information.
 *
 * This function should need to be called once for the lifetime of `handle`.
 *
 * @param handle A <peripheral> handle.
 * @param config Runtime configuration parameters.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_<ip>_result_t dif_<ip>_configure(const dif_<ip>_t* handle,
                                     dif_<ip>_config_t config);

/**
 * Begins a <peripheral> transaction.
 *
 * Each call to this function should be sequenced with a call to
 * `dif_<ip>_end()`.
 *
 * @param handle A <peripheral> handle.
 * @param transaction Transaction configuration parameters.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_<ip>_result_t dif_<ip>_start(const dif_<ip>_t* handle,
                                 dif_<ip>_transaction_t transaction);

/** Ends a <peripheral> transaction, writing the results to the given output..
 *
 * @param handle A <peripheral> handle.
 * @param output Transaction output parameters.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_<ip>_result_t dif_<ip>_end(const dif_<ip>_t* handle,
                               dif_<ip>_output_t output);

/**
 * Locks out <peripheral> functionality.
 *
 * This function is reentrant: calling it while functionality is locked will
 * have no effect and return `kDif<IP>Ok`.
 *
 * @param handle A <peripheral> handle.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_<ip>_result_t dif_<ip>_lock(const dif_<ip>_t* handle);

/**
 * Checks whether this <peripheral> is locked.
 *
 * @param handle A <peripheral> handle.
 * @param is_locked Out-param for the locked state.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_<ip>_result_t dif_<ip>_is_locked(const dif_<ip>_t* handle, bool *is_locked);

/**
 * Returns whether a particular interrupt is currently pending.
 *
 * @param handle A <peripheral> handle.
 * @param irq An interrupt type.
 * @param is_pending Out-param for whether the interrupt is pending.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_<ip>_result_t dif_<ip>_irq_is_pending(const dif_<ip>_t *handle,
                                          dif_<ip>_irq_t irq,
                                          bool *is_pending);

/**
 * Acknowledges a particular interrupt, indicating to the hardware that it has
 * been successfully serviced.
 *
 * @param handle A <peripheral> handle.
 * @param irq An interrupt type.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_<ip>_result_t dif_<ip>_irq_acknowledge(const dif_<ip>_t *handle,
                                           dif_<ip>_irq_t irq);

/**
 * Checks whether a particular interrupt is currently enabled or disabled.
 *
 * @param handle A <peripheral> handle.
 * @param irq An interrupt type.
 * @param state Out-param toggle state of the interrupt.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_<ip>_result_t dif_<ip>_irq_get_enabled(const dif_<ip>_t *handle,
                                           dif_<ip>_irq_t irq,
                                           dif_<ip>_toggle_t *state);

/**
 * Sets whether a particular interrupt is currently enabled or disabled.
 *
 * @param handle A <peripheral> handle.
 * @param irq An interrupt type.
 * @param state The new toggle state for the interrupt.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_<ip>_result_t dif_<ip>_irq_set_enabled(const dif_<ip>_t *handle,
                                           dif_<ip>_irq_t irq,
                                           dif_<ip>_toggle_t state);

/**
 * Forces a particular interrupt, causing it to be serviced as if hardware had
 * asserted it.
 *
 * @param handle A <peripheral> handle.
 * @param irq An interrupt type.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_<ip>_result_t dif_<ip>_irq_force(const dif_<ip>_t *handle,
                                     dif_<ip>_irq_t irq);

/**
 * Disables all interrupts, optionally snapshotting all toggle state for later
 * restoration.
 *
 * @param handle A <peripheral> handle.
 * @param snapshot Out-param for the snapshot; may be `NULL`.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_<ip>_result_t dif_<ip>_irq_disable_all(const dif_<ip>_t *handle,
                                           dif_<ip>_irq_snapshot_t *snapshot);

/**
 * Restores interrupts from the given snapshot.
 *
 * This function can be used with `dif_<ip>_irq_disable_all()` to temporary
 * interrupt save-and-restore.
 *
 * @param handle A <peripheral> handle.
 * @param snapshot A snapshot to restore from.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_<ip>_result_t dif_<ip>_irq_restore_all(const dif_<ip>_t *handle,
                                           const dif_<ip>_irq_snapshot_t *snapshot);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_TEMPLATE_H_
