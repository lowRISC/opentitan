// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_${ip_upper}_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_${ip_upper}_H_

// This file is the "DIF Library header template", which provides a base for
// building a DIF for a new peripheral, defining all of the declarations that
// would be expected of a DIF library as described in the README.md.
//
// This file should be instantiated with the `util/make_new_dif.py` script.
//
// The script also includes additional options for controlling how the tempalte
// is instantiated. After the script runs, delete this comment, the #error
// below, and any unnecessary definitions. Remember to run clang-format!
//
// Note that this file does not parse as C.

#error "This file is a template, and not real code."

/**
 * @file
 * @brief <a href="/hw/ip/${ip_snake}/doc/">${periph_upper}</a> Device Interface Functions
 */

#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_warn_unused_result.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * A toggle state: enabled, or disabled.
 *
 * This enum may be used instead of a `bool` when describing an enabled/disabled
 * state.
 */
typedef enum dif_${ip_snake}_toggle {
  /*
   * The "enabled" state.
   */
  kDif${ip_camel}ToggleEnabled,
  /**
   * The "disabled" state.
   */
  kDif${ip_camel}ToggleDisabled,
} dif_${ip_snake}_toggle_t;

/**
 * Hardware instantiation parameters for ${periph_lower}.
 *
 * This struct describes information about the underlying hardware that is
 * not determined until the hardware design is used as part of a top-level
 * design.
 */
typedef struct dif_${ip_snake}_params {
  /**
   * The base address for the ${periph_lower} hardware registers.
   */
  mmio_region_t base_addr;

  // Other fields, if necessary.
} dif_${ip_snake}_params_t;

/**
 * Runtime configuration for ${periph_lower}.
 *
 * This struct describes runtime information for one-time configuration of the
 * hardware.
 */
typedef struct dif_${ip_snake}_config {
  // Fields, if necessary.
} dif_${ip_snake}_config_t;

/**
 * A handle to ${periph_lower}.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_${ip_snake} {
  dif_${ip_snake}_params_t params;

  // Other fields, if necessary.
} dif_${ip_snake}_t;

/**
 * The result of a ${periph_lower} operation.
 */
typedef enum dif_${ip_snake}_result {
  /**
   * Indicates that the operation succeeded.
   */
  kDif${ip_camel}Ok = 0,
  /**
   * Indicates some unspecified failure.
   */
  kDif${ip_camel}Error = 1,
  /**
   * Indicates that some parameter passed into a function failed a
   * precondition.
   *
   * When this value is returned, no hardware operations occured.
   */
  kDif${ip_camel}BadArg = 2,
  /**
   * Indicates that this operation has been locked out, and can never
   * succeed until hardware reset.
   */
  // Remove this variant if you don't need it.
  kDif${ip_camel}Locked = 3,
} dif_${ip_snake}_result_t;


/**
 * Parameters for a ${periph_lower} transaction.
 */
typedef struct dif_${ip_snake}_transaction {
  // Your fields here.
} dif_${ip_snake}_transaction_t;

/**
 * An output location for a ${periph_lower} transaction.
 */
typedef struct dif_${ip_snake}_output {
  // Your fields here.
} dif_${ip_snake}_output_t;

/**
 * A ${periph_lower} interrupt request type.
 */
typedef enum dif_${ip_snake}_irq {
  // Your IRQs here!
} dif_${ip_snake}_irq_t;

/**
 * A snapshot of the enablement state of the interrupts for ${periph_lower}.
 *
 * This is an opaque type, to be used with the `dif_${ip_snake}_irq_disable_all()` and
 * `dif_${ip_snake}_irq_restore_all()` functions.
 */
typedef uint32_t dif_${ip_snake}_irq_snapshot_t;

/**
 * Calculates information needed to safely call a DIF. Functions like this
 * should be used instead of global variables or #defines.
 *
 * This function does not actuate the hardware.
 *
 * @param params Hardware instantiation parameters.
 * @return The information required.
 */
DIF_WARN_UNUSED_RESULT
uint32_t dif_${ip_snake}_get_size(dif_${ip_snake}_params_t params);

/**
 * Creates a new handle for ${periph_lower}.
 *
 * This function does not actuate the hardware.
 *
 * @param params Hardware instantiation parameters.
 * @param[out] ${handle} Out param for the initialized handle.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_${ip_snake}_result_t dif_${ip_snake}_init(dif_${ip_snake}_params_t params,
                                              dif_${ip_snake}_t *${handle});

/**
 * Configures ${periph_lower} with runtime information.
 *
 * This function should need to be called once for the lifetime of `handle`.
 *
 * @param ${handle} A ${periph_lower} handle.
 * @param config Runtime configuration parameters.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_${ip_snake}_result_t dif_${ip_snake}_configure(const dif_${ip_snake}_t *${handle},
                                                   dif_${ip_snake}_config_t config);

/**
 * Begins a ${periph_lower} transaction.
 *
 * Each call to this function should be sequenced with a call to
 * `dif_${ip_snake}_end()`.
 *
 * @param ${handle} A ${periph_lower} handle.
 * @param transaction Transaction configuration parameters.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_${ip_snake}_result_t dif_${ip_snake}_start(const dif_${ip_snake}_t *${handle},
                                               dif_${ip_snake}_transaction_t transaction);

/** Ends a ${periph_lower} transaction, writing the results to the given output..
 *
 * @param ${handle} A ${periph_lower} handle.
 * @param output Transaction output parameters.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_${ip_snake}_result_t dif_${ip_snake}_end(const dif_${ip_snake}_t *${handle},
                                             dif_${ip_snake}_output_t output);

/**
 * Locks out ${periph_lower} functionality.
 *
 * This function is reentrant: calling it while functionality is locked will
 * have no effect and return `kDif${ip_camel}Ok`.
 *
 * @param ${handle} A ${periph_lower} handle.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_${ip_snake}_result_t dif_${ip_snake}_lock(const dif_${ip_snake}_t *${handle});

/**
 * Checks whether this ${periph_lower} is locked.
 *
 * @param ${handle} A ${periph_lower} handle.
 * @param[out] is_locked Out-param for the locked state.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_${ip_snake}_result_t dif_${ip_snake}_is_locked(const dif_${ip_snake}_t *${handle},
                                                   bool *is_locked);

/**
 * Returns whether a particular interrupt is currently pending.
 *
 * @param ${handle} A ${periph_lower} handle.
 * @param irq An interrupt type.
 * @param[out] is_pending Out-param for whether the interrupt is pending.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_${ip_snake}_result_t dif_${ip_snake}_irq_is_pending(const dif_${ip_snake}_t *${handle},
                                                        dif_${ip_snake}_irq_t irq,
                                                        bool *is_pending);

/**
 * Acknowledges a particular interrupt, indicating to the hardware that it has
 * been successfully serviced.
 *
 * @param ${handle} A ${periph_lower} handle.
 * @param irq An interrupt type.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_${ip_snake}_result_t dif_${ip_snake}_irq_acknowledge(const dif_${ip_snake}_t *${handle},
                                                         dif_${ip_snake}_irq_t irq);

/**
 * Checks whether a particular interrupt is currently enabled or disabled.
 *
 * @param ${handle} A ${periph_lower} handle.
 * @param irq An interrupt type.
 * @param[out] state Out-param toggle state of the interrupt.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_${ip_snake}_result_t dif_${ip_snake}_irq_get_enabled(const dif_${ip_snake}_t *${handle},
                                                         dif_${ip_snake}_irq_t irq,
                                                         dif_${ip_snake}_toggle_t *state);

/**
 * Sets whether a particular interrupt is currently enabled or disabled.
 *
 * @param ${handle} A ${periph_lower} handle.
 * @param irq An interrupt type.
 * @param state The new toggle state for the interrupt.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_${ip_snake}_result_t dif_${ip_snake}_irq_set_enabled(const dif_${ip_snake}_t *${handle},
                                                         dif_${ip_snake}_irq_t irq,
                                                         dif_${ip_snake}_toggle_t state);

/**
 * Forces a particular interrupt, causing it to be serviced as if hardware had
 * asserted it.
 *
 * @param ${handle} A ${periph_lower} handle.
 * @param irq An interrupt type.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_${ip_snake}_result_t dif_${ip_snake}_irq_force(const dif_${ip_snake}_t *${handle},
                                                   dif_${ip_snake}_irq_t irq);

/**
 * Disables all interrupts, optionally snapshotting all toggle state for later
 * restoration.
 *
 * @param ${handle} A ${periph_lower} handle.
 * @param[out] snapshot Out-param for the snapshot; may be `NULL`.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_${ip_snake}_result_t dif_${ip_snake}_irq_disable_all(const dif_${ip_snake}_t *${handle},
                                                         dif_${ip_snake}_irq_snapshot_t *snapshot);

/**
 * Restores interrupts from the given snapshot.
 *
 * This function can be used with `dif_${ip_snake}_irq_disable_all()` to temporary
 * interrupt save-and-restore.
 *
 * @param ${handle} A ${periph_lower} handle.
 * @param snapshot A snapshot to restore from.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_${ip_snake}_result_t dif_${ip_snake}_irq_restore_all(const dif_${ip_snake}_t *${handle},
                                                         const dif_${ip_snake}_irq_snapshot_t *snapshot);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_${ip_upper}_H_
