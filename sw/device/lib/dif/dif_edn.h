// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_EDN_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_EDN_H_

/**
 * @file
 * @brief <a href="/hw/ip/edn/doc/">Entropy Distribution Network</a> Device
 * Interface Functions
 *
 * This API implements the interface for the Entropy Distribution Network (EDN)
 * hardware.
 *
 * There are two main modes of operation:
 *
 * - boot-time: EDN configures the associated CSRNG instance to fetch pre-FIPS
 *   entropy immediately at boot-time or after reset.
 * - auto refresh: EDN sends reseed and generate commands to the associated
 *   CSRNG instance. The API allows the user to set the CSRNG instantiate,
 *   reseed and generate para meters, as well as the reseed frequency.
 *
 * Common set of operations for both boot-time and auto refresh modes:
 *
 *  - `dif_edn_init()`
 *  - `dif_edn_configure()`
 *
 * Order of operations in boot-time request mode:
 *
 *  - `did_edn_boot_mode_start()`
 *  - `dif_edn_stop()`
 *
 * Order of operations in auto refresh mode:
 *
 *  - `dif_edn_auto_mode_start()`
 *  - `dif_edn_stop()`
 *
 * Remaining work:
 *
 * - Add error status interface.
 */

#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Maximum seed material number of uint32_t words supported in CSRNG
   * instantiate and seed commands.
   */
  kDifEntropySeedMaterialMaxWordLen = 12,
};

/**
 * A toggle state: enabled, or disabled.
 *
 * This enum may be used instead of a `bool` when describing an enabled/disabled
 * state.
 */
typedef enum dif_edn_toggle {
  /*
   * The "enabled" state.
   */
  kDifEdnToggleEnabled,
  /**
   * The "disabled" state.
   */
  kDifEdnToggleDisabled,
} dif_edn_toggle_t;

/**
 * Hardware instantiation parameters for Entropy Distribution Network.
 *
 * This struct describes information about the underlying hardware that is
 * not determined until the hardware design is used as part of a top-level
 * design.
 */
typedef struct dif_edn_params {
  /**
   * The base address for the Entropy Distribution Network hardware registers.
   */
  mmio_region_t base_addr;
} dif_edn_params_t;

/**
 * A handle to Entropy Distribution Network.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_edn {
  dif_edn_params_t params;
} dif_edn_t;

/**
 * The result of a Entropy Distribution Network operation.
 */
typedef enum dif_edn_result {
  /**
   * Indicates that the operation succeeded.
   */
  kDifEdnOk = 0,
  /**
   * Indicates some unspecified failure.
   */
  kDifEdnError = 1,
  /**
   * Indicates that some parameter passed into a function failed a
   * precondition.
   *
   * When this value is returned, no hardware operations occurred.
   */
  kDifEdnBadArg = 2,
  /**
   * Indicates that this operation has been locked out, and can never
   * succeed until hardware reset.
   */
  kDifEdnLocked = 3,
  /**
   * Indicates that the device is busy and cannot perform the requested
   * operation.
   */
  kDifEdnBusy = 4,
} dif_edn_result_t;

/**
 * CSRNG additional parameters for instantiate and generate commands.
 */
typedef struct dif_edn_seed_material {
  /**
   * Number of uint32_t words in `data`. Up to
   * `kDifEntropySeedMaterialMaxWordLen` words can be set to initialize or
   * reseed the CSRNG. CSRNG will extend the `data` to zeros if the provided
   * value is less than kDifEntropySeedMaterialMaxWordLen.
   */
  uint32_t len;
  /**
   * Seed material used in CSRNG instantiate or generate call.
   */
  uint32_t data[kDifEntropySeedMaterialMaxWordLen];
} dif_edn_seed_material_t;

/**
 * Auto-generate EDN module configuration parameters.
 */
typedef struct dif_edn_auto_params {
  /**
   * CSRNG instantiate command parameters.
   */
  dif_edn_seed_material_t instantiate_params;
  /**
   * CSRNG reseed command parameters.
   */
  dif_edn_seed_material_t reseed_params;
  /**
   * Number of uint32_t words to request the CSRNG on each generate call rounded
   * to the nearest 128bit block.
   */
  uint32_t generate_len;
  /**
   * Number of generate calls that can be made before a reseed request is made.
   */
  uint32_t reseed_interval;
} dif_edn_auto_params_t;

/**
 * A Entropy Distribution Network interrupt request type.
 */
typedef enum dif_edn_irq {
  /**
   * Asserted when a CSRNG request has completed.
   */
  kDifEdnCmdReqDone,
  /**
   * Asserted when a FIFO error occurs.
   */
  kDifEdnFatalError,
} dif_edn_irq_t;

/**
 * A snapshot of the enablement state of the interrupts the device.
 *
 * This is an opaque type, to be used with the `dif_edn_irq_disable_all()` and
 * `dif_edn_irq_restore_all()` functions.
 */
typedef uint32_t dif_edn_irq_snapshot_t;

/**
 * Creates a new handle for Entropy Distribution Network.
 *
 * This function does not actuate the hardware.
 *
 * @param params Hardware instantiation parameters.
 * @param[out] edn Out param for the initialized handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_edn_result_t dif_edn_init(dif_edn_params_t params, dif_edn_t *edn);

/**
 * Configures Entropy Distribution Network with runtime information.
 *
 * This function should need to be called once for the lifetime of `handle`.
 *
 * @param edn An Entropy Distribution Network handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_edn_result_t dif_edn_configure(const dif_edn_t *edn);

/**
 * Enables the Entropy Distribution Network in boot-time mode.
 *
 * Each call to this function should be sequenced with a call to
 * `dif_edn_stop()`.
 *
 * @param edn An Entropy Distribution Network handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_edn_result_t dif_edn_boot_mode_start(const dif_edn_t *edn);

/**
 * Enables the Entropy Distribution Network in auto refresh mode.
 *
 * Each call to this function should be sequenced with a call to
 * `dif_edn_stop()`.
 *
 * @param edn An Entropy Distribution Network handle.
 * @param config Auto request configuration parameters.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_edn_result_t dif_edn_auto_mode_start(const dif_edn_t *edn,
                                         dif_edn_auto_params_t *config);

/**
 * EDN Status flags.
 */
typedef enum dif_edn_status {
  /**
   * Device is actively processing a command in either auto or boot-time mode of
   * operation.
   */
  kDifEdnStatusCmdRunning,
  /**
   * Device has started the boot-time initialization process.
   */
  kDifEdnStatusCmdBootInitAck,
} dif_edn_status_t;

/**
 * Queries the Entropy Distribution Network status flags.
 *
 * @param edn An Entropy Distribution Network handle.
 * @param flag Status flag to query.
 * @param set Flag state (set/unset).
 * @return The result of the operation.
 */
dif_edn_result_t dif_edn_get_status(const dif_edn_t *edn, dif_edn_status_t flag,
                                    bool *set);

/**
 * Stops the current mode of operation and disables the entropy module.
 *
 * @param edn An Entropy Distribution Network handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_edn_result_t dif_edn_stop(const dif_edn_t *edn);

/**
 * Locks out Entropy Distribution Network functionality.
 *
 * This function is reentrant: calling it while functionality is locked will
 * have no effect and return `kDifEdnOk`.
 *
 * @param edn An Entropy Distribution Network handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_edn_result_t dif_edn_lock(const dif_edn_t *edn);

/**
 * Checks whether this Entropy Distribution Network is locked.
 *
 * @param edn An Entropy Distribution Network handle.
 * @param[out] is_locked Out-param for the locked state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_edn_result_t dif_edn_is_locked(const dif_edn_t *edn, bool *is_locked);

/**
 * Returns whether a particular interrupt is currently pending.
 *
 * @param edn An Entropy Distribution Network handle.
 * @param irq An interrupt type.
 * @param[out] is_pending Out-param for whether the interrupt is pending.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_edn_result_t dif_edn_irq_is_pending(const dif_edn_t *edn, dif_edn_irq_t irq,
                                        bool *is_pending);

/**
 * Acknowledges a particular interrupt, indicating to the hardware that it has
 * been successfully serviced.
 *
 * @param edn An Entropy Distribution Network handle.
 * @param irq An interrupt type.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_edn_result_t dif_edn_irq_acknowledge(const dif_edn_t *edn,
                                         dif_edn_irq_t irq);

/**
 * Checks whether a particular interrupt is currently enabled or disabled.
 *
 * @param edn An Entropy Distribution Network handle.
 * @param irq An interrupt type.
 * @param[out] state Out-param toggle state of the interrupt.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_edn_result_t dif_edn_irq_get_enabled(const dif_edn_t *edn,
                                         dif_edn_irq_t irq,
                                         dif_edn_toggle_t *state);

/**
 * Sets whether a particular interrupt is currently enabled or disabled.
 *
 * @param edn An Entropy Distribution Network handle.
 * @param irq An interrupt type.
 * @param state The new toggle state for the interrupt.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_edn_result_t dif_edn_irq_set_enabled(const dif_edn_t *edn,
                                         dif_edn_irq_t irq,
                                         dif_edn_toggle_t state);

/**
 * Forces a particular interrupt, causing it to be serviced as if hardware had
 * asserted it.
 *
 * @param edn An Entropy Distribution Network handle.
 * @param irq An interrupt type.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_edn_result_t dif_edn_irq_force(const dif_edn_t *edn, dif_edn_irq_t irq);

/**
 * Disables all interrupts, optionally snapshotting all toggle state for later
 * restoration.
 *
 * @param edn An Entropy Distribution Network handle.
 * @param[out] snapshot Out-param for the snapshot; may be `NULL`.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_edn_result_t dif_edn_irq_disable_all(const dif_edn_t *edn,
                                         dif_edn_irq_snapshot_t *snapshot);

/**
 * Restores interrupts from the given snapshot.
 *
 * This function can be used with `dif_edn_irq_disable_all()` to temporary
 * interrupt save-and-restore.
 *
 * @param edn An Entropy Distribution Network handle.
 * @param snapshot A snapshot to restore from.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_edn_result_t dif_edn_irq_restore_all(
    const dif_edn_t *edn, const dif_edn_irq_snapshot_t *snapshot);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_EDN_H_
