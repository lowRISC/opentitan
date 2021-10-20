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
#include "sw/device/lib/dif/dif_base.h"

#include "sw/device/lib/dif/autogen/dif_edn_autogen.h"

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
 * Configures Entropy Distribution Network with runtime information.
 *
 * This function should need to be called once for the lifetime of `handle`.
 *
 * @param edn An Entropy Distribution Network handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_configure(const dif_edn_t *edn);

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
dif_result_t dif_edn_boot_mode_start(const dif_edn_t *edn);

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
dif_result_t dif_edn_auto_mode_start(const dif_edn_t *edn,
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
dif_result_t dif_edn_get_status(const dif_edn_t *edn, dif_edn_status_t flag,
                                bool *set);

/**
 * Stops the current mode of operation and disables the entropy module.
 *
 * @param edn An Entropy Distribution Network handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_stop(const dif_edn_t *edn);

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
dif_result_t dif_edn_lock(const dif_edn_t *edn);

/**
 * Checks whether this Entropy Distribution Network is locked.
 *
 * @param edn An Entropy Distribution Network handle.
 * @param[out] is_locked Out-param for the locked state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_edn_is_locked(const dif_edn_t *edn, bool *is_locked);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_EDN_H_
