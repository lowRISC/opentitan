// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_CSRNG_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_CSRNG_H_

/**
 * @file
 * @brief <a href="/hw/ip/csrng/doc/">CSRNG</a> Device Interface Functions
 */

#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#include "sw/device/lib/dif/autogen/dif_csrng_autogen.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * This API implements an interface for the CSRNG hardware.
 *
 * The API follows the naming conventions used in NIST SP 800-90Ar1:
 *
 * - Instantiate.
 * - Update
 * - Reseed
 * - Generate
 * - Uninstantiate
 *
 * The seed used for instantiation can either be provided directly in
 * hardware by an entropy source module; or directly by software. See
 * `dif_csrng_instantiate()` and `dif_csrng_entropy_src` for
 * more details.
 *
 * The following sequence of operations are required to initialize
 * and generate cryptographic entropy from the CSRNG module:
 *
 * - `dif_csrng_init()`
 * - `dif_csrng_configure()`
 * - `dif_csrng_instantiate()`
 * - `dif_csrng_generate_start()`
 * - `dif_csrng_uninstantiate()`
 *
 * The following functions can be used for reseed and update operations:
 *
 * - `dif_csrng_reseed()`
 * - `dif_csrng_update()`
 *
 * The following utility functions are available to poll the state of
 * the hardware:
 *
 * - `dif_csrng_get_cmd_interface_status()`
 * - `dif_csrng_get_output_status()`
 *
 * Please see the following documentation for more information:
 * https://docs.opentitan.org/hw/ip/csrng/doc/
 *
 * Remaining work:
 *
 * - Add error status interface.
 * - Add internal state control and debug interface.
 */

/**
 * Enumeration of CSRNG command interface states.
 */
typedef enum dif_csrng_cmd_status {
  /**
   * The command interface is ready to accept commands.
   */
  kDifCsrngCmdStatusReady,
  /**
   * The command interface is processing a command.
   */
  kDifCsrngCmdStatusBusy,
  /**
   * The command interface completed with an error.
   */
  // TODO: How does the command interface recover from an error.
  // TODO: Add support for decoding ERR_CODE using, probably using
  // a separate interface.
  kDifCsrngCmdStatusError,
} dif_csrng_cmd_status_t;

/**
 * CSRNG consume seed from entropy source enable.
 */
typedef enum dif_csrng_entropy_src_toggle {
  /**
   * Seed material used as the only seed material.
   *
   * This configuration option will toggle the hardware state of the
   * CSRNG to non-FIPS compliant until it is re-instantiated.
   *
   * Note: Software may opt to XOR the seed material with a seed to implement
   * a software assisted FIPS mode of operation.
   */
  kDifCsrngEntropySrcToggleDisable = 1,
  /**
   * Entropy source XOR'ed with the provided seed material.
   */
  kDifCsrngEntropySrcToggleEnable = 0,
} dif_csrng_entropy_src_toggle_t;

/**
 * CSRNG common transaction parameters.
 */
typedef struct dif_csrng_seed_material {
  /**
   * Number of uint32_t words in `seed_material`. Up to 12 words can be
   * set to initialize the CSRNG. CSRNG will extend the `seed_material`
   * to zeros if the provided value is less that 12.
   */
  size_t seed_material_len;
  /**
   * Seed material used in CSRNG
   */
  uint32_t seed_material[12];
} dif_csrng_seed_material_t;

/**
 * Generated output state.
 */
typedef struct dif_csrng_output_status {
  /**
   * Set to true when there is cryptographic entropy data available to
   * read using `dif_csrng_generate_end()`.
   */
  bool valid_data;
  /**
   * Set to true when the cryptographic entropy data available to read
   * is FIPS/CC compliant at the hardware level.
   */
  bool fips_mode;
} dif_csrng_output_status_t;

/**
 * CSRNG internal state selector ID.
 */
typedef enum dif_csrng_internal_state_id {
  /**
   * CSRNG instance assigned to Entropy Distribution Network (EDN) 0.
   */
  kCsrngInternalStateIdEdn0 = 0,
  /**
   * CSRNG instance assigned to Entropy Distribution Network (EDN) 1.
   */
  kCsrngInternalStateIdEdn1 = 1,
  /**
   * CSRNG instance assigned to software interface.
   */
  kCsrngInternalStateIdSw = 2,
} dif_csrng_internal_state_id_t;

/**
 * CSRNG internal state.
 */
typedef struct dif_csrng_internal_state {
  /**
   * Indicates the number of requests for pseudorandom bits since instantiation
   * or reseeding.
   */
  uint32_t reseed_counter;
  /**
   * Internal V working state with a 128bit block size.
   */
  uint32_t v[4];
  /**
   * Internal key used to configure the internal CSRNG cipher.
   */
  uint32_t key[8];
  /**
   * Set to true when the CSRNG instance has been instantiated.
   */
  bool instantiated;
  /**
   * Set to true when FIPS compliant entropy was provided directly by the
   * entropy source to instantiate or reseed the CSRNG instance.
   */
  bool fips_compliance;
} dif_csrng_internal_state_t;

/**
 * Creates a new handle for CSRNG.
 *
 * This function does not actuate the hardware.
 *
 * @param base_addr Hardware instantiation base address.
 * @param[out] csrng Out param for the initialized handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_csrng_init(mmio_region_t base_addr, dif_csrng_t *csrng);

/**
 * Configures CSRNG.
 *
 * This function should need to be called once for the lifetime of `csrng`.
 *
 * @param csrng A CSRNG handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_csrng_configure(const dif_csrng_t *csrng);

/**
 * Initializes CSRNG instance with a new seed value.
 *
 * `seed_material` is used as specified in NIST SP 800-90Ar1 section
 * 10.2.1.3.1. See `dif_csrng_entropy_src` for details on how this value
 * is mixed with the CSRNG seed.
 *
 * `seed_material` can be NULL, in which case CSRNG will use a zero
 * vector instead.
 *
 * @param csrng A CSRNG handle.
 * @param entropy_src_enable Entropy source input enable.
 * @param seed_material Seed initialization parameters.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_csrng_instantiate(
    const dif_csrng_t *csrng, dif_csrng_entropy_src_toggle_t entropy_src_enable,
    const dif_csrng_seed_material_t *seed_material);

/**
 * Reseeds CSRNG instance.
 *
 * When `seed_material.seed_material_len` is set to 0, only the entropy source
 * seed is used to reseed the instance, otherwise it will be XOR'ed with the
 * entropy source.
 *
 * @param csrng A CSRNG handle.
 * @param seed_material Reseed parameters.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_csrng_reseed(const dif_csrng_t *csrng,
                              const dif_csrng_seed_material_t *seed_material);

/**
 * Updates CSRNG state.
 *
 * This function is similar to `dif_csrng_reseed()`, except:
 *
 * - Only `seed_material.seed_material` is used in the update operation.
 * - The update operation does not reset the internal CSRNG reseed
 *   counter.
 *
 * @param csrng A CSRNG handle.
 * @param seed_material Update parameters.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_csrng_update(const dif_csrng_t *csrng,
                              const dif_csrng_seed_material_t *seed_material);

/**
 * Requests cryptographic entropy bits from the CSRNG.
 *
 * The prediction resistance flag as specified in SP 800-90Ar1 section
 * 10.2.1.1 is not directily supported by the hardware. It is the
 * responsibility of the caller to reseed as needed before calling
 * this function.
 *
 * The CSRNG accepts generation requests with 128-bit granularity, with
 * a minimum 128-bit request size. This function will increase the size
 * of the request to align it to the nearest 128-bit boundary.
 *
 * @param csrng A CSRNG handle.
 * @param len Number of uint32_t words to generate.
 *
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_csrng_generate_start(const dif_csrng_t *csrng, size_t len);

/**
 * Reads the output of the last CSRNG generate call.
 *
 * This function blocks until all data is read from the CSRNG. The caller is
 * responsible for making sure that the `len` parameter matches the length set
 * in the `dif_csrng_generate_start()` call.
 *
 * `dif_csrng_get_output_status()` can be called before this function to ensure
 * there is data availble in the CSRNG output buffer.
 *
 * @param csrng A CSRNG handle.
 * @param[out] buf A buffer to fill with words from the pipeline.
 * @param len The number of words to read into `buf`.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_csrng_generate_end(const dif_csrng_t *csrng, uint32_t *buf,
                                    size_t len);

/**
 * Uninstantiates CSRNG
 *
 * Resets the CSRNG instance. Values in the CSRNG are zeroed out. This
 * command effectively resets the CSRNG, clearing any errors that it
 * may have encountered due to processing or entropy source errors.
 *
 * @param csrng An CSRNG handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_csrng_uninstantiate(const dif_csrng_t *csrng);

/**
 * Gets the current command interface status.
 *
 * This function can be called before or after any of the following functions:
 *
 * - `dif_csrng_instantiate()`
 * - `dif_csrng_reseed()`
 * - `dif_csrng_update()`
 * - `dif_csrng_generate_start()`
 * - `dif_csrng_uninstantiate()`
 *
 * @param csrng An CSRNG handle
 * @param[out] status Command interface status.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_csrng_get_cmd_interface_status(const dif_csrng_t *csrng,
                                                dif_csrng_cmd_status_t *status);

/**
 * Gets the current cryptographic entropy output data status.
 *
 * This function can be used before calling `dif_csrng_generate_end()` to
 * check if there is data available to read.
 *
 * @param csrng A CSRNG handle.
 * @param[out] status CSRNG output status.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_csrng_get_output_status(const dif_csrng_t *csrng,
                                         dif_csrng_output_status_t *status);

/**
 * Gets the working state of a CSRNG instance.
 *
 * @param csrng A CSRNG handle
 * @param instance_id CSRNG instance ID.
 * @param[out] state The working state of a CSRNG instance.
 * @return The result of the operation.
 *
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_csrng_get_internal_state(
    const dif_csrng_t *csrng, dif_csrng_internal_state_id_t instance_id,
    dif_csrng_internal_state_t *state);

/**
 * Locks out CSRNG functionality.
 *
 * This function is reentrant: calling it while functionality is locked will
 * have no effect and return `kDifCsrngOk`.
 *
 * @param csrng A CSRNG handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_csrng_lock(const dif_csrng_t *csrng);

/**
 * Checks whether this CSRNG is locked.
 *
 * @param csrng A CSRNG handle.
 * @param[out] is_locked Out-param for the locked state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_csrng_is_locked(const dif_csrng_t *csrng, bool *is_locked);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_CSRNG_H_
