// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_KEYMGR_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_KEYMGR_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/impl/status.h"

#ifdef __cplusplus
extern "C" {
#endif

enum {
  /**
   * Number of 32-bit words for the salt.
   */
  kKeymgrSaltNumWords = 8,
  /**
   * Number of 32-bit words for each output key share.
   */
  kKeymgrOutputShareNumWords = 8,
};

/**
 * Data used to differentiate a generated keymgr key.
 */
typedef struct keymgr_diversification {
  /**
   * Salt value to use for key generation.
   */
  uint32_t salt[kKeymgrSaltNumWords];
  /**
   * Version for key generation (anti-rollback protection).
   */
  uint32_t version;
} keymgr_diversification_t;

/**
 * Generated key from keymgr.
 *
 * The output key material is 256 bits, generated in two shares.
 */
typedef struct keymgr_output {
  uint32_t share0[kKeymgrOutputShareNumWords];
  uint32_t share1[kKeymgrOutputShareNumWords];
} keymgr_output_t;

/**
 * Derive a key manager key that is visible to software.
 *
 * @param diversification Diversification input for the key derivation.
 * @param[out] key Destination key struct.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_generate_key_sw(const keymgr_diversification_t diversification,
                                keymgr_output_t *key);

/**
 * Derive a key manager key for the AES block.
 *
 * Calls the key manager to sideload a key into the AES hardware block and
 * waits until the operation is complete before returning.
 *
 * @param diversification Diversification input for the key derivation.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_generate_key_aes(
    const keymgr_diversification_t diversification);

/**
 * Derive a key manager key for the KMAC block.
 *
 * Calls the key manager to sideload a key into the KMAC hardware block and
 * waits until the operation is complete before returning.
 *
 * @param diversification Diversification input for the key derivation.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_generate_key_kmac(
    const keymgr_diversification_t diversification);

/**
 * Derive a key manager key for the OTBN block.
 *
 * Calls the key manager to sideload a key into the OTBN hardware block and
 * waits until the operation is complete before returning.
 *
 * @param diversification Diversification input for the key derivation.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_generate_key_otbn(
    const keymgr_diversification_t diversification);

/**
 * Clear the sideloaded AES key.
 *
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_sideload_clear_aes(void);

/**
 * Clear the sideloaded KMAC key.
 *
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_sideload_clear_kmac(void);

/**
 * Clear the sideloaded OTBN key.
 *
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t keymgr_sideload_clear_otbn(void);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_KEYMGR_H_
