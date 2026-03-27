// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_KEYBLOB_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_KEYBLOB_H_

#include "datatypes.h"
#include "status.h"
#include "sw/device/lib/crypto/drivers/keymgr.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  /**
   * Number of 32-bit words in a hardware-backed key's keyblob.
   */
  kKeyblobHwBackedWords = kKeymgrSaltNumWords,
  /**
   * Number of bytes in a hardware-backed key's keyblob.
   */
  kKeyblobHwBackedBytes = kKeyblobHwBackedWords * sizeof(uint32_t),
};

/**
 * Construct key manager diversification data from a raw keyblob.
 *
 * The keyblob must be exactly 8 32-bit words long. The first word is the
 * version and subsequent words are the salt. The key mode is appended to the
 * salt to prevent key manager keys being used for different modes.
 *
 * @param keyblob Pointer to the keyblob.
 * @param mode Key mode to use in the diversification.
 * @param[out] Destination key manager diversification struct.
 */
OT_WARN_UNUSED_RESULT
status_t keyblob_buffer_to_keymgr_diversification(
    const uint32_t *keyblob, otcrypto_key_mode_t mode,
    keymgr_diversification_t *diversification);

/**
 * Construct key manager diversification data from a blinded key.
 *
 * The keyblob for a hardware-backed key must be exactly 8 32-bit words long.
 * The first word is the version and subsequent words are the salt. The key
 * mode is appended to the salt to prevent key manager keys being used for
 * different modes.
 *
 * If the key configuration states that the key is not hardware-backed, or if
 * the keyblob is the wrong length, this function will return an error.
 *
 * @param key Blinded key to use.
 * @param[out] Destination key manager diversification struct.
 */
OT_WARN_UNUSED_RESULT
status_t keyblob_to_keymgr_diversification(
    const otcrypto_blinded_key_t *key,
    keymgr_diversification_t *diversification);

/**
 * Calls keymgr to sideload key material into OTBN.
 *
 * This routine should only ever be called on hardware-backed keys.
 *
 * @param key Sideloaded key handle.
 * @return OK or error.
 */
OT_WARN_UNUSED_RESULT
status_t keyblob_sideload_key_otbn(const otcrypto_blinded_key_t *key);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_KEYBLOB_H_
