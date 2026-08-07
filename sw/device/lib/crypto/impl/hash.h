// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_HASH_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_HASH_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/crypto/include/datatypes.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Metadata and dispatch information for a supported hash function.
 */
typedef struct hash_info {
  /// Hardened hash mode identifier.
  otcrypto_hash_mode_t mode;
  /// Output digest length in 32-bit words.
  size_t digest_wordlen;
  /// Pointer to DER DigestInfo OID prefix (for PKCS#1 v1.5 padding, NULL if
  /// N/A).
  const uint8_t *der_oid;
  /// Byte-length of the DER DigestInfo OID prefix.
  size_t der_oid_len;
  /// One-shot compute function pointer.
  otcrypto_status_t (*compute)(const otcrypto_const_byte_buf_t *,
                               otcrypto_hash_digest_t *);
} hash_info_t;

/**
 * Retrieves the hash info struct for a given hash mode.
 *
 * @param hash_mode Hash mode to look up.
 * @param[out] info Destination pointer for the hash info struct.
 * @return OTCRYPTO_OK if found, OTCRYPTO_BAD_ARGS otherwise.
 */
OT_WARN_UNUSED_RESULT
status_t hash_info_get(otcrypto_hash_mode_t hash_mode, hash_info_t *info);

/**
 * Computes a digest of a message using the centralized hash dispatch table.
 *
 * The caller should allocate space for the digest buffer (`digest_data`) of
 * sufficient size (up to 16 words / 64 bytes) and pass an output `digest`
 * struct. This function will populate `digest->mode`, `digest->len`, and
 * `digest->data` based on the hash mode and write the resulting digest into
 * `digest_data`.
 *
 * @param hash_mode Hash algorithm to use.
 * @param message Input message buffer.
 * @param[out] digest_data Buffer to hold output digest words.
 * @param[out] digest Output digest struct.
 * @return OTCRYPTO_OK or error status.
 */
OT_WARN_UNUSED_RESULT
status_t hash_message(otcrypto_hash_mode_t hash_mode,
                      const otcrypto_const_byte_buf_t *message,
                      uint32_t *digest_data, otcrypto_hash_digest_t *digest);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_HASH_H_
