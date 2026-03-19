// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_INTEGRITY_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_INTEGRITY_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/crypto/include/datatypes.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Random value to start the CRC with for the ptr_checksum of buffers.
 * This is to prevent the all zero data with a zero checksum to be considered as
 * valid.
 * Pick a value that is loaded in a single cycle.
 */
#define kOtcryptoInitIntegrityChecksum 0x5A3

/**
 * Compute the checksum of an unblinded key.
 *
 * The current key checksum is ignored. Call this routine after modifying
 * blinded key material (e.g. for re-masking).
 *
 * @param key Unblinded key.
 * @returns Checksum value.
 */
uint32_t integrity_unblinded_checksum(const otcrypto_unblinded_key_t *key);

/**
 * Compute the checksum of a blinded key.
 *
 * The current key checksum is ignored. Call this routine after modifying
 * blinded key material (e.g. for re-masking).
 *
 * @param key Blinded key.
 * @returns Checksum value.
 */
uint32_t integrity_blinded_checksum(const otcrypto_blinded_key_t *key);

/**
 * Perform an integrity check on the unblinded key.
 *
 * Returns `kHardenedBoolTrue` if the check passed and `kHardenedBoolFalse`
 * otherwise.
 *
 * @param key Unblinded key.
 * @returns Whether the integrity check passed.
 */
OT_WARN_UNUSED_RESULT
hardened_bool_t integrity_unblinded_key_check(
    const otcrypto_unblinded_key_t *key);

/**
 * Perform an integrity check on the blinded key.
 *
 * Returns `kHardenedBoolTrue` if the check passed and `kHardenedBoolFalse`
 * otherwise.
 *
 * @param key Blinded key.
 * @returns Whether the integrity check passed.
 */
OT_WARN_UNUSED_RESULT
hardened_bool_t integrity_blinded_key_check(const otcrypto_blinded_key_t *key);

/**
 * Helper function to calculate the checksum for a buffer.
 *
 * The integrity is calculated only on the buffer address and length, but not
 * the content. This allows the creation of a secure buffer before the content
 * is available, and the content can be filled later.
 */
OT_WARN_UNUSED_RESULT
static inline uint32_t calculate_buf_checksum(const void *data, size_t len) {
  return kOtcryptoInitIntegrityChecksum + (uint32_t)(uintptr_t)data +
         (uint32_t)len;
}

#ifndef OTCRYPTO_DISABLE_BUF_INTEGRITY_CHECKS

/**
 * Macro to create a buffer such otcrypto_const_word32_buf, otcrypto_word32_buf,
 * otcrypto_const_byte_buf, otcrypto_byte_buf.
 *
 * A secure manner of creating a buffer is to create a buffer with its length,
 * then set its checksum using the macro. After the checksum is set, the buffer
 * can be filled with the data such as a plaintext.
 *
 * The checksum can be verified via the OTCRYPTO_CHECK_BUF macro and should be
 * called after the buffer is consumed.
 *
 */
#define OTCRYPTO_MAKE_BUF(type, data_ptr, length)                \
  (type) {                                                       \
    .data = (data_ptr), .len = (length),                         \
    .ptr_checksum = calculate_buf_checksum((data_ptr), (length)) \
  }

/**
 * Helper function to verify the checksum of secure buffers.
 */
OT_WARN_UNUSED_RESULT
hardened_bool_t verify_buf_integrity(const otcrypto_generic_buf_t *buf);

/**
 * Macro to verify the checksum of a buffer such otcrypto_const_word32_buf,
 * otcrypto_word32_buf, otcrypto_const_byte_buf, otcrypto_byte_buf.
 *
 * This should be used after a buffer is consumed (for example after it was fed
 * to an accelerator) but before making security critical decisions on the data.
 */
#define OTCRYPTO_CHECK_BUF(buf_ptr) \
  verify_buf_integrity((const otcrypto_generic_buf_t *)(buf_ptr))

#else

#define OTCRYPTO_MAKE_BUF(type, data_ptr, length) \
  (type) { .data = (data_ptr), .len = (length) }

#define OTCRYPTO_CHECK_BUF(buf_ptr) (kHardenedBoolTrue)

#endif  // OTCRYPTO_DISABLE_BUF_INTEGRITY_CHECKS

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_INCLUDE_INTEGRITY_H_
