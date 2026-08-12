// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_KMAC_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_KMAC_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/crypto/impl/status.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * The exposed constants to caller functions.
 */
enum {
  // The total size of prefix registers (in bytes), after removing len encodings
  kKmacPrefixMaxSize = 36,
  // The max size of customization string for KMAC.
  kKmacCustStrMaxSize = 32,
  // The size of the sideload key. This parameter is not exposed by KMAC or
  // Keymgr hjson files from HW, so we need to hardcode it for the moment.
  kKmacSideloadKeyLength = 256,
  // Length of a SHA3-224 digest in bytes.
  kKmacSha3224DigestBytes = 224 / 8,
  // Length of a SHA3-224 digest in 32-bit words.
  kKmacSha3224DigestWords = kKmacSha3224DigestBytes / sizeof(uint32_t),
  // Length of a SHA3_256 digest in bytes.
  kKmacSha3256DigestBytes = 256 / 8,
  // Length of a SHA3_256 digest in 32-bit words.
  kKmacSha3256DigestWords = kKmacSha3256DigestBytes / sizeof(uint32_t),
  // Length of a SHA3_384 digest in bytes.
  kKmacSha3384DigestBytes = 384 / 8,
  // Length of a SHA3_384 digest in 32-bit words.
  kKmacSha3384DigestWords = kKmacSha3384DigestBytes / sizeof(uint32_t),
  // Length of a SHA3_512 digest in bytes.
  kKmacSha3512DigestBytes = 512 / 8,
  // Length of a SHA3_512 digest in 32-bit words.
  kKmacSha3512DigestWords = kKmacSha3512DigestBytes / sizeof(uint32_t),
};

/**
 * Simplified key struct to pass blinded key internally.
 */
typedef struct kmac_blinded_key {
  uint32_t *share0;
  uint32_t *share1;
  // The length of single share (in bytes)
  size_t len;
  // Whether the key should be provided by keymgr through sideload port.
  // If `hw_backed` is true, `share0/1` pointers and `len` are ignored.
  hardened_bool_t hw_backed;
  /**
   * Checksum of this KMAC key structure.
   */
  uint32_t checksum;
} kmac_blinded_key_t;

/**
 * A context struct maintained for streaming operations.
 *
 * TODO: Refine this once the save-and-restore feature has landed.
 */
typedef struct kmac_ctx {
  // The KMAC operation (internal `kmac_operation_t` value).
  uint32_t operation;
  // The security strength (internal `kmac_security_str_t` value).
  uint32_t security_str;
  // Whether the squeezing phase has started (`hardened_bool_t` value).
  uint32_t squeeze_started;
  // Number of words already read from the current Keccak state block.
  uint32_t squeeze_offset;
} kmac_ctx_t;

/**
 * Check whether given key length is valid for KMAC.

 * @param key_len Key length as input.
 * @return Return OTCRYPTO_OK if valid and otherwise an error.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_key_length_check(size_t key_len);

/**
 * Set the "global" config of HWIP
 *
 * For the moment, we have a number of configuation options needs to be
 * configured at session level. This functions serves as a temporary
 * solution by setting default values to this configuration.
 * TODO: Define config struct and pass it as argument.
 * TODO: see #14832
 *
 * Warning: This function sets `entropy_ready`, which triggers kmac_entropy's
 * FSM to jump to next step. Therefore, the caller of this function should make
 * sure that entropy is configured properly beforehand.
 *
 * It enforces the following as the default configuration:
 * It touches the following fields of CSRs:
 *   CFG register:
 *     endianness, entropy_mode, fast_process, msg_mask, ent_ready,
 * en_unsup_mode EDN refresh settings: hash threshold refresh
 * counter entropy seed -> ignore? INTR_ENABLE: all disabled
 *
 * @return Error code.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_hwip_default_configure(void);

/**
 * Hardware wipe guard.
 *
 * Cleanup handler that wipes the internal state of the KMAC HWIP and returns
 * it to the idle state so that it can be claimed for a new operation.
 *
 * @param guard Guard variable armed with `kHardenedBoolTrue` and disarmed with
                `kHardenedBoolFalse.
 */
void kmac_wipe_guard(uint32_t *guard);

/**
 * Compute SHA-3-224 in one-shot.
 *
 * The caller must ensure that there is at least 224 bits = 28 bytes of space
 * available at the location pointed to by `digest`.
 *
 * @param message The input message buffer.
 * @param[out] digest Output buffer for the result.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_sha3_224(const otcrypto_const_byte_buf_t *message,
                       uint32_t *digest);

/**
 * Compute SHA-3-256 in one-shot.
 *
 * The caller must ensure that there is at least 256 bits = 32 bytes of space
 * available at the location pointed to by `digest`.
 *
 * @param message The input message buffer.
 * @param[out] digest Output buffer for the result.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_sha3_256(const otcrypto_const_byte_buf_t *message,
                       uint32_t *digest);

/**
 * Compute SHA-3-384 in one-shot.
 *
 * The caller must ensure that there is at least 384 bits = 48 bytes of space
 * available at the location pointed to by `digest`.
 *
 * @param message The input message buffer.
 * @param[out] digest Output buffer for the result.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_sha3_384(const otcrypto_const_byte_buf_t *message,
                       uint32_t *digest);

/**
 * Compute SHA-3-512 in one-shot.
 *
 * The caller must ensure that there is at least 512 bits = 64 bytes of space
 * available at the location pointed to by `digest`.
 *
 * @param message The input message buffer.
 * @param[out] digest Output buffer for the result.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_sha3_512(const otcrypto_const_byte_buf_t *message,
                       uint32_t *digest);

/**
 * Compute SHAKE-128 in one-shot.
 *
 * The caller must ensure that `digest_len` words are allocated at the location
 * pointed to by `digest`.
 *
 * @param message The input message buffer.
 * @param[out] digest Output buffer for the result.
 * @param digest_len Requested digest length in 32-bit words.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_shake_128(const otcrypto_const_byte_buf_t *message,
                        uint32_t *digest, size_t digest_len);

/**
 * Compute SHAKE-256 in one-shot.
 *
 * The caller must ensure that `digest_len` words are allocated at the location
 * pointed to by `digest`.
 *
 * @param message The input message buffer.
 * @param[out] digest Output buffer for the result.
 * @param digest_len Requested digest length in 32-bit words.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_shake_256(const otcrypto_const_byte_buf_t *message,
                        uint32_t *digest, size_t digest_len);

/**
 * Compute CSHAKE-128 in one-shot.
 *
 * The caller must ensure that `digest_len` words are allocated at the location
 * pointed to by `digest`.
 *
 * @param message The input message buffer.
 * @param func_name The function name.
 * @param func_name_len The function name length in bytes.
 * @param cust_str The customization string.
 * @param cust_str_len The customization string length in bytes.
 * @param[out] digest Output buffer for the result.
 * @param digest_len Requested digest length in 32-bit words.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_cshake_128(const otcrypto_const_byte_buf_t *message,
                         const unsigned char *func_name, size_t func_name_len,
                         const unsigned char *cust_str, size_t cust_str_len,
                         uint32_t *digest, size_t digest_len);

/**
 * Compute CSHAKE-256 in one-shot.
 *
 * The caller must ensure that `digest_len` words are allocated at the location
 * pointed to by `digest`.
 *
 * @param message The input message buffer.
 * @param func_name The function name.
 * @param func_name_len The function name length in bytes.
 * @param cust_str The customization string.
 * @param cust_str_len The customization string length in bytes.
 * @param[out] digest Output buffer for the result.
 * @param digest_len Requested digest length in 32-bit words.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_cshake_256(const otcrypto_const_byte_buf_t *message,
                         const unsigned char *func_name, size_t func_name_len,
                         const unsigned char *cust_str, size_t cust_str_len,
                         uint32_t *digest, size_t digest_len);

/**
 * Compute KMAC-128 in one-shot.
 *
 * This function also supports sideloading the key from the Keymgr through a
 * peripheral port inaccessible to SW. In order to sideload the key, the caller
 * needs to set `key->hw_backed` to `kHardenedBoolTrue`. When sideloading,
 * `key->length` must correspond to the sideload key size
 * `kKmacSideloadKeyLength / 8` and `share` pointers must be set to NULL.
 *
 * With SW-provided keys, `key->hw_backed` must be `kHardenedBoolFalse`, `share`
 * pointers must be correctly configured and `len` must match the key length.
 *
 * The caller must ensure that `digest_len` bytes are allocated at the location
 * pointed to by `digest`. `cust_str_len` must not exceed
 * `kKmacCustStrMaxSize`. If `masked_digest` is true, the `digest` buffer must
 * have enough space for 2x `digest_len` bytes.
 *
 * @param key The KMAC key.
 * @param masked_digest Whether to return the digest in concatenated shares.
 * @param message The input message buffer.
 * @param cust_str The customization string.
 * @param cust_str_len The customization string length in bytes.
 * @param[out] digest Output buffer for the result.
 * @param digest_len Requested digest length in bytes.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_kmac_128(kmac_blinded_key_t *key, hardened_bool_t masked_digest,
                       const otcrypto_const_byte_buf_t *message,
                       const unsigned char *cust_str, size_t cust_str_len,
                       uint32_t *digest, size_t digest_len);

/**
 * Compute KMAC-256 in one-shot.
 *
 * This function also supports sideloading the key from the Keymgr through a
 * peripheral port inaccessible to SW. In order to sideload the key, the caller
 * needs to set `key->hw_backed` to `kHardenedBoolTrue`. When sideloading,
 * `key->length` must correspond to the sideload key size
 * `kKmacSideloadKeyLength / 8` and `share` pointers must be set to NULL.
 *
 * With SW-provided keys, `key->hw_backed` must be `kHardenedBoolFalse`, `share`
 * pointers must be correctly configured and `len` must match the key length.
 *
 * The caller must ensure that `digest_len` bytes are allocated at the location
 * pointed to by `digest`. `cust_str_len` must not exceed
 * `kKmacCustStrMaxSize`. If `masked_digest` is true, the `digest` buffer must
 * have enough space for 2x `digest_len` bytes.
 *
 * @param key The KMAC key.
 * @param masked_digest Whether to return the digest in concatenated shares.
 * @param message The input message buffer.
 * @param cust_str The customization string.
 * @param cust_str_len The customization string length in bytes.
 * @param[out] digest Output buffer for the result.
 * @param digest_len Requested digest length in bytes.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_kmac_256(kmac_blinded_key_t *key, hardened_bool_t masked_digest,
                       const otcrypto_const_byte_buf_t *message,
                       const unsigned char *cust_str, size_t cust_str_len,
                       uint32_t *digest, size_t digest_len);

/**
 * Initializes the context for a streamed SHA-3-224 computation.
 *
 * @param[out] ctx KMAC context.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_sha3_224_init(kmac_ctx_t *ctx);

/**
 * Initializes the context for a streamed SHA-3-256 computation.
 *
 * @param[out] ctx KMAC context.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_sha3_256_init(kmac_ctx_t *ctx);

/**
 * Initializes the context for a streamed SHA-3-384 computation.
 *
 * @param[out] ctx KMAC context.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_sha3_384_init(kmac_ctx_t *ctx);

/**
 * Initializes the context for a streamed SHA-3-512 computation.
 *
 * @param[out] ctx KMAC context.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_sha3_512_init(kmac_ctx_t *ctx);

/**
 * Initializes the context for a streamed SHAKE-128 computation.
 *
 * @param[out] ctx KMAC context.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_shake_128_init(kmac_ctx_t *ctx);

/**
 * Initializes the context for a streamed SHAKE-256 computation.
 *
 * @param[out] ctx KMAC context.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_shake_256_init(kmac_ctx_t *ctx);

/**
 * Initializes the context for a streamed CSHAKE-128 computation.
 *
 * The combined length of `func_name` and `cust_str` must not exceed
 * `kKmacPrefixMaxSize`.
 *
 * @param func_name The function name.
 * @param func_name_len The function name length in bytes.
 * @param cust_str The customization string.
 * @param cust_str_len The customization string length in bytes.
 * @param[out] ctx KMAC context.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_cshake_128_init(const unsigned char *func_name,
                              size_t func_name_len,
                              const unsigned char *cust_str,
                              size_t cust_str_len, kmac_ctx_t *ctx);

/**
 * Initializes the context for a streamed CSHAKE-256 computation.
 *
 * The combined length of `func_name` and `cust_str` must not exceed
 * `kKmacPrefixMaxSize`.
 *
 * @param func_name The function name.
 * @param func_name_len The function name length in bytes.
 * @param cust_str The customization string.
 * @param cust_str_len The customization string length in bytes.
 * @param[out] ctx KMAC context.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_cshake_256_init(const unsigned char *func_name,
                              size_t func_name_len,
                              const unsigned char *cust_str,
                              size_t cust_str_len, kmac_ctx_t *ctx);

/**
 * Initializes the context for a streamed KMAC-128 computation.
 *
 * The key is configured as documented for `kmac_kmac_128`; both SW-provided
 * and sideloaded (`key->hw_backed = kHardenedBoolTrue`) keys are supported.
 * `cust_str_len` must not exceed `kKmacCustStrMaxSize`.
 *
 * @param key The KMAC key.
 * @param cust_str The customization string.
 * @param cust_str_len The customization string length in bytes.
 * @param[out] ctx KMAC context.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_kmac_128_init(kmac_blinded_key_t *key,
                            const unsigned char *cust_str, size_t cust_str_len,
                            kmac_ctx_t *ctx);

/**
 * Initializes the context for a streamed KMAC-256 computation.
 *
 * The key is configured as documented for `kmac_kmac_256`; both SW-provided
 * and sideloaded (`key->hw_backed = kHardenedBoolTrue`) keys are supported.
 * `cust_str_len` must not exceed `kKmacCustStrMaxSize`.
 *
 * @param key The KMAC key.
 * @param cust_str The customization string.
 * @param cust_str_len The customization string length in bytes.
 * @param[out] ctx KMAC context.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_kmac_256_init(kmac_blinded_key_t *key,
                            const unsigned char *cust_str, size_t cust_str_len,
                            kmac_ctx_t *ctx);

/**
 * Pass data for absorption to a streamed {KMAC, SHA3, SHAKE, cSHAKE}
 * operation.
 *
 * This function can be called multiple times between an `init` and
 * `final` invocation.
 *
 * @param ctx KMAC context.
 * @param msg Message bytes to be absorbed.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_update(kmac_ctx_t *ctx, const otcrypto_const_byte_buf_t *msg);

/**
 * Squeeze digest words out of a streamed SHAKE or cSHAKE operation.
 *
 * This function can be called multiple times to extract a digest of arbitrary
 * length in several steps. The first call terminates the absorb phase.
 * It is necessary to call `kmac_xof_end` after all data has been squeezed
 * in order to release the hardware.
 *
 * @param ctx KMAC context.
 * @param[out] digest Output buffer for the result.
 * @param digest_len Requested digest length in 32-bit words.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_xof_squeeze(kmac_ctx_t *ctx, uint32_t *digest, size_t digest_len);

/**
 * Finish a streamed SHAKE or cSHAKE operation.
 *
 * Issues the `DONE` command, which wipes the Keccak state and releases the
 * KMAC HWIP.
 *
 * @param ctx KMAC context.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_xof_end(kmac_ctx_t *ctx);

/**
 * Finalize a streamed SHA-3-224 computation and return the digest.
 *
 * @param ctx KMAC context.
 * @param[out] digest Output buffer for the result.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_sha3_224_final(kmac_ctx_t *ctx, uint32_t *digest);

/**
 * Finalize a streaming SHA-3-256 computation and return the digest.
 *
 * @param ctx KMAC context.
 * @param[out] digest Output buffer for the result.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_sha3_256_final(kmac_ctx_t *ctx, uint32_t *digest);

/**
 * Finalize a streamed SHA-3-384 computation and return the digest.
 *
 * @param ctx KMAC context.
 * @param[out] digest Output buffer for the result.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_sha3_384_final(kmac_ctx_t *ctx, uint32_t *digest);

/**
 * Finalize a streamed SHA-3-512 computation and return the digest.
 *
 * @param ctx KMAC context.
 * @param[out] digest Output buffer for the result.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_sha3_512_final(kmac_ctx_t *ctx, uint32_t *digest);

/**
 * Finalize a streamed SHAKE-128 computation and return the digest.
 *
 * @param ctx KMAC context.
 * @param[out] digest Output buffer for the result.
 * @param digest_len Requested digest length in 32-bit words.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_shake_128_final(kmac_ctx_t *ctx, uint32_t *digest,
                              size_t digest_len);

/**
 * Finalize a streamed SHAKE-256 computation and return the digest.
 *
 * @param ctx KMAC context.
 * @param[out] digest Output buffer for the result.
 * @param digest_len Requested digest length in 32-bit words.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_shake_256_final(kmac_ctx_t *ctx, uint32_t *digest,
                              size_t digest_len);

/**
 * Finalize a streamed CSHAKE-128 computation and return the digest.
 *
 * @param ctx KMAC context.
 * @param[out] digest Output buffer for the result.
 * @param digest_len Requested digest length in 32-bit words.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_cshake_128_final(kmac_ctx_t *ctx, uint32_t *digest,
                               size_t digest_len);

/**
 * Finalize a streamed CSHAKE-256 computation and return the digest.
 *
 * @param ctx KMAC context.
 * @param[out] digest Output buffer for the result.
 * @param digest_len Requested digest length in 32-bit words.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_cshake_256_final(kmac_ctx_t *ctx, uint32_t *digest,
                               size_t digest_len);

/**
 * Finalize a streamed KMAC-128 computation and return the tag.
 *
 * If `masked_digest` is true, the `digest` buffer must have enough space for
 * twice the amount of `digest_len` bytes.
 *
 * @param ctx KMAC context.
 * @param masked_digest Whether to return the digest in concatenated shares.
 * @param[out] digest Output buffer for the result.
 * @param digest_len Requested digest length in bytes.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_kmac_128_final(kmac_ctx_t *ctx, hardened_bool_t masked_digest,
                             uint32_t *digest, size_t digest_len);

/**
 * Finalize a streaming KMAC-256 computation and return the tag.
 *
 * If `masked_digest` is true, the `digest` buffer must have enough space for
 * twice the amount of `digest_len` bytes.
 *
 * @param ctx KMAC context.
 * @param masked_digest Whether to return the digest in concatenated shares.
 * @param[out] digest Output buffer for the result.
 * @param digest_len Requested digest length in bytes.
 * @return Error status.
 */
OT_WARN_UNUSED_RESULT
status_t kmac_kmac_256_final(kmac_ctx_t *ctx, hardened_bool_t masked_digest,
                             uint32_t *digest, size_t digest_len);

/**
 * Compute the checksum of an KMAC key.
 *
 * Call this routine after creating or modifying the KMAC key structure.
 *
 * @param key KMAC key.
 * @returns Checksum value.
 */
uint32_t kmac_key_integrity_checksum(const kmac_blinded_key_t *key);

/**
 * Perform an integrity check on the KMAC key.
 *
 * Returns `kHardenedBoolTrue` if the check passed and `kHardenedBoolFalse`
 * otherwise.
 *
 * @param key KMAC key.
 * @returns Whether the integrity check passed.
 */
hardened_bool_t kmac_key_integrity_checksum_check(
    const kmac_blinded_key_t *key);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_KMAC_H_
