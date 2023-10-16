// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_KEYBLOB_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_KEYBLOB_H_

#include "sw/device/lib/crypto/drivers/keymgr.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Get the word-length of the full blinded keyblob for a given key length.
 *
 * @param config Key configuration.
 * @returns Word-length of the blinded keyblob.
 */
size_t keyblob_num_words(const crypto_key_config_t config);

/**
 * Get the word-length of a single key share for a given key length.
 *
 * Essentially, this just rounds `config.key_length` up to the next word.
 * The results assume that the key is not hardware-backed, since
 * hardware-backed keys do not have shares within the keyblob.
 *
 * @param config Key configuration.
 * @returns Word-length of one key share (or unblinded key).
 */
size_t keyblob_share_num_words(const crypto_key_config_t config);

/**
 * Return pointers to the separate shares within the blinded key.
 *
 * Returns an error if the keyblob length does not match the expectations from
 * the key configuration.
 *
 * @param key Blinded key from which to extract shares.
 * @param[out] share0 Pointer to direct to the first share.
 * @param[out] share1 Pointer to direct to the second share.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t keyblob_to_shares(const crypto_blinded_key_t *key, uint32_t **share0,
                           uint32_t **share1);

/**
 * Construct a blinded keyblob from the given shares.
 *
 * The size of each share should be at least `key_len` rounded up to the next
 * word (so if `key_len` is 10 bytes, each share should be 3 words or 12
 * bytes). The size of the destination buffer should be sufficient to fit
 * both shares; if `key_len` is 10 bytes, it must have 6 words, even though
 * 20 bytes would technically fit in 5. This is to preserve word-alignment of
 * the shares.
 *
 * @param share0 First share.
 * @param share1 Second share.
 * @param config Key configuration.
 * @param[out] keyblob Destination buffer.
 */
void keyblob_from_shares(const uint32_t *share0, const uint32_t *share1,
                         const crypto_key_config_t config, uint32_t *keyblob);

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
    const crypto_blinded_key_t *key, keymgr_diversification_t *diversification);

/**
 * Checks that the configuration represents a key masked with XOR.
 *
 * Returns false if the key is for an algorithm that uses a different masking
 * method (e.g. arithmetic masking for asymmetric crypto) or if the key is
 * hardware-backed.
 *
 * @param config Key configuration.
 * @return OK if `config` represents an XOR-masked key, BAD_ARGS otherwise.
 */
OT_WARN_UNUSED_RESULT
status_t keyblob_ensure_xor_masked(const crypto_key_config_t config);

/**
 * Construct a blinded keyblob from the given key and mask.
 *
 * The size of the key and mask should be `key_len` rounded up to the next
 * word (so if `key_len` is 10 bytes, each share should be 3 words or 12
 * bytes). The size of the destination buffer should be sufficient to fit
 * both shares; if `key_len` is 10 bytes, it must have 6 words, even though
 * 20 bytes would technically fit in 5. This is to preserve word-alignment of
 * the shares.
 *
 * Returns an error if called for an asymmetric key configuration; asymmetric
 * keys are likely to be masked with arithmetic rather than boolean (XOR)
 * schemes, and this function cannot be used for them.
 *
 * @param key Plaintext key.
 * @param mask Blinding value.
 * @param config Key configuration.
 * @param[out] keyblob Destination buffer.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t keyblob_from_key_and_mask(const uint32_t *key, const uint32_t *mask,
                                   const crypto_key_config_t config,
                                   uint32_t *keyblob);

/**
 * Incorporate a fresh mask into the blinded key.
 *
 * Returns an error if called for an asymmetric key configuration; asymmetric
 * keys are likely to be masked with arithmetic rather than boolean (XOR)
 * schemes, and this function cannot be used for them.
 *
 * @param key Blinded key to re-mask. Modified in-place.
 * @param mask Blinding parameter (fresh random mask).
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
status_t keyblob_remask(crypto_blinded_key_t *key, const uint32_t *mask);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_IMPL_KEYBLOB_H_
