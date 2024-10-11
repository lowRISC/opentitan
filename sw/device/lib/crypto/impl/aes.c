// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/aes.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/aes.h"
#include "sw/device/lib/crypto/drivers/keymgr.h"
#include "sw/device/lib/crypto/impl/aes_gcm/aes_gcm.h"
#include "sw/device/lib/crypto/impl/aes_gcm/ghash.h"
#include "sw/device/lib/crypto/impl/aes_kwp/aes_kwp.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('a', 'e', 's')

// Check that cipher mode enum from AES driver matches the one from the
// top-level API.
OT_ASSERT_ENUM_VALUE(kAesCipherModeEcb, (uint32_t)kOtcryptoAesModeEcb);
OT_ASSERT_ENUM_VALUE(kAesCipherModeCbc, (uint32_t)kOtcryptoAesModeCbc);
OT_ASSERT_ENUM_VALUE(kAesCipherModeCfb, (uint32_t)kOtcryptoAesModeCfb);
OT_ASSERT_ENUM_VALUE(kAesCipherModeOfb, (uint32_t)kOtcryptoAesModeOfb);
OT_ASSERT_ENUM_VALUE(kAesCipherModeCtr, (uint32_t)kOtcryptoAesModeCtr);

// Check GHASH context size against the underlying implementation.
static_assert(sizeof(otcrypto_aes_gcm_context_t) >= sizeof(aes_gcm_context_t),
              "Size of AES-GCM context object for top-level API must be at "
              "least as large as the context for the "
              "underlying implementation.");
static_assert(alignof(aes_gcm_context_t) >= alignof(uint32_t),
              "Internal AES-GCM context object must be word-aligned for use "
              "with `hardened_memcpy`.");
static_assert(sizeof(otcrypto_key_config_t) % sizeof(uint32_t) == 0,
              "Key configuration size should be a multiple of 32 bits");

// Ensure the internal AES-GCM context size is a multiple of the word size and
// calculate the number of words.
static_assert(sizeof(aes_gcm_context_t) % sizeof(uint32_t) == 0,
              "Internal AES-GCM context object must be a multiple of the word "
              "size for use with `hardened_memcpy`.");
enum {
  kAesGcmContextNumWords = sizeof(aes_gcm_context_t) / sizeof(uint32_t),
};

/**
 * Save an AES-GCM context.
 *
 * @param internal_ctx Internal context object to save.
 * @param[out] api_ctx Resulting API-facing context object.
 */
static inline void gcm_context_save(aes_gcm_context_t *internal_ctx,
                                    otcrypto_aes_gcm_context_t *api_ctx) {
  hardened_memcpy(api_ctx->data, (uint32_t *)internal_ctx,
                  kAesGcmContextNumWords);
}

/**
 * Restore an AES-GCM context.
 *
 * @param api_ctx API-facing context object to restore from.
 * @param[out] internal_ctx Resulting internal context object.
 */
static inline void gcm_context_restore(otcrypto_aes_gcm_context_t *api_ctx,
                                       aes_gcm_context_t *internal_ctx) {
  hardened_memcpy((uint32_t *)internal_ctx, api_ctx->data,
                  kAesGcmContextNumWords);
}

/**
 * Extract an AES key from the blinded key struct.
 *
 * Also performs integrity, mode, and null-pointer checks on the key. This
 * function is only for basic AES modes; do not use for AES-GCM or AES-KWP keys
 * since they will fail the mode check.
 *
 * @param blinded_key Blinded key struct.
 * @param aes_mode Block cipher mode.
 * @param[out] aes_key Destination AES key struct.
 * @return Result of the operation.
 */
static status_t aes_key_construct(const otcrypto_blinded_key_t *blinded_key,
                                  const otcrypto_aes_mode_t aes_mode,
                                  aes_key_t *aes_key) {
  // Key integrity check.
  if (launder32(integrity_blinded_key_check(blinded_key)) !=
      kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(integrity_blinded_key_check(blinded_key),
                    kHardenedBoolTrue);

  if (blinded_key->config.hw_backed == kHardenedBoolTrue) {
    // Call keymgr to sideload the key into AES.
    keymgr_diversification_t diversification;
    HARDENED_TRY(
        keyblob_to_keymgr_diversification(blinded_key, &diversification));
    HARDENED_TRY(keymgr_generate_key_aes(diversification));
    aes_key->key_shares[0] = NULL;
    aes_key->key_shares[1] = NULL;
  } else if (blinded_key->config.hw_backed == kHardenedBoolFalse) {
    // Get pointers to the individual shares.
    uint32_t *share0;
    uint32_t *share1;
    HARDENED_TRY(keyblob_to_shares(blinded_key, &share0, &share1));
    aes_key->key_shares[0] = share0;
    aes_key->key_shares[1] = share1;
  } else {
    return OTCRYPTO_BAD_ARGS;
  }
  aes_key->sideload = blinded_key->config.hw_backed;

  // Check for null pointer.
  if (blinded_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Set the block cipher mode based on the key mode.
  switch (blinded_key->config.key_mode) {
    case kOtcryptoKeyModeAesEcb:
      aes_key->mode = kAesCipherModeEcb;
      break;
    case kOtcryptoKeyModeAesCbc:
      aes_key->mode = kAesCipherModeCbc;
      break;
    case kOtcryptoKeyModeAesCfb:
      aes_key->mode = kAesCipherModeCfb;
      break;
    case kOtcryptoKeyModeAesOfb:
      aes_key->mode = kAesCipherModeOfb;
      break;
    case kOtcryptoKeyModeAesCtr:
      aes_key->mode = kAesCipherModeCtr;
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Check that the key mode matches the requested block cipher mode.
  if (memcmp(&aes_key->mode, &aes_mode, sizeof(aes_key->mode)) != 0) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(aes_key->mode, aes_mode);

  // Set the AES key length (in words).
  aes_key->key_len = keyblob_share_num_words(blinded_key->config);

  return OTCRYPTO_OK;
}

/**
 * Applies the specified mode of AES padding to the block.
 *
 * Modifies only positions on and after index `last_block_len` in the
 * `padded_block`; real input may be written to the initial locations either
 * before or after calling this function.
 *
 * @param padding_mode Padding mode.
 * @param partial_data_len Length of real input in this block (may be 0).
 * @param[out] padded_block Destination padded block.
 * @return Result of the operation.
 */
static status_t aes_padding_apply(otcrypto_aes_padding_t padding_mode,
                                  const size_t partial_data_len,
                                  aes_block_t *block) {
  if (partial_data_len >= kAesBlockNumBytes) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Get a byte-sized pointer to the padding start point within the block's
  // data buffer.
  char *padding = ((char *)block->data) + partial_data_len;

  // Pad a full block if the last block is full, otherwise just fill the last
  // block.
  size_t padding_len = kAesBlockNumBytes - partial_data_len;
  hardened_bool_t padding_written = kHardenedBoolFalse;
  switch (launder32(padding_mode)) {
    case kOtcryptoAesPaddingPkcs7:
      // Pads with value same as the number of padding bytes.
      memset(padding, (uint8_t)padding_len, padding_len);
      padding_written = kHardenedBoolTrue;
      break;
    case kOtcryptoAesPaddingIso9797M2:
      // Pads with 0x80 (0b10000000), followed by zero bytes.
      memset(padding, 0x0, padding_len);
      padding[0] = 0x80;
      padding_written = kHardenedBoolTrue;
      break;
    case kOtcryptoAesPaddingNull:
      // This routine should not be called if padding is not needed.
      return OTCRYPTO_RECOV_ERR;
    default:
      // Unrecognized padding mode.
      return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(padding_written, kHardenedBoolTrue);

  return OTCRYPTO_OK;
}

/**
 * Return the number of blocks for the input and padding mode.
 *
 * @param plaintext_len Length of plaintext in bytes.
 * @param padding Padding mode.
 * @returns Number of AES blocks required.
 */
static status_t num_padded_blocks_get(size_t plaintext_len,
                                      otcrypto_aes_padding_t padding,
                                      size_t *num_blocks) {
  size_t num_full_blocks = plaintext_len / kAesBlockNumBytes;

  if (padding == kOtcryptoAesPaddingNull) {
    // If no padding mode is given, the last block must be full.
    if (num_full_blocks * kAesBlockNumBytes != plaintext_len) {
      return OTCRYPTO_BAD_ARGS;
    }

    *num_blocks = num_full_blocks;
    return OTCRYPTO_OK;
  }
  HARDENED_CHECK_NE(padding, kOtcryptoAesPaddingNull);

  // For non-null padding modes, we append a full block of padding if the last
  // block is full, so the value is always <full blocks> + 1.
  *num_blocks = num_full_blocks + 1;
  return OTCRYPTO_OK;
}

/**
 * Return the block at index i for the given input and padding mode.
 *
 * @param input Input data buffer.
 * @param padding Padding mode.
 * @param index Block index.
 * @param[out] AES block at `index`.
 * @param input_len Length of cipher input in bytes.
 * @param padding Padding mode.
 * @returns Number of AES blocks required.
 */
static status_t get_block(otcrypto_const_byte_buf_t input,
                          otcrypto_aes_padding_t padding, size_t index,
                          aes_block_t *block) {
  size_t num_full_blocks = input.len / kAesBlockNumBytes;

  // The index should never be more than `num_full_blocks` + 1, even including
  // padding.
  HARDENED_CHECK_LE(index, num_full_blocks + 1);

  if (launder32(index) < num_full_blocks) {
    HARDENED_CHECK_LT(index, num_full_blocks);
    // No need to worry about padding, just copy the data into the output
    // block.
    // TODO(#17711) Change to `hardened_memcpy`.
    memcpy(block->data, &input.data[index * kAesBlockNumBytes],
           kAesBlockNumBytes);
    return OTCRYPTO_OK;
  }
  HARDENED_CHECK_GE(index, num_full_blocks);

  // If we get here, this block is the one with padding. It may be a partial
  // block or an empty block that will be entirely filled with padded bytes.
  size_t partial_data_len = input.len % kAesBlockNumBytes;
  memcpy(block->data, &input.data[index * kAesBlockNumBytes], partial_data_len);

  // Apply padding.
  HARDENED_TRY(aes_padding_apply(padding, partial_data_len, block));
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_aes_padded_plaintext_length(
    size_t plaintext_len, otcrypto_aes_padding_t aes_padding,
    size_t *padded_len) {
  size_t padded_nblocks;
  HARDENED_TRY(
      num_padded_blocks_get(plaintext_len, aes_padding, &padded_nblocks));
  *padded_len = padded_nblocks * kAesBlockNumBytes;
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_aes(const otcrypto_blinded_key_t *key,
                               otcrypto_word32_buf_t iv,
                               otcrypto_aes_mode_t aes_mode,
                               otcrypto_aes_operation_t aes_operation,
                               otcrypto_const_byte_buf_t cipher_input,
                               otcrypto_aes_padding_t aes_padding,
                               otcrypto_byte_buf_t cipher_output) {
  // Check for NULL pointers in input pointers and data buffers.
  if (key == NULL || (aes_mode != kOtcryptoAesModeEcb && iv.data == NULL) ||
      cipher_input.data == NULL || cipher_output.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Calculate the number of blocks for the input, including the padding for
  // encryption.
  size_t input_nblocks;
  if (aes_operation == kOtcryptoAesOperationEncrypt) {
    HARDENED_TRY(
        num_padded_blocks_get(cipher_input.len, aes_padding, &input_nblocks));
  } else if (aes_operation == kOtcryptoAesOperationDecrypt) {
    // If the operation is decryption, the input length must be divisible by
    // the block size.
    if (launder32(cipher_input.len) % kAesBlockNumBytes != 0) {
      return OTCRYPTO_BAD_ARGS;
    }
    HARDENED_CHECK_EQ(cipher_input.len % kAesBlockNumBytes, 0);
    input_nblocks = cipher_input.len / kAesBlockNumBytes;
  }

  // Check input/output lengths.
  //   - Input length must be nonzero.
  //   - Output length must match number of input blocks.
  if (cipher_input.len == 0 ||
      launder32(cipher_output.len) != input_nblocks * kAesBlockNumBytes) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(cipher_output.len, input_nblocks * kAesBlockNumBytes);

  // Construct the IV and check its length. ECB mode will ignore the IV, so in
  // this case it is left uninitialized.
  aes_block_t aes_iv;
  if (aes_mode == launder32(kAesCipherModeEcb)) {
    HARDENED_CHECK_EQ(aes_mode, kAesCipherModeEcb);
  } else {
    HARDENED_CHECK_NE(aes_mode, kAesCipherModeEcb);

    // The IV must be exactly one block long.
    if (launder32(iv.len) != kAesBlockNumWords) {
      return OTCRYPTO_BAD_ARGS;
    }
    HARDENED_CHECK_EQ(iv.len, kAesBlockNumWords);
    hardened_memcpy(aes_iv.data, iv.data, kAesBlockNumWords);
  }

  // Parse the AES key.
  aes_key_t aes_key;
  HARDENED_TRY(aes_key_construct(key, aes_mode, &aes_key));

  // Start the operation (encryption or decryption).
  switch (aes_operation) {
    case kOtcryptoAesOperationEncrypt:
      HARDENED_TRY(aes_encrypt_begin(aes_key, &aes_iv));
      break;
    case kOtcryptoAesOperationDecrypt:
      HARDENED_TRY(aes_decrypt_begin(aes_key, &aes_iv));
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Perform the cipher operation for all full blocks. The input and output are
  // offset by `block_offset` number of blocks, where `block_offset` can be 1
  // or 2. So if unrolled, these loops would look like:
  //
  // - block_offset == 1
  //   aes_update(NULL, input[0]);
  //   aes_update(output[0], input[1]);
  //   aes_update(output[1], input[2]);
  //   aes_update(output[2], NULL);
  //
  // - block_offset == 2
  //   aes_update(NULL, input[0]);
  //   aes_update(NULL, input[1]);
  //   aes_update(output[0], input[2]); // The HW is processing input[1].
  //   aes_update(output[1], input[3]); // The HW is processing input[2].
  //   aes_update(output[2], NULL);
  //   aes_update(output[3], NULL);
  //
  // Using a `block_offset` of 2 allows having 3 blocks in flight which is
  // beneficial from a hardening and performance point of view:
  // - Software retrieves Block x-1 from the data output registers.
  // - Hardware processes Block x.
  // - Software provides  Block x+1 via the data input registers.
  //
  // See the AES driver for details.
  const size_t block_offset = input_nblocks >= 3 ? 2 : 1;
  aes_block_t block_in;
  aes_block_t block_out;
  size_t i;

  // Provide the first `block_offset` number of input blocks and call the AES
  // cipher.
  for (i = 0; launder32(i) < block_offset; ++i) {
    HARDENED_TRY(get_block(cipher_input, aes_padding, i, &block_in));
    TRY(aes_update(/*dest=*/NULL, &block_in));
  }
  // Check that the loop ran for the correct number of iterations.
  HARDENED_CHECK_EQ(i, block_offset);

  // Call the AES cipher while providing new input and copying data to the
  // output buffer.
  for (i = block_offset; launder32(i) < input_nblocks; ++i) {
    HARDENED_TRY(get_block(cipher_input, aes_padding, i, &block_in));
    TRY(aes_update(&block_out, &block_in));
    // TODO(#17711) Change to `hardened_memcpy`.
    memcpy(&cipher_output.data[(i - block_offset) * kAesBlockNumBytes],
           block_out.data, kAesBlockNumBytes);
  }
  // Check that the loop ran for the correct number of iterations.
  HARDENED_CHECK_EQ(i, input_nblocks);

  // Retrieve the output from the final `block_offset` blocks (providing no
  // input).
  for (i = block_offset; launder32(i) > 0; --i) {
    HARDENED_TRY(aes_update(&block_out, /*src=*/NULL));
    // TODO(#17711) Change to `hardened_memcpy`.
    memcpy(&cipher_output.data[(input_nblocks - i) * kAesBlockNumBytes],
           block_out.data, kAesBlockNumBytes);
  }
  // Check that the loop ran for the correct number of iterations.
  HARDENED_CHECK_EQ(i, 0);

  // Deinitialize the AES block and update the IV (in ECB mode, skip the IV).
  if (aes_mode == launder32(kAesCipherModeEcb)) {
    HARDENED_TRY(aes_end(NULL));
  } else {
    HARDENED_TRY(aes_end(&aes_iv));
    hardened_memcpy(iv.data, aes_iv.data, kAesBlockNumWords);
  }

  // If the key was sideloaded, clear it.
  if (key->config.hw_backed == kHardenedBoolTrue) {
    HARDENED_TRY(keymgr_sideload_clear_aes());
  }

  return OTCRYPTO_OK;
}

/**
 * Construct the underlying AES key for AES-GCM.
 *
 * Also performs integrity, mode, and null-pointer checks on the key.
 *
 * @param blinded_key Blinded key struct.
 * @param[out] aes_key Destination AES key struct.
 * @return Result of the operation.
 */
static status_t aes_gcm_key_construct(const otcrypto_blinded_key_t *blinded_key,
                                      aes_key_t *aes_key) {
  // Key integrity check.
  if (launder32(integrity_blinded_key_check(blinded_key)) !=
      kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(integrity_blinded_key_check(blinded_key),
                    kHardenedBoolTrue);

  // Check the key mode.
  if (launder32((uint32_t)blinded_key->config.key_mode) !=
      kOtcryptoKeyModeAesGcm) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(blinded_key->config.key_mode, kOtcryptoKeyModeAesGcm);

  // Set the mode of the underlying AES key to CTR (since this is the
  // underlying block cipher mode for GCM).
  aes_key->mode = kAesCipherModeCtr;

  // Set the AES key length (in words).
  aes_key->key_len = keyblob_share_num_words(blinded_key->config);

  // Check for null pointer.
  if (blinded_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (launder32(blinded_key->config.hw_backed) == kHardenedBoolTrue) {
    // In this case, we use an implementation-specific representation; the
    // first "share" is the keyblob and the second share is ignored.
    if (launder32(blinded_key->keyblob_length) != kKeyblobHwBackedBytes) {
      return OTCRYPTO_BAD_ARGS;
    }
    HARDENED_CHECK_EQ(blinded_key->keyblob_length, kKeyblobHwBackedBytes);
    aes_key->key_shares[0] = blinded_key->keyblob;
    aes_key->key_shares[1] = NULL;
    aes_key->sideload = launder32(kHardenedBoolTrue);
  } else if (launder32(blinded_key->config.hw_backed) == kHardenedBoolFalse) {
    HARDENED_CHECK_EQ(blinded_key->config.hw_backed, kHardenedBoolFalse);
    // Get pointers to the individual shares.
    uint32_t *share0;
    uint32_t *share1;
    HARDENED_TRY(keyblob_to_shares(blinded_key, &share0, &share1));
    aes_key->key_shares[0] = share0;
    aes_key->key_shares[1] = share1;
    aes_key->sideload = launder32(kHardenedBoolFalse);
  } else {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(aes_key->sideload, blinded_key->config.hw_backed);

  return OTCRYPTO_OK;
}

/**
 * Checks if the given byte-length matches the tag length enum value.
 *
 * @param word_len Allocated tag length in 32-bit words.
 * @param tag_len Tag length enum value.
 * @return OK if the tag length is acceptable, BAD_ARGS otherwise.
 */
status_t aes_gcm_check_tag_length(size_t word_len,
                                  otcrypto_aes_gcm_tag_len_t tag_len) {
  size_t bit_len = 0;
  switch (launder32(tag_len)) {
    case kOtcryptoAesGcmTagLen128:
      HARDENED_CHECK_EQ(tag_len, kOtcryptoAesGcmTagLen128);
      bit_len = 128;
      break;
    case kOtcryptoAesGcmTagLen96:
      HARDENED_CHECK_EQ(tag_len, kOtcryptoAesGcmTagLen96);
      bit_len = 96;
      break;
    case kOtcryptoAesGcmTagLen64:
      HARDENED_CHECK_EQ(tag_len, kOtcryptoAesGcmTagLen64);
      bit_len = 64;
      break;
    case kOtcryptoAesGcmTagLen32:
      HARDENED_CHECK_EQ(tag_len, kOtcryptoAesGcmTagLen32);
      bit_len = 32;
      break;
    default:
      // Invalid tag length.
      return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_GT(bit_len, 0);
  HARDENED_CHECK_EQ(bit_len % 32, 0);

  if (launder32(word_len) != bit_len / 32) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(word_len, bit_len / 32);

  // Extra hardening checks; the word length must be nonzero and at most the
  // size of an AES block.
  HARDENED_CHECK_LT(0, word_len);
  HARDENED_CHECK_LE(word_len, kAesBlockNumWords);

  return OTCRYPTO_OK;
}

/**
 * Actuate the key manager to generate a sideloaded AES-GCM key.
 *
 * The AES driver will not load or clear sideloaded keys by itself, so we need
 * to do it separately at each stage of the AES-GCM operation.
 *
 * Sideloaded keys are stored in the `aes_key_t` struct in a format specific to
 * this AES-GCM implementation: the first "key share" is the diversification
 * data as it would be stored in a blinded keyblob, and the second "share" is
 * completely ignored.
 *
 * If the key is not a sideloaded key, this function does nothing.
 *
 * @param key Key to load.
 * @return OK or errror.
 */
static status_t load_key_if_sideloaded(const aes_key_t key) {
  if (launder32(key.sideload) == kHardenedBoolFalse) {
    return OTCRYPTO_OK;
  } else if (key.sideload != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(key.sideload, kHardenedBoolTrue);
  keymgr_diversification_t diversification;
  HARDENED_TRY(keyblob_buffer_to_keymgr_diversification(
      key.key_shares[0], kOtcryptoKeyModeAesGcm, &diversification));
  return keymgr_generate_key_aes(diversification);
}

/**
 * Clear the sideload slot if the AES key was sideloaded.
 *
 * It is important to clear the sideload slot before returning to the caller so
 * that other applications can't access the key in between operations.
 *
 * If the key is not a sideloaded key, this function does nothing.
 *
 * @param key Key that was possibly loaded.
 * @return OK or errror.
 */
static status_t clear_key_if_sideloaded(const aes_key_t key) {
  if (launder32(key.sideload) == kHardenedBoolFalse) {
    HARDENED_CHECK_EQ(key.sideload, kHardenedBoolFalse);
    return OTCRYPTO_OK;
  } else if (launder32(key.sideload) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(key.sideload, kHardenedBoolTrue);
  return keymgr_sideload_clear_aes();
}

otcrypto_status_t otcrypto_aes_gcm_encrypt(const otcrypto_blinded_key_t *key,
                                           otcrypto_const_byte_buf_t plaintext,
                                           otcrypto_const_word32_buf_t iv,
                                           otcrypto_const_byte_buf_t aad,
                                           otcrypto_aes_gcm_tag_len_t tag_len,
                                           otcrypto_byte_buf_t ciphertext,
                                           otcrypto_word32_buf_t auth_tag) {
  // Check for NULL pointers in input pointers and required-nonzero-length data
  // buffers.
  if (key == NULL || iv.data == NULL || auth_tag.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Conditionally check for null pointers in data buffers that may be
  // 0-length.
  if ((aad.len != 0 && aad.data == NULL) ||
      (ciphertext.len != 0 && ciphertext.data == NULL) ||
      (plaintext.len != 0 && plaintext.data == NULL)) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Ensure the plaintext and ciphertext lengths match.
  if (launder32(ciphertext.len) != plaintext.len) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(ciphertext.len, plaintext.len);

  // Check the tag length.
  HARDENED_TRY(aes_gcm_check_tag_length(auth_tag.len, tag_len));

  // Construct the AES key.
  aes_key_t aes_key;
  HARDENED_TRY(aes_gcm_key_construct(key, &aes_key));
  HARDENED_TRY(load_key_if_sideloaded(aes_key));

  // Call the core encryption operation.
  HARDENED_TRY(aes_gcm_encrypt(aes_key, iv.len, iv.data, plaintext.len,
                               plaintext.data, aad.len, aad.data, auth_tag.len,
                               auth_tag.data, ciphertext.data));

  HARDENED_TRY(clear_key_if_sideloaded(aes_key));
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_aes_gcm_decrypt(
    const otcrypto_blinded_key_t *key, otcrypto_const_byte_buf_t ciphertext,
    otcrypto_const_word32_buf_t iv, otcrypto_const_byte_buf_t aad,
    otcrypto_aes_gcm_tag_len_t tag_len, otcrypto_const_word32_buf_t auth_tag,
    otcrypto_byte_buf_t plaintext, hardened_bool_t *success) {
  // Check for NULL pointers in input pointers and required-nonzero-length data
  // buffers.
  if (key == NULL || iv.data == NULL || auth_tag.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Conditionally check for null pointers in data buffers that may be
  // 0-length.
  if ((aad.len != 0 && aad.data == NULL) ||
      (ciphertext.len != 0 && ciphertext.data == NULL) ||
      (plaintext.len != 0 && plaintext.data == NULL)) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Construct the AES key.
  aes_key_t aes_key;
  HARDENED_TRY(aes_gcm_key_construct(key, &aes_key));
  HARDENED_TRY(load_key_if_sideloaded(aes_key));

  // Ensure the plaintext and ciphertext lengths match.
  if (launder32(ciphertext.len) != plaintext.len) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(ciphertext.len, plaintext.len);

  // Check the tag length.
  HARDENED_TRY(aes_gcm_check_tag_length(auth_tag.len, tag_len));

  // Call the core decryption operation.
  HARDENED_TRY(aes_gcm_decrypt(aes_key, iv.len, iv.data, ciphertext.len,
                               ciphertext.data, aad.len, aad.data, auth_tag.len,
                               auth_tag.data, plaintext.data, success));

  HARDENED_TRY(clear_key_if_sideloaded(aes_key));
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_aes_gcm_encrypt_init(
    const otcrypto_blinded_key_t *key, otcrypto_const_word32_buf_t iv,
    otcrypto_aes_gcm_context_t *ctx) {
  if (key == NULL || key->keyblob == NULL || iv.data == NULL || ctx == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Construct the AES key.
  aes_key_t aes_key;
  HARDENED_TRY(aes_gcm_key_construct(key, &aes_key));
  HARDENED_TRY(load_key_if_sideloaded(aes_key));

  // Call the internal init operation.
  aes_gcm_context_t internal_ctx;
  HARDENED_TRY(aes_gcm_encrypt_init(aes_key, iv.len, iv.data, &internal_ctx));

  // Save the context and clear the key if needed.
  gcm_context_save(&internal_ctx, ctx);
  HARDENED_TRY(clear_key_if_sideloaded(internal_ctx.key));
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_aes_gcm_decrypt_init(
    const otcrypto_blinded_key_t *key, otcrypto_const_word32_buf_t iv,
    otcrypto_aes_gcm_context_t *ctx) {
  if (key == NULL || key->keyblob == NULL || iv.data == NULL || ctx == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Construct the AES key.
  aes_key_t aes_key;
  HARDENED_TRY(aes_gcm_key_construct(key, &aes_key));
  HARDENED_TRY(load_key_if_sideloaded(aes_key));

  // Call the internal init operation.
  aes_gcm_context_t internal_ctx;
  HARDENED_TRY(aes_gcm_decrypt_init(aes_key, iv.len, iv.data, &internal_ctx));

  // Save the context and clear the key if needed.
  gcm_context_save(&internal_ctx, ctx);
  HARDENED_TRY(clear_key_if_sideloaded(internal_ctx.key));
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_aes_gcm_update_aad(otcrypto_aes_gcm_context_t *ctx,
                                              otcrypto_const_byte_buf_t aad) {
  if (ctx == NULL || aad.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (aad.len == 0) {
    // Nothing to do.
    return OTCRYPTO_OK;
  }

  // Restore the AES-GCM context object and load the key if needed.
  aes_gcm_context_t internal_ctx;
  gcm_context_restore(ctx, &internal_ctx);
  HARDENED_TRY(load_key_if_sideloaded(internal_ctx.key));

  // Call the internal update operation.
  HARDENED_TRY(aes_gcm_update_aad(&internal_ctx, aad.len, aad.data));

  // Save the context and clear the key if needed.
  gcm_context_save(&internal_ctx, ctx);
  HARDENED_TRY(clear_key_if_sideloaded(internal_ctx.key));
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_aes_gcm_update_encrypted_data(
    otcrypto_aes_gcm_context_t *ctx, otcrypto_const_byte_buf_t input,
    otcrypto_byte_buf_t output, size_t *output_bytes_written) {
  if (ctx == NULL || input.data == NULL || output.data == NULL ||
      output_bytes_written == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  *output_bytes_written = 0;

  if (input.len == 0) {
    // Nothing to do.
    return OTCRYPTO_OK;
  }

  // Restore the AES-GCM context object and load the key if needed.
  aes_gcm_context_t internal_ctx;
  gcm_context_restore(ctx, &internal_ctx);
  HARDENED_TRY(load_key_if_sideloaded(internal_ctx.key));

  // The output buffer must be long enough to hold all full blocks that will
  // exist after `input` is added.
  size_t partial_block_len = internal_ctx.input_len % kAesBlockNumBytes;
  if (input.len > UINT32_MAX - partial_block_len) {
    return OTCRYPTO_BAD_ARGS;
  }
  size_t min_output_blocks =
      (partial_block_len + input.len) / kAesBlockNumBytes;
  size_t min_output_len = min_output_blocks * kAesBlockNumBytes;
  if (output.len < min_output_len) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Call the internal update operation.
  HARDENED_TRY(aes_gcm_update_encrypted_data(
      &internal_ctx, input.len, input.data, output_bytes_written, output.data));

  // Save the context and clear the key if needed.
  gcm_context_save(&internal_ctx, ctx);
  HARDENED_TRY(clear_key_if_sideloaded(internal_ctx.key));
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_aes_gcm_encrypt_final(
    otcrypto_aes_gcm_context_t *ctx, otcrypto_aes_gcm_tag_len_t tag_len,
    otcrypto_byte_buf_t ciphertext, size_t *ciphertext_bytes_written,
    otcrypto_word32_buf_t auth_tag) {
  if (ctx == NULL || ciphertext_bytes_written == NULL ||
      auth_tag.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (ciphertext.len != 0 && ciphertext.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  *ciphertext_bytes_written = 0;

  // Check the tag length.
  HARDENED_TRY(aes_gcm_check_tag_length(auth_tag.len, tag_len));

  // Restore the AES-GCM context object and load the key if needed.
  aes_gcm_context_t internal_ctx;
  gcm_context_restore(ctx, &internal_ctx);
  HARDENED_TRY(load_key_if_sideloaded(internal_ctx.key));

  // If the partial block is nonempty, the output must be at least as long as
  // the partial block.
  size_t partial_block_len = internal_ctx.input_len % kAesBlockNumBytes;
  if (ciphertext.len < partial_block_len) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Call the internal final operation.
  HARDENED_TRY(aes_gcm_encrypt_final(&internal_ctx, auth_tag.len, auth_tag.data,
                                     ciphertext_bytes_written,
                                     ciphertext.data));

  // Clear the context and the key if needed.
  hardened_memshred(ctx->data, ARRAYSIZE(ctx->data));
  HARDENED_TRY(clear_key_if_sideloaded(internal_ctx.key));
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_aes_gcm_decrypt_final(
    otcrypto_aes_gcm_context_t *ctx, otcrypto_const_word32_buf_t auth_tag,
    otcrypto_aes_gcm_tag_len_t tag_len, otcrypto_byte_buf_t plaintext,
    size_t *plaintext_bytes_written, hardened_bool_t *success) {
  if (ctx == NULL || plaintext_bytes_written == NULL || auth_tag.data == NULL ||
      success == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (plaintext.len != 0 && plaintext.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  *plaintext_bytes_written = 0;
  *success = kHardenedBoolFalse;

  // Check the tag length.
  HARDENED_TRY(aes_gcm_check_tag_length(auth_tag.len, tag_len));

  // Restore the AES-GCM context object and load the key if needed.
  aes_gcm_context_t internal_ctx;
  gcm_context_restore(ctx, &internal_ctx);
  HARDENED_TRY(load_key_if_sideloaded(internal_ctx.key));

  // If the partial block is nonempty, the output must be at least as long as
  // the partial block.
  size_t partial_block_len = internal_ctx.input_len % kAesBlockNumBytes;
  if (plaintext.len < partial_block_len) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Call the internal final operation.
  HARDENED_TRY(aes_gcm_decrypt_final(&internal_ctx, auth_tag.len, auth_tag.data,
                                     plaintext_bytes_written, plaintext.data,
                                     success));

  // Clear the context and the key if needed.
  hardened_memshred(ctx->data, ARRAYSIZE(ctx->data));
  HARDENED_TRY(clear_key_if_sideloaded(internal_ctx.key));
  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_aes_kwp_wrapped_len(
    const otcrypto_key_config_t config, size_t *wrapped_num_words) {
  // Check that the total wrapped key length will fit in 32 bits.
  size_t config_num_words = sizeof(otcrypto_key_config_t) / sizeof(uint32_t);
  if (keyblob_num_words(config) > UINT32_MAX - config_num_words - 2) {
    return OTCRYPTO_BAD_ARGS;
  }

  // A wrapped key includes:
  //   - The full key configuration
  //   - The key checksum (32 bits)
  //   - The keyblob length (in words) as a 32-bit word
  //   - The keyblob
  *wrapped_num_words = config_num_words + 2 + keyblob_num_words(config);

  // We need to add 64 bits for the AES-KWP prefix.
  *wrapped_num_words += 2;

  // The number of words needs to be rounded up to the next multiple of 64 bits.
  if (*wrapped_num_words % 2 == 1) {
    *wrapped_num_words += 1;
  }

  return OTCRYPTO_OK;
}

/**
 * Extract an AES-KWP key encryption key from the blinded key struct.
 *
 * Also checks the key's integrity and mode.
 *
 * @param key_kek Blinded key encryption key.
 * @param[out] aes_key Destination AES key struct.
 * @return Result of the operation.
 */
static status_t aes_kwp_key_construct(const otcrypto_blinded_key_t *key_kek,
                                      aes_key_t *aes_key) {
  // Key integrity check.
  if (launder32(integrity_blinded_key_check(key_kek)) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(integrity_blinded_key_check(key_kek), kHardenedBoolTrue);

  // Check the key mode.
  if (launder32((uint32_t)key_kek->config.key_mode) != kOtcryptoKeyModeAesKwp) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(key_kek->config.key_mode, kOtcryptoKeyModeAesKwp);

  // Set the mode of the underlying AES key to ECB (since this is the
  // underlying block cipher mode for KWP).
  aes_key->mode = kAesCipherModeEcb;

  if (key_kek->config.hw_backed == kHardenedBoolTrue) {
    // Call keymgr to sideload the key into AES.
    keymgr_diversification_t diversification;
    HARDENED_TRY(keyblob_to_keymgr_diversification(key_kek, &diversification));
    HARDENED_TRY(keymgr_generate_key_aes(diversification));
  } else if (key_kek->config.hw_backed != kHardenedBoolFalse) {
    return OTCRYPTO_BAD_ARGS;
  }
  aes_key->sideload = key_kek->config.hw_backed;

  // Set the AES key length (in words).
  aes_key->key_len = keyblob_share_num_words(key_kek->config);

  // Get pointers to the individual shares.
  uint32_t *share0;
  uint32_t *share1;
  HARDENED_TRY(keyblob_to_shares(key_kek, &share0, &share1));
  aes_key->key_shares[0] = share0;
  aes_key->key_shares[1] = share1;

  return OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_aes_kwp_wrap(
    const otcrypto_blinded_key_t *key_to_wrap,
    const otcrypto_blinded_key_t *key_kek, otcrypto_word32_buf_t wrapped_key) {
  if (key_to_wrap == NULL || key_to_wrap->keyblob == NULL || key_kek == NULL ||
      key_kek->keyblob == NULL || wrapped_key.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the integrity of the key material we are wrapping.
  if (launder32(integrity_blinded_key_check(key_to_wrap)) !=
      kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(integrity_blinded_key_check(key_to_wrap),
                    kHardenedBoolTrue);

  // Check the length of the output buffer.
  size_t exp_len;
  HARDENED_TRY(otcrypto_aes_kwp_wrapped_len(key_to_wrap->config, &exp_len));
  if (wrapped_key.len != exp_len) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the integrity/lengths/mode of the key encryption key, and construct
  // an internal AES key.
  aes_key_t kek;
  HARDENED_TRY(aes_kwp_key_construct(key_kek, &kek));

  // Check the keyblob length.
  uint32_t keyblob_words = keyblob_num_words(key_to_wrap->config);
  if (key_to_wrap->keyblob_length != keyblob_words * sizeof(uint32_t)) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check that the configuration is aligned.
  if (misalignment32_of((uintptr_t)&key_to_wrap->config) != 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Create the plaintext by copying the key configuration, checksum, keyblob
  // length, and keyblob into a buffer.
  uint32_t config_words = sizeof(otcrypto_key_config_t) / sizeof(uint32_t);
  size_t plaintext_num_words = config_words + 2 + keyblob_words;
  uint32_t plaintext[plaintext_num_words];
  hardened_memcpy(plaintext, (uint32_t *)&key_to_wrap->config, config_words);
  plaintext[config_words] = key_to_wrap->checksum;
  plaintext[config_words + 1] = keyblob_words;
  hardened_memcpy(plaintext + config_words + 2, key_to_wrap->keyblob,
                  keyblob_words);

  // Wrap the key.
  return aes_kwp_wrap(kek, plaintext, sizeof(plaintext), wrapped_key.data);
}

otcrypto_status_t otcrypto_aes_kwp_unwrap(
    otcrypto_const_word32_buf_t wrapped_key,
    const otcrypto_blinded_key_t *key_kek, hardened_bool_t *success,
    otcrypto_blinded_key_t *unwrapped_key) {
  *success = kHardenedBoolFalse;

  if (wrapped_key.data == NULL || key_kek == NULL || key_kek->keyblob == NULL ||
      success == NULL || unwrapped_key == NULL ||
      unwrapped_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the integrity/lengths/mode of the key encryption key, and construct
  // an internal AES key.
  aes_key_t kek;
  HARDENED_TRY(aes_kwp_key_construct(key_kek, &kek));

  // Check that the configuration is aligned.
  if (misalignment32_of((uintptr_t)&unwrapped_key->config) != 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Unwrap the key.
  uint32_t plaintext[wrapped_key.len];
  HARDENED_TRY(aes_kwp_unwrap(kek, wrapped_key.data,
                              wrapped_key.len * sizeof(uint32_t), success,
                              plaintext));

  if (launder32(*success) != kHardenedBoolTrue) {
    *success = kHardenedBoolFalse;
    return OTCRYPTO_OK;
  }
  HARDENED_CHECK_EQ(*success, kHardenedBoolTrue);

  // Set back to false while we check other conditions.
  *success = kHardenedBoolFalse;

  // Extract the key configuration.
  uint32_t config_words = sizeof(otcrypto_key_config_t) / sizeof(uint32_t);
  hardened_memcpy((uint32_t *)&unwrapped_key->config, plaintext, config_words);

  // Extract the checksum and keyblob length.
  unwrapped_key->checksum = plaintext[config_words];
  uint32_t keyblob_words = plaintext[config_words + 1];
  if (keyblob_words != keyblob_num_words(unwrapped_key->config)) {
    *success = kHardenedBoolFalse;
    return OTCRYPTO_OK;
  }

  // Extract the keyblob.
  if (unwrapped_key->keyblob_length != keyblob_words * sizeof(uint32_t)) {
    return OTCRYPTO_BAD_ARGS;
  }
  hardened_memcpy(unwrapped_key->keyblob, plaintext + config_words + 2,
                  keyblob_words);

  // Finally, check the integrity of the key material we unwrapped.
  *success = integrity_blinded_key_check(unwrapped_key);
  return OTCRYPTO_OK;
}
