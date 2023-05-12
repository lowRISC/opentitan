// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/aes.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/aes.h"
#include "sw/device/lib/crypto/impl/aes_gcm/aes_gcm.h"
#include "sw/device/lib/crypto/impl/aes_gcm/ghash.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"

// Check that cipher mode enum from AES driver matches the one from the
// top-level API.
OT_ASSERT_ENUM_VALUE(kAesCipherModeEcb, (uint32_t)kBlockCipherModeEcb);
OT_ASSERT_ENUM_VALUE(kAesCipherModeCbc, (uint32_t)kBlockCipherModeCbc);
OT_ASSERT_ENUM_VALUE(kAesCipherModeCfb, (uint32_t)kBlockCipherModeCfb);
OT_ASSERT_ENUM_VALUE(kAesCipherModeOfb, (uint32_t)kBlockCipherModeOfb);
OT_ASSERT_ENUM_VALUE(kAesCipherModeCtr, (uint32_t)kBlockCipherModeCtr);

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('a', 'e', 's')

// Check GHASH context size against the underlying implementation.
static_assert(sizeof(ghash_context_t) == sizeof(gcm_ghash_context_t),
              "Sizes of GHASH context object for top-level API must match the "
              "underlying implementation.");

crypto_status_t otcrypto_aes_keygen(crypto_blinded_key_t *key) {
  // TODO: Implement AES sideloaded key generation once we have a keymgr
  // driver. In the meantime, non-sideloaded AES keys can simply be generated
  // using the DRBG and key-import functions.
  return OTCRYPTO_NOT_IMPLEMENTED;
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
static status_t aes_key_construct(const crypto_blinded_key_t *blinded_key,
                                  const block_cipher_mode_t aes_mode,
                                  aes_key_t *aes_key) {
  // Key integrity check.
  if (launder32(integrity_blinded_key_check(blinded_key)) !=
      kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(integrity_blinded_key_check(blinded_key),
                    kHardenedBoolTrue);

  // TODO(#15590): add support for sideloaded keys by actuating keymgr here if
  // needed (this requires a keymgr driver).
  if (blinded_key->config.hw_backed != kHardenedBoolFalse) {
    return OTCRYPTO_NOT_IMPLEMENTED;
  }
  aes_key->sideload = kHardenedBoolFalse;

  // Check for null pointer (not allowed for non-sideloaded keys).
  if (blinded_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Set the block cipher mode based on the key mode.
  switch (blinded_key->config.key_mode) {
    case kKeyModeAesEcb:
      aes_key->mode = kAesCipherModeEcb;
      break;
    case kKeyModeAesCbc:
      aes_key->mode = kAesCipherModeCbc;
      break;
    case kKeyModeAesCfb:
      aes_key->mode = kAesCipherModeCfb;
      break;
    case kKeyModeAesOfb:
      aes_key->mode = kAesCipherModeOfb;
      break;
    case kKeyModeAesCtr:
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

  // Get pointers to the individual shares.
  uint32_t *share0;
  uint32_t *share1;
  HARDENED_TRY(keyblob_to_shares(blinded_key, &share0, &share1));
  aes_key->key_shares[0] = share0;
  aes_key->key_shares[1] = share1;

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
static status_t aes_padding_apply(aes_padding_t padding_mode,
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
    case kAesPaddingPkcs7:
      // Pads with value same as the number of padding bytes.
      memset(padding, (uint8_t)padding_len, padding_len);
      padding_written = kHardenedBoolTrue;
      break;
    case kAesPaddingIso9797M2:
      // Pads with 0x80 (0b10000000), followed by zero bytes.
      memset(padding, 0x0, padding_len);
      padding[0] = 0x80;
      padding_written = kHardenedBoolTrue;
      break;
    case kAesPaddingNull:
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
                                      aes_padding_t padding,
                                      size_t *num_blocks) {
  size_t num_full_blocks = plaintext_len / kAesBlockNumBytes;

  if (padding == kAesPaddingNull) {
    // If no padding mode is given, the last block must be full.
    if (num_full_blocks * kAesBlockNumBytes != plaintext_len) {
      return OTCRYPTO_BAD_ARGS;
    }

    *num_blocks = num_full_blocks;
    return OTCRYPTO_OK;
  }
  HARDENED_CHECK_NE(padding, kAesPaddingNull);

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
static status_t get_block(crypto_const_uint8_buf_t input, aes_padding_t padding,
                          size_t index, aes_block_t *block) {
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

crypto_status_t otcrypto_aes_padded_plaintext_length(size_t plaintext_len,
                                                     aes_padding_t aes_padding,
                                                     size_t *padded_len) {
  size_t padded_nblocks;
  HARDENED_TRY(
      num_padded_blocks_get(plaintext_len, aes_padding, &padded_nblocks));
  *padded_len = padded_nblocks * kAesBlockNumBytes;
  return OTCRYPTO_OK;
}

crypto_status_t otcrypto_aes(const crypto_blinded_key_t *key,
                             crypto_uint8_buf_t iv,
                             block_cipher_mode_t aes_mode,
                             aes_operation_t aes_operation,
                             crypto_const_uint8_buf_t cipher_input,
                             aes_padding_t aes_padding,
                             crypto_uint8_buf_t cipher_output) {
  // Check for NULL pointers in input pointers and data buffers.
  if (key == NULL || (aes_mode != kBlockCipherModeEcb && iv.data == NULL) ||
      cipher_input.data == NULL || cipher_output.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Calculate the number of blocks for the input, including the padding for
  // encryption.
  size_t input_nblocks;
  if (aes_operation == kAesOperationEncrypt) {
    HARDENED_TRY(
        num_padded_blocks_get(cipher_input.len, aes_padding, &input_nblocks));
  } else if (aes_operation == kAesOperationDecrypt) {
    // If the operation is decryption, the input length must be divisible by
    // the block size.
    if (launder32(cipher_input.len) % kAesBlockNumBytes != 0) {
      return OTCRYPTO_BAD_ARGS;
    }
    HARDENED_CHECK_EQ(cipher_input.len % kAesBlockNumBytes, 0);
    input_nblocks = cipher_input.len / kAesBlockNumBytes;
  }

  // Check for bad lengths:
  //   - IV must be exactly one block long in all modes except ECB
  //   - Input length must be nonzero.
  //   - Output length must match number of input blocks.
  if (aes_mode != launder32(kAesCipherModeEcb)) {
    HARDENED_CHECK_NE(aes_mode, kAesCipherModeEcb);
    if (launder32(iv.len) != kAesBlockNumBytes) {
      return OTCRYPTO_BAD_ARGS;
    }
    HARDENED_CHECK_EQ(iv.len, kAesBlockNumBytes);
  }
  if (cipher_input.len == 0 ||
      launder32(cipher_output.len) != input_nblocks * kAesBlockNumBytes) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(cipher_output.len, input_nblocks * kAesBlockNumBytes);

  // Load the IV.
  aes_block_t aes_iv;
  // TODO(#17711) Change to `hardened_memcpy`.
  memcpy(aes_iv.data, iv.data, kAesBlockNumBytes);

  // Parse the AES key.
  aes_key_t aes_key;
  HARDENED_TRY(aes_key_construct(key, aes_mode, &aes_key));

  // Start the operation (encryption or decryption).
  switch (aes_operation) {
    case kAesOperationEncrypt:
      HARDENED_TRY(aes_encrypt_begin(aes_key, &aes_iv));
      break;
    case kAesOperationDecrypt:
      HARDENED_TRY(aes_decrypt_begin(aes_key, &aes_iv));
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Perform the cipher operation for all full blocks (excluding last block).
  // The input and output are offset by one, so if unrolled this loop would
  // look like:
  //   aes_update(NULL, input[0]);
  //   aes_update(output[0], input[1]);
  //   aes_update(output[1], input[2]);
  //   ...
  // See the AES driver for details.
  aes_block_t block_in;
  aes_block_t block_out;
  size_t i;
  for (i = 0; launder32(i) < input_nblocks; i++) {
    HARDENED_TRY(get_block(cipher_input, aes_padding, i, &block_in));

    // Call the AES cipher and copy data to output buffer if needed.
    if (launder32(i) == 0) {
      HARDENED_CHECK_EQ(i, 0);
      HARDENED_TRY(aes_update(/*dest=*/NULL, &block_in));
    } else {
      HARDENED_TRY(aes_update(&block_out, &block_in));
      // TODO(#17711) Change to `hardened_memcpy`.
      memcpy(&cipher_output.data[(i - 1) * kAesBlockNumBytes], block_out.data,
             kAesBlockNumBytes);
    }
  }

  // Check that the loop ran for the correct number of iterations.
  HARDENED_CHECK_EQ(i, input_nblocks);

  // Retrieve the output from the final block (providing no input).
  HARDENED_TRY(aes_update(&block_out, /*src=*/NULL));
  // TODO(#17711) Change to `hardened_memcpy`.
  memcpy(&cipher_output.data[(input_nblocks - 1) * kAesBlockNumBytes],
         block_out.data, kAesBlockNumBytes);

  // Deinitialize the AES block.
  HARDENED_TRY(aes_end());

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
static status_t aes_gcm_key_construct(const crypto_blinded_key_t *blinded_key,
                                      aes_key_t *aes_key) {
  // Key integrity check.
  if (launder32(integrity_blinded_key_check(blinded_key)) !=
      kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(integrity_blinded_key_check(blinded_key),
                    kHardenedBoolTrue);

  // Check the key mode.
  if (launder32((uint32_t)blinded_key->config.key_mode) != kKeyModeAesGcm) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(blinded_key->config.key_mode, kKeyModeAesGcm);

  // Set the mode of the underlying AES key to CTR (since this is the
  // underlying block cipher mode for GCM).
  aes_key->mode = kAesCipherModeCtr;

  // TODO(#15590): add support for sideloaded keys by actuating keymgr here if
  // needed (this requires a keymgr driver).
  if (blinded_key->config.hw_backed != kHardenedBoolFalse) {
    return OTCRYPTO_NOT_IMPLEMENTED;
  }
  aes_key->sideload = kHardenedBoolFalse;

  // Check for null pointer (not allowed for non-sideloaded keys).
  if (blinded_key->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Set the AES key length (in words).
  aes_key->key_len = keyblob_share_num_words(blinded_key->config);

  // Get pointers to the individual shares.
  uint32_t *share0;
  uint32_t *share1;
  HARDENED_TRY(keyblob_to_shares(blinded_key, &share0, &share1));
  aes_key->key_shares[0] = share0;
  aes_key->key_shares[1] = share1;

  return OTCRYPTO_OK;
}

/**
 * Checks if the given byte-length matches the tag length enum value.
 *
 * @param byte_len Allocated tag length in bytes.
 * @param tag_len Allocated tag length in bytes.
 * @return OK if the tag length is acceptable, BAD_ARGS otherwise.
 */
status_t aes_gcm_check_tag_length(size_t byte_len, aead_gcm_tag_len_t tag_len) {
  size_t bit_len = 0;
  switch (launder32(tag_len)) {
    case kAeadGcmTagLen128:
      HARDENED_CHECK_EQ(tag_len, kAeadGcmTagLen128);
      bit_len = 128;
      break;
    case kAeadGcmTagLen120:
      HARDENED_CHECK_EQ(tag_len, kAeadGcmTagLen120);
      bit_len = 120;
      break;
    case kAeadGcmTagLen112:
      HARDENED_CHECK_EQ(tag_len, kAeadGcmTagLen112);
      bit_len = 112;
      break;
    case kAeadGcmTagLen104:
      HARDENED_CHECK_EQ(tag_len, kAeadGcmTagLen104);
      bit_len = 104;
      break;
    case kAeadGcmTagLen96:
      HARDENED_CHECK_EQ(tag_len, kAeadGcmTagLen96);
      bit_len = 96;
      break;
    case kAeadGcmTagLen64:
      HARDENED_CHECK_EQ(tag_len, kAeadGcmTagLen64);
      bit_len = 64;
      break;
    case kAeadGcmTagLen32:
      HARDENED_CHECK_EQ(tag_len, kAeadGcmTagLen32);
      bit_len = 32;
      break;
    default:
      // Invalid tag length.
      return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_GT(bit_len, 0);

  if (launder32(byte_len) * 8 != bit_len) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(byte_len * 8, bit_len);

  // Extra hardening checks; the byte-length must be nonzero, a multiple of 2,
  // and at most the size of an AES block.
  HARDENED_CHECK_EQ(byte_len % 2, 0);
  HARDENED_CHECK_LT(0, byte_len);
  HARDENED_CHECK_LE(byte_len, kAesBlockNumBytes);

  return OTCRYPTO_OK;
}

crypto_status_t otcrypto_aes_encrypt_gcm(const crypto_blinded_key_t *key,
                                         crypto_const_uint8_buf_t plaintext,
                                         crypto_const_uint8_buf_t iv,
                                         crypto_const_uint8_buf_t aad,
                                         aead_gcm_tag_len_t tag_len,
                                         crypto_uint8_buf_t *ciphertext,
                                         crypto_uint8_buf_t *auth_tag) {
  // Check for NULL pointers in input pointers and required-nonzero-length data
  // buffers.
  if (key == NULL || iv.data == NULL || ciphertext == NULL ||
      auth_tag == NULL || auth_tag->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Conditionally check for null pointers in data buffers that may be
  // 0-length.
  if ((aad.len != 0 && aad.data == NULL) ||
      (ciphertext->len != 0 && ciphertext->data == NULL) ||
      (plaintext.len != 0 && plaintext.data == NULL)) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Ensure the plaintext and ciphertext lengths match.
  if (launder32(ciphertext->len) != plaintext.len) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(ciphertext->len, plaintext.len);

  // Check the tag length.
  HARDENED_TRY(aes_gcm_check_tag_length(auth_tag->len, tag_len));

  // Construct the AES key.
  aes_key_t aes_key;
  HARDENED_TRY(aes_gcm_key_construct(key, &aes_key));

  // Call the core encryption operation.
  HARDENED_TRY(aes_gcm_encrypt(aes_key, iv.len, iv.data, plaintext.len,
                               plaintext.data, aad.len, aad.data, auth_tag->len,
                               auth_tag->data, ciphertext->data));

  return OTCRYPTO_OK;
}

crypto_status_t otcrypto_aes_decrypt_gcm(
    const crypto_blinded_key_t *key, crypto_const_uint8_buf_t ciphertext,
    crypto_const_uint8_buf_t iv, crypto_const_uint8_buf_t aad,
    aead_gcm_tag_len_t tag_len, crypto_const_uint8_buf_t auth_tag,
    crypto_uint8_buf_t *plaintext, hardened_bool_t *success) {
  // Check for NULL pointers in input pointers and required-nonzero-length data
  // buffers.
  if (key == NULL || iv.data == NULL || plaintext == NULL ||
      auth_tag.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Conditionally check for null pointers in data buffers that may be
  // 0-length.
  if ((aad.len != 0 && aad.data == NULL) ||
      (ciphertext.len != 0 && ciphertext.data == NULL) ||
      (plaintext->len != 0 && plaintext->data == NULL)) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Construct the AES key.
  aes_key_t aes_key;
  HARDENED_TRY(aes_gcm_key_construct(key, &aes_key));

  // Ensure the plaintext and ciphertext lengths match.
  if (launder32(ciphertext.len) != plaintext->len) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(ciphertext.len, plaintext->len);

  // Check the tag length.
  HARDENED_TRY(aes_gcm_check_tag_length(auth_tag.len, tag_len));

  // Call the core decryption operation.
  HARDENED_TRY(aes_gcm_decrypt(aes_key, iv.len, iv.data, ciphertext.len,
                               ciphertext.data, aad.len, aad.data, auth_tag.len,
                               auth_tag.data, plaintext->data, success));

  return OTCRYPTO_OK;
}

crypto_status_t otcrypto_gcm_ghash_init(const crypto_blinded_key_t *hash_subkey,
                                        gcm_ghash_context_t *ctx) {
  if (hash_subkey == NULL || ctx == NULL || hash_subkey->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Key integrity check.
  if (launder32(integrity_blinded_key_check(hash_subkey)) !=
      kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(integrity_blinded_key_check(hash_subkey),
                    kHardenedBoolTrue);

  // Check the key mode.
  if (launder32((uint32_t)hash_subkey->config.key_mode) != kKeyModeAesGcm) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(hash_subkey->config.key_mode, kKeyModeAesGcm);

  // The hash subkey cannot be sideloaded, since GHASH is implemented in
  // software.
  if (hash_subkey->config.hw_backed != kHardenedBoolFalse) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Get pointers to the individual shares of the blinded key.
  uint32_t *share0;
  uint32_t *share1;
  HARDENED_TRY(keyblob_to_shares(hash_subkey, &share0, &share1));

  // Combine the shares; the underlying GHASH operation is not yet hardened, so
  // we need to unmask the key.
  uint32_t unmasked_key[kGhashBlockNumWords];
  for (size_t i = 0; i < kGhashBlockNumWords; i++) {
    unmasked_key[i] = share0[i] ^ share1[i];
  }

  // Set the key for the GHASH context and start a GHASH operation.
  ghash_context_t *gctx = (ghash_context_t *)ctx->ctx;
  ghash_init_subkey(unmasked_key, gctx);
  ghash_init(gctx);

  return OTCRYPTO_OK;
}

crypto_status_t otcrypto_gcm_ghash_update(gcm_ghash_context_t *ctx,
                                          crypto_const_uint8_buf_t input) {
  if (ctx == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (input.len != 0 && input.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  ghash_context_t *gctx = (ghash_context_t *)ctx->ctx;
  ghash_update(gctx, input.len, input.data);

  return OTCRYPTO_OK;
}

crypto_status_t otcrypto_gcm_ghash_final(gcm_ghash_context_t *ctx,
                                         crypto_uint8_buf_t digest) {
  if (ctx == NULL || digest.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (launder32(digest.len) != kGhashBlockNumBytes) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(digest.len, kGhashBlockNumBytes);

  ghash_context_t *gctx = (ghash_context_t *)ctx->ctx;
  uint32_t result[kGhashBlockNumBytes];
  ghash_final(gctx, result);

  // TODO(#17711) Change to `hardened_memcpy`.
  memcpy(digest.data, result, sizeof(result));

  return OTCRYPTO_OK;
}

crypto_status_t otcrypto_aes_gcm_gctr(const crypto_blinded_key_t *key,
                                      crypto_const_uint8_buf_t icb,
                                      crypto_const_uint8_buf_t input,
                                      crypto_uint8_buf_t output) {
  if (key == NULL || icb.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  if ((input.len != 0 && input.data == NULL) ||
      (output.len != 0 && output.data == NULL)) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (launder32(icb.len) != kAesBlockNumBytes) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(icb.len, kAesBlockNumBytes);

  if (launder32(input.len) != output.len) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(input.len, output.len);

  // Construct the AES key.
  aes_key_t aes_key;
  HARDENED_TRY(aes_gcm_key_construct(key, &aes_key));

  // Construct the initial counter block.
  aes_block_t aes_icb;
  // TODO(#17711) Change to `hardened_memcpy`.
  memcpy(aes_icb.data, icb.data, kAesBlockNumBytes);

  HARDENED_TRY(
      aes_gcm_gctr(aes_key, &aes_icb, input.len, input.data, output.data));

  return OTCRYPTO_OK;
}

crypto_status_t otcrypto_aes_kwp_encrypt(
    const crypto_blinded_key_t *key_to_wrap,
    const crypto_blinded_key_t *key_kek, crypto_uint8_buf_t *wrapped_key) {
  // TODO: AES-KWP is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

crypto_status_t otcrypto_aes_kwp_decrypt(crypto_const_uint8_buf_t wrapped_key,
                                         const crypto_blinded_key_t *key_kek,
                                         crypto_blinded_key_t *unwrapped_key) {
  // TODO: AES-KWP is not yet implemented.
  return OTCRYPTO_NOT_IMPLEMENTED;
}
