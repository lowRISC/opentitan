// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/aes.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/aes.h"
#include "sw/device/lib/crypto/impl/integrity_check.h"
#include "sw/device/lib/crypto/include/datatypes.h"

// Check that cipher mode enum from AES driver matches the one from the
// top-level API.
OT_ASSERT_ENUM_VALUE(kAesCipherModeEcb, kBlockCipherModeEcb);
OT_ASSERT_ENUM_VALUE(kAesCipherModeCbc, kBlockCipherModeCbc);
OT_ASSERT_ENUM_VALUE(kAesCipherModeCfb, kBlockCipherModeCfb);
OT_ASSERT_ENUM_VALUE(kAesCipherModeOfb, kBlockCipherModeOfb);
OT_ASSERT_ENUM_VALUE(kAesCipherModeCtr, kBlockCipherModeCtr);

/**
 * Extract an AES key from the blinded key struct.
 *
 * @param blinded_key Blinded key struct.
 * @param aes_mode Block cipher mode.
 * @param[out] aes_key Destination AES key struct.
 * @return Result of the operation.
 */
static crypto_status_t construct_aes_key(
    const crypto_blinded_key_t *blinded_key, const block_cipher_mode_t aes_mode,
    aes_key_t *aes_key) {
  // TODO(#15590): add support for sideloaded keys by actuating keymgr here if
  // needed (this requires a keymgr driver).
  if (blinded_key->config.hw_backed != kHardenedBoolFalse) {
    return kCryptoStatusBadArgs;
  }
  aes_key->sideload = kHardenedBoolFalse;

  // Set the block cipher mode based on the key mode.
  switch (blinded_key->config.key_mode) {
    case kKeyModeAesEcb:
      aes_key->mode = kBlockCipherModeEcb;
      break;
    case kKeyModeAesCbc:
      aes_key->mode = kBlockCipherModeCbc;
      break;
    case kKeyModeAesCfb:
      aes_key->mode = kBlockCipherModeCfb;
      break;
    case kKeyModeAesOfb:
      aes_key->mode = kBlockCipherModeOfb;
      break;
    case kKeyModeAesCtr:
      aes_key->mode = kBlockCipherModeCtr;
      break;
    default:
      return kCryptoStatusBadArgs;
  }

  // Check that the key mode matches the requested block cipher mode.
  if (aes_key->mode != aes_mode) {
    return kCryptoStatusBadArgs;
  }

  // Determine the AES key length.
  size_t key_share_nbytes = blinded_key->config.key_length;
  size_t key_share_nwords = key_share_nbytes / sizeof(uint32_t);
  aes_key->key_len = key_share_nwords;

  // The blinded key is represented in two shares; the keyblob should be the
  // length of exactly two times the key length.
  if (blinded_key->keyblob_length != key_share_nbytes * 2) {
    return kCryptoStatusBadArgs;
  }

  // Set pointers to the two key shares. One share starts at the beginning of
  // the key blob, and the other starts exactly halfway through.
  aes_key->key_shares[0] = blinded_key->keyblob;
  aes_key->key_shares[1] = &blinded_key->keyblob[key_share_nwords];

  return kCryptoStatusOK;
}

/**
 * Applies the specified mode of AES padding to the block.
 *
 * Modifies only positions on and after index `last_block_len` in the
 * `padded_block`; real input may be written to the initial locations either
 * before or after calling this function.
 *
 * @param aes_padding Padding mode.
 * @param last_block_len Length of real input in this block.
 * @param[out] padded_block Destination padded block.
 * @return Result of the operation.
 */
static crypto_status_t aes_padding_apply(aes_padding_t aes_padding,
                                         const size_t last_block_len,
                                         aes_block_t *padded_block) {
  size_t padding_len = kAesBlockNumBytes - last_block_len;
  switch (aes_padding) {
    case kAesPaddingPkcs7:
      // Pads with value same as the number of padding bytes.
      if (padding_len > 0) {
        memset(&padded_block->data[last_block_len], padding_len, padding_len);
      }
      break;
    case kAesPaddingIso9797M2:
      // Pads with 0x80 (10000000), followed by zero bytes.
      if (padding_len > 0) {
        padded_block->data[last_block_len] = 0x80;
        if (padding_len > 1) {
          memset(&padded_block->data[last_block_len + 1], 0x0, padding_len - 1);
        }
      }
      break;
    case kAesPaddingNull:
      // No padding; input length must be an exact multiple of block size.
      if (padding_len != 0) {
        return kCryptoStatusBadArgs;
      }
      break;
    default:
      // TODO(#15591): Add any other padding modes that will be included in the
      // final API.
      return kCryptoStatusBadArgs;
  }
  return kCryptoStatusOK;
}

crypto_status_t otcrypto_aes(const crypto_blinded_key_t *key,
                             crypto_uint8_buf_t iv,
                             block_cipher_mode_t aes_mode,
                             aes_operation_t aes_operation,
                             crypto_const_uint8_buf_t cipher_input,
                             aes_padding_t aes_padding,
                             crypto_uint8_buf_t *cipher_output) {
  // Check for NULL pointers in input pointers and data buffers.
  if (key == NULL || cipher_output == NULL || iv.data == NULL ||
      cipher_input.data == NULL || cipher_output->data == NULL) {
    return kCryptoStatusBadArgs;
  }

  // Key integrity check.
  if (blinded_key_integrity_check(key) != kHardenedBoolTrue) {
    return kCryptoStatusBadArgs;
  }

  // Calculate the number of input blocks by rounding up to the nearest full
  // block.
  size_t input_nblocks =
      (cipher_input.len + (kAesBlockNumBytes - 1)) / kAesBlockNumBytes;

  // Check for bad lengths:
  //   - IV must be exactly one block long.
  //   - Input length must be nonzero.
  //   - Output length must match number of input blocks.
  if (iv.len != kAesBlockNumBytes || cipher_input.len == 0 ||
      cipher_output->len != input_nblocks * kAesBlockNumBytes) {
    return kCryptoStatusBadArgs;
  }

  // Load the IV.
  aes_block_t aes_iv;
  memcpy(aes_iv.data, iv.data, iv.len);

  // Parse the AES key.
  aes_key_t aes_key;
  crypto_status_t err = construct_aes_key(key, aes_mode, &aes_key);
  if (err != kCryptoStatusOK) {
    return err;
  }

  // Start the operation (encryption or decryption).
  aes_error_t aes_err;
  switch (aes_operation) {
    case kAesOperationEncrypt:
      aes_err = aes_encrypt_begin(aes_key, &aes_iv);
      if (aes_err != kAesOk) {
        return kCryptoStatusInternalError;
      }
      break;
    case kAesOperationDecrypt:
      aes_err = aes_decrypt_begin(aes_key, &aes_iv);
      if (aes_err != kAesOk) {
        return kCryptoStatusInternalError;
      }
      break;
    default:
      return kCryptoStatusBadArgs;
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
    // Construct the next block of input. Use `memcpy` to accomodate strict
    // aliasing rules.
    if (i == input_nblocks - 1) {
      // Last block; pad if needed.
      size_t last_block_len = cipher_input.len - (i * kAesBlockNumBytes);
      memcpy(block_in.data, &cipher_input.data[i * kAesBlockNumBytes],
             last_block_len);
      err = aes_padding_apply(aes_padding, last_block_len, &block_in);
      if (err != kCryptoStatusOK) {
        return err;
      }
    } else {
      memcpy(block_in.data, &cipher_input.data[i * kAesBlockNumBytes],
             kAesBlockNumBytes);
    }

    // Call the AES cipher and copy data to output buffer if needed.
    if (i == 0) {
      aes_err = aes_update(/*dest*/ NULL, &block_in);
      if (aes_err != kAesOk) {
        return kCryptoStatusInternalError;
      }
    } else {
      aes_err = aes_update(&block_out, &block_in);
      if (aes_err != kAesOk) {
        return kCryptoStatusInternalError;
      }
      memcpy(&cipher_output->data[(i - 1) * kAesBlockNumBytes], block_out.data,
             kAesBlockNumBytes);
    }
  }

  // Check that the loop ran for the correct number of iterations.
  HARDENED_CHECK_EQ(i, input_nblocks);

  // Retrieve the output from the final block (providing no input).
  aes_err = aes_update(&block_out, /*src*/ NULL);
  if (aes_err != kAesOk) {
    return kCryptoStatusInternalError;
  }
  memcpy(&cipher_output->data[(input_nblocks - 1) * kAesBlockNumBytes],
         block_out.data, kAesBlockNumBytes);

  // Deinitialize the AES block.
  aes_err = aes_end();
  if (aes_err != kAesOk) {
    return kCryptoStatusInternalError;
  }

  return kCryptoStatusOK;
}
