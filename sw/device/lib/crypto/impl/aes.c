// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/aes.h"

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/aes.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/drivers/keymgr.h"
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

/**
 * Extract an AES key from the blinded key struct.
 *
 * Also performs integrity, mode, and null-pointer checks on the key. This
 * function is only for basic AES modes; do not use for AES-GCM or AES-KWP keys
 * since they will fail the mode check.
 *
 * Re-masks the key after checking its integrity. The caller should ensure the
 * entropy complex is up before calling this function.
 *
 * @param blinded_key Blinded key struct.
 * @param aes_mode Block cipher mode.
 * @param[out] aes_key Destination AES key struct.
 * @return Result of the operation.
 */
static status_t aes_key_construct(otcrypto_blinded_key_t *blinded_key,
                                  const otcrypto_aes_mode_t aes_mode,
                                  aes_key_t *aes_key) {
  // Key integrity check.
  if (integrity_blinded_key_check(blinded_key) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(integrity_blinded_key_check(blinded_key)),
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
    // Remask the key.
    HARDENED_TRY(keyblob_remask(blinded_key));

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
  otcrypto_key_mode_t blinded_key_mode_used = launder32(0);
  switch (blinded_key->config.key_mode) {
    case kOtcryptoKeyModeAesEcb:
      aes_key->mode = kAesCipherModeEcb;
      blinded_key_mode_used =
          launder32(blinded_key_mode_used) | kOtcryptoKeyModeAesEcb;
      break;
    case kOtcryptoKeyModeAesCbc:
      aes_key->mode = launder32(kAesCipherModeCbc);
      blinded_key_mode_used =
          launder32(blinded_key_mode_used) | kOtcryptoKeyModeAesCbc;
      break;
    case kOtcryptoKeyModeAesCfb:
      aes_key->mode = launder32(kAesCipherModeCfb);
      blinded_key_mode_used =
          launder32(blinded_key_mode_used) | kOtcryptoKeyModeAesCfb;
      break;
    case kOtcryptoKeyModeAesOfb:
      aes_key->mode = launder32(kAesCipherModeOfb);
      blinded_key_mode_used =
          launder32(blinded_key_mode_used) | kOtcryptoKeyModeAesOfb;
      break;
    case kOtcryptoKeyModeAesCtr:
      aes_key->mode = launder32(kAesCipherModeCtr);
      blinded_key_mode_used =
          launder32(blinded_key_mode_used) | kOtcryptoKeyModeAesCtr;
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
  // Check if we landed in the correct case statement. Use ORs for this to
  // avoid that multiple cases were executed.
  HARDENED_CHECK_EQ(launder32(blinded_key_mode_used),
                    blinded_key->config.key_mode);

  // Check that the key mode matches the requested block cipher mode.
  if (memcmp(&aes_key->mode, &aes_mode, sizeof(aes_key->mode)) != 0) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(aes_key->mode, aes_mode);

  // Set the AES key length (in words).
  aes_key->key_len = keyblob_share_num_words(blinded_key->config);

  if (aes_key->sideload == kHardenedBoolFalse) {
    // Create the checksum of the key and store it in the key structure.
    aes_key->checksum = aes_key_integrity_checksum(aes_key);
  }

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
  otcrypto_aes_padding_t padding_written = launder32(0);
  switch (launder32(padding_mode)) {
    case kOtcryptoAesPaddingPkcs7:
      // Pads with value same as the number of padding bytes.
      memset(padding, (uint8_t)padding_len, padding_len);
      padding_written = launder32(padding_written) | kOtcryptoAesPaddingPkcs7;
      break;
    case kOtcryptoAesPaddingIso9797M2:
      // Pads with 0x80 (0b10000000), followed by zero bytes.
      memset(padding, 0x0, padding_len);
      padding[0] = 0x80;
      padding_written =
          launder32(padding_written) | kOtcryptoAesPaddingIso9797M2;
      break;
    case kOtcryptoAesPaddingNull:
      // This routine should not be called if padding is not needed.
      return OTCRYPTO_RECOV_ERR;
    default:
      // Unrecognized padding mode.
      return OTCRYPTO_BAD_ARGS;
  }
  // Check if we landed in the correct case statement. Use ORs for this to
  // avoid that multiple cases were executed.
  HARDENED_CHECK_EQ(launder32(padding_written), padding_mode);

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
 * Uses hardening primitives internally that consume entropy; check the entropy
 * complex is up before calling.
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

  // Randomize the destination buffer.
  HARDENED_TRY(hardened_memshred(block->data, ARRAYSIZE(block->data)));

  if (index < num_full_blocks) {
    HARDENED_CHECK_LT(index, num_full_blocks);
    // No need to worry about padding, just copy the data into the output
    // block.
    // Byte buffers passed as input may not be word-aligned, so we cannot
    // use `hardened_memcpy`.
    // This is acceptable because the data is non-sensitive.
    memcpy(block->data, &input.data[index * kAesBlockNumBytes],
           kAesBlockNumBytes);
    return OTCRYPTO_OK;
  }
  HARDENED_CHECK_GE(launder32(index), num_full_blocks);

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

/**
 * Performs the AES operation.
 *
 * @param key Pointer to the blinded key struct with key shares.
 * @param iv Initialization vector, used for CBC, CFB, OFB, CTR modes. May be
 *           NULL if mode is ECB.
 * @param aes_mode Required AES mode of operation.
 * @param aes_operation Required AES operation (encrypt or decrypt).
 * @param cipher_input Input data to be ciphered.
 * @param aes_padding Padding scheme to be used for the data.
 * @param[out] cipher_output Output data after cipher operation.
 * @return The result of the cipher operation.
 */
static otcrypto_status_t otcrypto_aes_impl(
    otcrypto_blinded_key_t *key, otcrypto_word32_buf_t iv,
    otcrypto_aes_mode_t aes_mode, otcrypto_aes_operation_t aes_operation,
    otcrypto_const_byte_buf_t cipher_input, otcrypto_aes_padding_t aes_padding,
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
  if (aes_mode == kAesCipherModeEcb) {
    HARDENED_CHECK_EQ(launder32(aes_mode), kAesCipherModeEcb);
  } else {
    HARDENED_CHECK_NE(launder32(aes_mode), kAesCipherModeEcb);

    // The IV must be exactly one block long.
    if (iv.len != kAesBlockNumWords) {
      return OTCRYPTO_BAD_ARGS;
    }
    HARDENED_CHECK_EQ(launder32(iv.len), kAesBlockNumWords);
    HARDENED_TRY(hardened_memcpy(aes_iv.data, iv.data, kAesBlockNumWords));
  }

  // Parse the AES key.
  aes_key_t aes_key;
  HARDENED_TRY(aes_key_construct(key, aes_mode, &aes_key));

  // Start the operation (encryption or decryption).
  otcrypto_aes_operation_t aes_operation_started = launder32(0);
  switch (aes_operation) {
    case kOtcryptoAesOperationEncrypt:
      HARDENED_TRY(aes_encrypt_begin(aes_key, &aes_iv));
      aes_operation_started =
          launder32(aes_operation_started) | kOtcryptoAesOperationEncrypt;
      break;
    case kOtcryptoAesOperationDecrypt:
      HARDENED_TRY(aes_decrypt_begin(aes_key, &aes_iv));
      aes_operation_started =
          launder32(aes_operation_started) | kOtcryptoAesOperationDecrypt;
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
  // Check if we landed in the correct case statement. Use ORs for this to
  // avoid that multiple cases were executed.
  HARDENED_CHECK_EQ(launder32(aes_operation_started), aes_operation);

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
    HARDENED_TRY(aes_update(/*dest=*/NULL, &block_in));
  }
  // Check that the loop ran for the correct number of iterations.
  HARDENED_CHECK_EQ(i, block_offset);

  // Call the AES cipher while providing new input and copying data to the
  // output buffer.
  for (i = block_offset; launder32(i) < input_nblocks; ++i) {
    HARDENED_TRY(get_block(cipher_input, aes_padding, i, &block_in));
    HARDENED_TRY(hardened_memshred(block_out.data, ARRAYSIZE(block_out.data)));
    HARDENED_TRY(aes_update(&block_out, &block_in));
    // Byte buffers passed as input may not be word-aligned, so we cannot
    // use `hardened_memcpy`.
    // This is acceptable because the data is non-sensitive.
    memcpy(&cipher_output.data[(i - block_offset) * kAesBlockNumBytes],
           block_out.data, kAesBlockNumBytes);
  }
  // Check that the loop ran for the correct number of iterations.
  HARDENED_CHECK_EQ(i, input_nblocks);

  // Retrieve the output from the final `block_offset` blocks (providing no
  // input).
  for (i = block_offset; i > 0; --i) {
    HARDENED_TRY(aes_update(&block_out, /*src=*/NULL));
    // Byte buffers passed as input may not be word-aligned, so we cannot
    // use `hardened_memcpy`.
    // This is acceptable because the data is non-sensitive.
    memcpy(&cipher_output.data[(input_nblocks - i) * kAesBlockNumBytes],
           block_out.data, kAesBlockNumBytes);
  }
  // Check that the loop ran for the correct number of iterations.
  HARDENED_CHECK_EQ(launder32(i), 0);

  // Verify the CTRL and CTRL_AUX registers.

  // Since this is a checking mechanism itself, we do not add extra redundancy
  // to the if loop.
  hardened_bool_t encrypt = kHardenedBoolTrue;
  if (aes_operation == kOtcryptoAesOperationDecrypt)
    encrypt = kHardenedBoolFalse;
  HARDENED_TRY(aes_verify_ctrl_reg(aes_key, encrypt));
  HARDENED_TRY(aes_verify_ctrl_aux_reg());

  // Deinitialize the AES block and update the IV (in ECB mode, skip the IV).
  if (aes_mode == kAesCipherModeEcb) {
    HARDENED_TRY(aes_end(NULL));
  } else {
    HARDENED_TRY(aes_end(&aes_iv));
    HARDENED_TRY(hardened_memcpy(iv.data, aes_iv.data, kAesBlockNumWords));
  }

  // In case the key was sideloaded, clear it.
  return keymgr_sideload_clear_aes();
}

otcrypto_status_t otcrypto_aes(otcrypto_blinded_key_t *key,
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

  // Ensure the entropy complex is initialized.
  HARDENED_TRY(entropy_complex_check());

  if (launder32(key->config.security_level) == kOtcryptoKeySecurityLevelLow) {
    HARDENED_CHECK_EQ(key->config.security_level, kOtcryptoKeySecurityLevelLow);
    // No additional FI protection.
    return otcrypto_aes_impl(key, iv, aes_mode, aes_operation, cipher_input,
                             aes_padding, cipher_output);
  } else {
    HARDENED_CHECK_NE(key->config.security_level, kOtcryptoKeySecurityLevelLow);
    // Protect the AES computation against faults. Recomputes the ciphertext or
    // plaintexts after the actual AES operation and compares it to the input.

    // Copy the IV for the second AES computation.
    uint32_t iv_data[iv.len];
    memcpy(iv_data, iv.data, sizeof(iv_data));
    otcrypto_word32_buf_t iv_redundant = {
        .data = iv_data,
        .len = iv.len,
    };

    // First AES operation using the intended AES mode (encryption or
    // decryption).
    HARDENED_TRY(otcrypto_aes_impl(key, iv, aes_mode, aes_operation,
                                   cipher_input, aes_padding, cipher_output));

    // Second AES operation using the counterpart of the AES mode (decryption or
    // encryption).
    otcrypto_aes_operation_t aes_operation_inverse;
    size_t len_bytes;
    if (aes_operation == kOtcryptoAesOperationEncrypt) {
      aes_operation_inverse = kOtcryptoAesOperationDecrypt;
      len_bytes = cipher_output.len;
    } else {
      aes_operation_inverse = kOtcryptoAesOperationEncrypt;
      TRY(otcrypto_aes_padded_plaintext_length(cipher_output.len, aes_padding,
                                               &len_bytes));
    }

    // Create the input buffer that contains the cipher_output of the first AES
    // operation.
    otcrypto_const_byte_buf_t cipher_input_redundant = {
        .data = cipher_output.data,
        .len = cipher_output.len,
    };
    // Create the output buffer.
    uint32_t output_buf[len_bytes / sizeof(uint32_t)];
    otcrypto_byte_buf_t cipher_input_recomputed = {
        .data = (unsigned char *)output_buf,
        .len = len_bytes,
    };
    HARDENED_TRY(otcrypto_aes_impl(
        key, iv_redundant, aes_mode, aes_operation_inverse,
        cipher_input_redundant, aes_padding, cipher_input_recomputed));

    // Comparison.
    HARDENED_CHECK_EQ(
        consttime_memeq_byte(cipher_input.data, output_buf, cipher_input.len),
        kHardenedBoolTrue);
  }

  return OTCRYPTO_OK;
}
