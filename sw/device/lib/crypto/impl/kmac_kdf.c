// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/kmac_kdf.h"

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/crypto/drivers/kmac.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('k', 'k', 'd')

otcrypto_status_t otcrypto_kmac_kdf(
    otcrypto_blinded_key_t *key_derivation_key,
    const otcrypto_const_byte_buf_t label,
    const otcrypto_const_byte_buf_t context,
    otcrypto_blinded_key_t *output_key_material) {
  // Check NULL pointers.
  if (key_derivation_key->keyblob == NULL || output_key_material == NULL ||
      output_key_material->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check for null label with nonzero length.
  if (label.data == NULL && label.len != 0) {
    return OTCRYPTO_BAD_ARGS;
  }
  // Because of KMAC HWIPs prefix limitation, `label` should not exceed
  // `kKmacCustStrMaxSize` bytes.
  if (label.len > kKmacCustStrMaxSize) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check for null context with nonzero length.
  if (context.data == NULL && context.len != 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the private key checksum.
  if (launder32(integrity_blinded_key_check(key_derivation_key)) !=
      kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(integrity_blinded_key_check(key_derivation_key),
                    kHardenedBoolTrue);

  // Check `key_len` is supported by KMAC HWIP.
  // The set of supported key sizes is {128, 192, 256, 384, 512}.
  HARDENED_TRY(kmac_key_length_check(key_derivation_key->config.key_length));

  kmac_blinded_key_t kmac_key = {
      .share0 = NULL,
      .share1 = NULL,
      .hw_backed = key_derivation_key->config.hw_backed,
      .len = key_derivation_key->config.key_length,
  };

  // Validate key length of `key_derivation_key`.
  if (key_derivation_key->config.hw_backed == kHardenedBoolTrue) {
    // Check that 1) key size matches sideload port size, 2) keyblob length
    // matches diversification length.
    if (keyblob_share_num_words(key_derivation_key->config) *
            sizeof(uint32_t) !=
        kKmacSideloadKeyLength / 8) {
      return OTCRYPTO_BAD_ARGS;
    }
    // Configure keymgr with diversification input and then generate the
    // sideload key.
    keymgr_diversification_t diversification;
    // Diversification call also checks that
    // `key_derivation_key->keyblob_length` is 8 words long.
    HARDENED_TRY(keyblob_to_keymgr_diversification(key_derivation_key,
                                                   &diversification));
    HARDENED_TRY(keymgr_generate_key_kmac(diversification));
  } else if (key_derivation_key->config.hw_backed == kHardenedBoolFalse) {
    // Remask the key.
    HARDENED_TRY(keyblob_remask(key_derivation_key));

    if (key_derivation_key->keyblob_length !=
        keyblob_num_words(key_derivation_key->config) * sizeof(uint32_t)) {
      return OTCRYPTO_BAD_ARGS;
    }
    HARDENED_TRY(keyblob_to_shares(key_derivation_key, &kmac_key.share0,
                                   &kmac_key.share1));
  } else {
    return OTCRYPTO_BAD_ARGS;
  }

  // At the moment, `kmac_kmac_128/256` only supports word-sized digest lengths.
  if (output_key_material->config.key_length % sizeof(uint32_t) != 0) {
    return OTCRYPTO_NOT_IMPLEMENTED;
  }

  // Output key cannot be hardware-backed.
  if (output_key_material->config.hw_backed != kHardenedBoolFalse) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(output_key_material->config.hw_backed, kHardenedBoolFalse);

  // Check the keyblob length.
  if (output_key_material->keyblob_length !=
      keyblob_num_words(output_key_material->config) * sizeof(uint32_t)) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Randomize the keyblob memory.
  hardened_memshred(output_key_material->keyblob,
                    keyblob_num_words(output_key_material->config));

  switch (launder32(key_derivation_key->config.key_mode)) {
    case kOtcryptoKeyModeKdfKmac128: {
      HARDENED_CHECK_EQ(key_derivation_key->config.key_mode,
                        kOtcryptoKeyModeKdfKmac128);
      // No need to further check key size against security level because
      // `kmac_key_length_check` ensures that the key is at least 128-bit.
      HARDENED_TRY(kmac_kmac_128(
          &kmac_key, /*masked_digest=*/kHardenedBoolTrue, context.data,
          context.len, label.data, label.len, output_key_material->keyblob,
          output_key_material->config.key_length / sizeof(uint32_t)));
      break;
    }
    case kOtcryptoKeyModeKdfKmac256: {
      HARDENED_CHECK_EQ(key_derivation_key->config.key_mode,
                        kOtcryptoKeyModeKdfKmac256);
      // Check that key size matches the security strength. It should be at
      // least 256-bit.
      if (key_derivation_key->config.key_length < 256 / 8) {
        return OTCRYPTO_BAD_ARGS;
      }
      HARDENED_TRY(kmac_kmac_256(
          &kmac_key, /*masked_digest=*/kHardenedBoolTrue, context.data,
          context.len, label.data, label.len, output_key_material->keyblob,
          output_key_material->config.key_length / sizeof(uint32_t)));
      break;
    }
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  output_key_material->checksum =
      integrity_blinded_checksum(output_key_material);

  // Clear the KMAC sideload slot in case the key was sideloaded.
  return keymgr_sideload_clear_kmac();
}
