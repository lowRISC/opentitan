// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/kmac_kdf.h"

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/crypto/drivers/kmac.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/integrity.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('k', 'k', 'd')

/**
 * Internal helper for KMAC-based KDF operations.
 *
 * @param key_derivation_key Key to use for derivation.
 * @param label Customization string (label).
 * @param context Context or measurement string.
 * @param is_cdi Whether this is a CDI derivation (uses attestation branch).
 * @param output_key_material Destination for the derived key.
 * @return Status of the operation.
 */
static otcrypto_status_t kmac_kdf_common(
    otcrypto_blinded_key_t *key_derivation_key,
    const otcrypto_const_byte_buf_t *label,
    const otcrypto_const_byte_buf_t *context, hardened_bool_t is_cdi,
    otcrypto_blinded_key_t *output_key_material) {
  if (key_derivation_key->keyblob == NULL || output_key_material == NULL ||
      output_key_material->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if ((label->data == NULL && label->len != 0) ||
      (label->len > kKmacCustStrMaxSize)) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check for null context with nonzero length.
  if (context->data == NULL && context->len != 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (launder32(integrity_blinded_key_check(key_derivation_key)) !=
      kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(integrity_blinded_key_check(key_derivation_key),
                    kHardenedBoolTrue);
  HARDENED_TRY(kmac_key_length_check(key_derivation_key->config.key_length));

  kmac_blinded_key_t kmac_key = {
      .share0 = NULL,
      .share1 = NULL,
      .hw_backed = key_derivation_key->config.hw_backed,
      .len = key_derivation_key->config.key_length,
  };

  if (launder32(key_derivation_key->config.hw_backed) == kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(key_derivation_key->config.hw_backed, kHardenedBoolTrue);
    if (keyblob_share_num_words(key_derivation_key->config) *
            sizeof(uint32_t) !=
        kKmacSideloadKeyLength / 8) {
      return OTCRYPTO_BAD_ARGS;
    }

    keymgr_diversification_t diversification;
    if (launder32(is_cdi) == kHardenedBoolTrue) {
      HARDENED_CHECK_EQ(is_cdi, kHardenedBoolTrue);
      HARDENED_TRY(keyblob_to_keymgr_attestation_diversification(
          key_derivation_key, &diversification));
      HARDENED_TRY(
          keymgr_generate_key_kmac(diversification, kHardenedBoolTrue));
    } else {
      HARDENED_TRY(keyblob_to_keymgr_diversification(key_derivation_key,
                                                     &diversification));
      HARDENED_TRY(
          keymgr_generate_key_kmac(diversification, kHardenedBoolFalse));
    }
  } else {
    // CDI derivations must be hardware-backed.
    if (launder32(is_cdi) == kHardenedBoolTrue) {
      return OTCRYPTO_BAD_ARGS;
    }
    HARDENED_TRY(keyblob_remask(key_derivation_key));
    if (key_derivation_key->keyblob_length !=
        keyblob_num_words(key_derivation_key->config) * sizeof(uint32_t)) {
      return OTCRYPTO_BAD_ARGS;
    }
    HARDENED_TRY(keyblob_to_shares(key_derivation_key, &kmac_key.share0,
                                   &kmac_key.share1));
  }

  // At the moment, `kmac_kmac_128/256` only supports word-sized digest lengths.
  if (output_key_material->config.key_length % sizeof(uint32_t) != 0) {
    return OTCRYPTO_NOT_IMPLEMENTED;
  }
  if (output_key_material->config.hw_backed != kHardenedBoolFalse ||
      output_key_material->keyblob_length !=
          keyblob_num_words(output_key_material->config) * sizeof(uint32_t)) {
    return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_TRY(
      hardened_memshred(output_key_material->keyblob,
                        keyblob_num_words(output_key_material->config)));

  otcrypto_key_mode_t key_mode_used = launder32(0);
  switch (launder32(key_derivation_key->config.key_mode)) {
    case kOtcryptoKeyModeKdfKmac128:
      key_mode_used = launder32(key_mode_used) | kOtcryptoKeyModeKdfKmac128;
      HARDENED_TRY(kmac_kmac_128(
          &kmac_key, kHardenedBoolTrue, context, label->data, label->len,
          output_key_material->keyblob,
          output_key_material->config.key_length / sizeof(uint32_t)));
      break;
    case kOtcryptoKeyModeKdfKmac256:
      key_mode_used = launder32(key_mode_used) | kOtcryptoKeyModeKdfKmac256;
      // Check that key size matches the security strength. It should be at
      // least 256-bit.
      if (key_derivation_key->config.key_length < 256 / 8) {
        return OTCRYPTO_BAD_ARGS;
      }
      HARDENED_TRY(kmac_kmac_256(
          &kmac_key, kHardenedBoolTrue, context, label->data, label->len,
          output_key_material->keyblob,
          output_key_material->config.key_length / sizeof(uint32_t)));
      break;
    default:
      return OTCRYPTO_BAD_ARGS;
  }
  HARDENED_CHECK_EQ(launder32(key_mode_used),
                    key_derivation_key->config.key_mode);

  output_key_material->checksum =
      integrity_blinded_checksum(output_key_material);
  return otcrypto_eval_exit(keymgr_sideload_clear_kmac());
}

otcrypto_status_t otcrypto_kmac_kdf(
    otcrypto_blinded_key_t *key_derivation_key,
    const otcrypto_const_byte_buf_t *label,
    const otcrypto_const_byte_buf_t *context,
    otcrypto_blinded_key_t *output_key_material) {
  return kmac_kdf_common(key_derivation_key, label, context, kHardenedBoolFalse,
                         output_key_material);
}

otcrypto_status_t otcrypto_cdi_kmac_kdf(
    otcrypto_blinded_key_t *key_derivation_key,
    const otcrypto_const_byte_buf_t *cdi_label,
    const otcrypto_const_byte_buf_t *dice_measurement,
    otcrypto_blinded_key_t *output_key_material) {
  return kmac_kdf_common(key_derivation_key, cdi_label, dice_measurement,
                         kHardenedBoolTrue, output_key_material);
}
