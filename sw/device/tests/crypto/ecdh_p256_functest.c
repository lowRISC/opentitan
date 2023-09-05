// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/ecc/p256_common.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/ecc.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

static const ecc_curve_t kCurveP256 = {
    .curve_type = kEccCurveTypeNistP256,
    .domain_parameter =
        (ecc_domain_t){
            .p = (crypto_const_byte_buf_t){.data = NULL, .len = 0},
            .a = (crypto_const_byte_buf_t){.data = NULL, .len = 0},
            .b = (crypto_const_byte_buf_t){.data = NULL, .len = 0},
            .q = (crypto_const_byte_buf_t){.data = NULL, .len = 0},
            .gx = NULL,
            .gy = NULL,
            .cofactor = 0u,
            .checksum = 0u,
        },
};

// Configuration for the private key.
static const crypto_key_config_t kEcdhPrivateKeyConfig = {
    .version = kCryptoLibVersion1,
    .key_mode = kKeyModeEcdh,
    .key_length = kP256ScalarBytes,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kSecurityLevelLow,
};

// Configuration for the ECDH shared (symmetric) key. This configuration
// specifies an AES key, but any symmetric mode that supports 256-bit keys is
// OK here.
static const crypto_key_config_t kEcdhSharedKeyConfig = {
    .version = kCryptoLibVersion1,
    .key_mode = kKeyModeAesCtr,
    .key_length = kP256CoordBytes,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kSecurityLevelLow,
};

status_t key_exchange_test(void) {
  // Allocate space for two private keys.
  uint32_t keyblobA[keyblob_num_words(kEcdhPrivateKeyConfig)];
  crypto_blinded_key_t private_keyA = {
      .config = kEcdhPrivateKeyConfig,
      .keyblob_length = sizeof(keyblobA),
      .keyblob = keyblobA,
      .checksum = 0,
  };
  uint32_t keyblobB[keyblob_num_words(kEcdhPrivateKeyConfig)];
  crypto_blinded_key_t private_keyB = {
      .config = kEcdhPrivateKeyConfig,
      .keyblob_length = sizeof(keyblobB),
      .keyblob = keyblobB,
      .checksum = 0,
  };

  // Allocate space for two public keys.
  uint32_t xA[kP256CoordWords];
  uint32_t yA[kP256CoordWords];
  ecc_public_key_t public_keyA = {
      .x =
          {
              .key_mode = kKeyModeEcdh,
              .key_length = sizeof(xA),
              .key = xA,
          },
      .y =
          {
              .key_mode = kKeyModeEcdh,
              .key_length = sizeof(yA),
              .key = yA,
          },
  };
  uint32_t xB[kP256CoordWords];
  uint32_t yB[kP256CoordWords];
  ecc_public_key_t public_keyB = {
      .x =
          {
              .key_mode = kKeyModeEcdh,
              .key_length = sizeof(xB),
              .key = xB,
          },
      .y =
          {
              .key_mode = kKeyModeEcdh,
              .key_length = sizeof(yB),
              .key = yB,
          },
  };

  // Generate a keypair.
  LOG_INFO("Generating keypair A...");
  TRY(otcrypto_ecdh_keygen(&kCurveP256, &private_keyA, &public_keyA));

  // Generate a second keypair.
  LOG_INFO("Generating keypair B...");
  TRY(otcrypto_ecdh_keygen(&kCurveP256, &private_keyB, &public_keyB));

  // Sanity check; public keys should be different from each other.
  CHECK_ARRAYS_NE(xA, xB, ARRAYSIZE(xA));
  CHECK_ARRAYS_NE(yA, yB, ARRAYSIZE(yA));

  // Allocate space for two shared keys.
  uint32_t shared_keyblobA[keyblob_num_words(kEcdhSharedKeyConfig)];
  crypto_blinded_key_t shared_keyA = {
      .config = kEcdhSharedKeyConfig,
      .keyblob_length = sizeof(shared_keyblobA),
      .keyblob = shared_keyblobA,
      .checksum = 0,
  };
  uint32_t shared_keyblobB[keyblob_num_words(kEcdhSharedKeyConfig)];
  crypto_blinded_key_t shared_keyB = {
      .config = kEcdhSharedKeyConfig,
      .keyblob_length = sizeof(shared_keyblobB),
      .keyblob = shared_keyblobB,
      .checksum = 0,
  };

  // Compute the shared secret from A's side of the computation (using A's
  // private key and B's public key).
  LOG_INFO("Generating shared secret (A)...");
  TRY(otcrypto_ecdh(&private_keyA, &public_keyB, &kCurveP256, &shared_keyA));

  // Compute the shared secret from B's side of the computation (using B's
  // private key and A's public key).
  LOG_INFO("Generating shared secret (B)...");
  TRY(otcrypto_ecdh(&private_keyB, &public_keyA, &kCurveP256, &shared_keyB));

  // Get pointers to individual shares of both shared keys.
  uint32_t *keyA0;
  uint32_t *keyA1;
  TRY(keyblob_to_shares(&shared_keyA, &keyA0, &keyA1));
  uint32_t *keyB0;
  uint32_t *keyB1;
  TRY(keyblob_to_shares(&shared_keyB, &keyB0, &keyB1));

  // Unmask the keys and check that they match.
  uint32_t keyA[kP256CoordWords];
  uint32_t keyB[kP256CoordWords];
  for (size_t i = 0; i < ARRAYSIZE(keyA); i++) {
    keyA[i] = keyA0[i] ^ keyA1[i];
    keyB[i] = keyB0[i] ^ keyB1[i];
  }
  CHECK_ARRAYS_EQ(keyA, keyB, ARRAYSIZE(keyA));

  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  CHECK_STATUS_OK(entropy_testutils_auto_mode_init());

  status_t err = key_exchange_test();
  if (!status_ok(err)) {
    // If there was an error, print the OTBN error bits and instruction count.
    LOG_INFO("OTBN error bits: 0x%08x", otbn_err_bits_get());
    LOG_INFO("OTBN instruction count: 0x%08x", otbn_instruction_count_get());
    // Print the error.
    CHECK_STATUS_OK(err);
    return false;
  }

  return true;
}
