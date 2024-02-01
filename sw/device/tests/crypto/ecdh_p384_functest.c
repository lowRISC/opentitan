// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/ecc.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

enum {
  /* Number of 32-bit words in a P-384 public key. */
  kP384PublicKeyWords = 768 / 32,
  /* Number of 32-bit words in a P-384 signature. */
  kP384SignatureWords = 768 / 32,
  /* Number of bytes in a P-384 private key. */
  kP384PrivateKeyBytes = 384 / 8,
  /* Number of bytes in an ECDH/P-384 shared key. */
  kP384SharedKeyBytes = 384 / 8,
  /* Number of 32-bit words in an ECDH/P-384 shared key. */
  kP384SharedKeyWords = kP384SharedKeyBytes / sizeof(uint32_t),
};

static const otcrypto_ecc_curve_t kCurveP384 = {
    .curve_type = kOtcryptoEccCurveTypeNistP384,
    .domain_parameter = NULL,
};

// Configuration for the private key.
static const otcrypto_key_config_t kEcdhPrivateKeyConfig = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeEcdh,
    .key_length = kP384PrivateKeyBytes,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

// Configuration for the ECDH shared (symmetric) key. This configuration
// specifies an AES key, but any symmetric mode that supports 384-bit keys is
// OK here.
static const otcrypto_key_config_t kEcdhSharedKeyConfig = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeAesCtr,
    .key_length = kP384SharedKeyBytes,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

status_t key_exchange_test(void) {
  // Allocate space for two private keys.
  uint32_t keyblobA[keyblob_num_words(kEcdhPrivateKeyConfig)];
  otcrypto_blinded_key_t private_keyA = {
      .config = kEcdhPrivateKeyConfig,
      .keyblob_length = sizeof(keyblobA),
      .keyblob = keyblobA,
      .checksum = 0,
  };
  uint32_t keyblobB[keyblob_num_words(kEcdhPrivateKeyConfig)];
  otcrypto_blinded_key_t private_keyB = {
      .config = kEcdhPrivateKeyConfig,
      .keyblob_length = sizeof(keyblobB),
      .keyblob = keyblobB,
      .checksum = 0,
  };

  // Allocate space for two public keys.
  uint32_t pkA[kP384PublicKeyWords] = {0};
  uint32_t pkB[kP384PublicKeyWords] = {0};
  otcrypto_unblinded_key_t public_keyA = {
      .key_mode = kOtcryptoKeyModeEcdh,
      .key_length = sizeof(pkA),
      .key = pkA,
  };
  otcrypto_unblinded_key_t public_keyB = {
      .key_mode = kOtcryptoKeyModeEcdh,
      .key_length = sizeof(pkB),
      .key = pkB,
  };

  // Generate a keypair.
  LOG_INFO("Generating keypair A...");
  TRY(otcrypto_ecdh_keygen(&kCurveP384, &private_keyA, &public_keyA));

  // Generate a second keypair.
  LOG_INFO("Generating keypair B...");
  TRY(otcrypto_ecdh_keygen(&kCurveP384, &private_keyB, &public_keyB));

  // Sanity check; public keys should be different from each other.
  CHECK_ARRAYS_NE(pkA, pkB, ARRAYSIZE(pkA));
  // Sanity check; private keys should be different from each other.
  CHECK_ARRAYS_NE(keyblobA, keyblobB, ARRAYSIZE(keyblobA));

  // Allocate space for two shared keys.
  uint32_t shared_keyblobA[keyblob_num_words(kEcdhSharedKeyConfig)];
  otcrypto_blinded_key_t shared_keyA = {
      .config = kEcdhSharedKeyConfig,
      .keyblob_length = sizeof(shared_keyblobA),
      .keyblob = shared_keyblobA,
      .checksum = 0,
  };
  uint32_t shared_keyblobB[keyblob_num_words(kEcdhSharedKeyConfig)];
  otcrypto_blinded_key_t shared_keyB = {
      .config = kEcdhSharedKeyConfig,
      .keyblob_length = sizeof(shared_keyblobB),
      .keyblob = shared_keyblobB,
      .checksum = 0,
  };

  // Compute the shared secret from A's side of the computation (using A's
  // private key and B's public key).
  LOG_INFO("Generating shared secret (A)...");
  TRY(otcrypto_ecdh(&private_keyA, &public_keyB, &kCurveP384, &shared_keyA));

  // Compute the shared secret from B's side of the computation (using B's
  // private key and A's public key).
  LOG_INFO("Generating shared secret (B)...");
  TRY(otcrypto_ecdh(&private_keyB, &public_keyA, &kCurveP384, &shared_keyB));

  // Get pointers to individual shares of both shared keys.
  uint32_t *keyA0;
  uint32_t *keyA1;
  TRY(keyblob_to_shares(&shared_keyA, &keyA0, &keyA1));
  uint32_t *keyB0;
  uint32_t *keyB1;
  TRY(keyblob_to_shares(&shared_keyB, &keyB0, &keyB1));

  // Unmask the keys and check that they match.
  uint32_t keyA[kP384SharedKeyWords];
  uint32_t keyB[kP384SharedKeyWords];
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
