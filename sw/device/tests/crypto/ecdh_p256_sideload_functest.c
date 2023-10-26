// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/ecc.h"
#include "sw/device/lib/crypto/include/key_transport.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

enum {
  /* Number of 32-bit words in a P-256 public key. */
  kP256PublicKeyWords = 512 / 32,
  /* Number of 32-bit words in a P-256 signature. */
  kP256SignatureWords = 512 / 32,
  /* Number of bytes in a P-256 private key. */
  kP256PrivateKeyBytes = 256 / 8,
  /* Number of bytes in an ECDH/P-256 shared key. */
  kP256SharedKeyBytes = 256 / 8,
  /* Number of 32-bit words in an ECDH/P-256 shared key. */
  kP256SharedKeyWords = kP256SharedKeyBytes / sizeof(uint32_t),
};

static const ecc_curve_t kCurveP256 = {
    .curve_type = kEccCurveTypeNistP256,
    .domain_parameter = NULL,
};

// Versions for private keys A and B.
static const uint32_t kPrivateKeyAVersion = 0xa;
static const uint32_t kPrivateKeyBVersion = 0xb;

// Salt for private keys A and B.
static const uint32_t kPrivateKeyASalt[7] = {0xdeadbeef, 0xdeadbeef, 0xdeadbeef,
                                             0xdeadbeef, 0xdeadbeef, 0xdeadbeef,
                                             0xdeadbeef};
static const uint32_t kPrivateKeyBSalt[7] = {0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab,
                                             0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7,
                                             0xb8b9babb};

// Configuration for the private key.
static const crypto_key_config_t kEcdhPrivateKeyConfig = {
    .version = kCryptoLibVersion1,
    .key_mode = kKeyModeEcdh,
    .key_length = kP256PrivateKeyBytes,
    .hw_backed = kHardenedBoolTrue,
    .security_level = kSecurityLevelLow,
};

// Configuration for the ECDH shared (symmetric) key. This configuration
// specifies an AES key, but any symmetric mode that supports 256-bit keys is
// OK here.
static const crypto_key_config_t kEcdhSharedKeyConfig = {
    .version = kCryptoLibVersion1,
    .key_mode = kKeyModeAesCtr,
    .key_length = kP256SharedKeyBytes,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kSecurityLevelLow,
};

status_t key_exchange_test(void) {
  // Allocate space for two sideloaded private keys.
  uint32_t keyblobA[keyblob_num_words(kEcdhPrivateKeyConfig)];
  crypto_blinded_key_t private_keyA = {
      .config = kEcdhPrivateKeyConfig,
      .keyblob_length = sizeof(keyblobA),
      .keyblob = keyblobA,
  };
  TRY(otcrypto_hw_backed_key(kPrivateKeyAVersion, kPrivateKeyASalt,
                             &private_keyA));
  uint32_t keyblobB[keyblob_num_words(kEcdhPrivateKeyConfig)];
  crypto_blinded_key_t private_keyB = {
      .config = kEcdhPrivateKeyConfig,
      .keyblob_length = sizeof(keyblobB),
      .keyblob = keyblobB,
  };
  TRY(otcrypto_hw_backed_key(kPrivateKeyBVersion, kPrivateKeyBSalt,
                             &private_keyB));

  // Allocate space for two public keys.
  uint32_t pkA[kP256PublicKeyWords] = {0};
  uint32_t pkB[kP256PublicKeyWords] = {0};
  crypto_unblinded_key_t public_keyA = {
      .key_mode = kKeyModeEcdh,
      .key_length = sizeof(pkA),
      .key = pkA,
  };
  crypto_unblinded_key_t public_keyB = {
      .key_mode = kKeyModeEcdh,
      .key_length = sizeof(pkB),
      .key = pkB,
  };

  // Generate a keypair.
  LOG_INFO("Generating keypair A...");
  TRY(otcrypto_ecdh_keygen(&kCurveP256, &private_keyA, &public_keyA));

  // Generate a second keypair.
  LOG_INFO("Generating keypair B...");
  TRY(otcrypto_ecdh_keygen(&kCurveP256, &private_keyB, &public_keyB));

  // Sanity check; public keys should be different from each other.
  CHECK_ARRAYS_NE(pkA, pkB, ARRAYSIZE(pkA));

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
  uint32_t keyA[kP256SharedKeyWords];
  uint32_t keyB[kP256SharedKeyWords];
  for (size_t i = 0; i < ARRAYSIZE(keyA); i++) {
    keyA[i] = keyA0[i] ^ keyA1[i];
    keyB[i] = keyB0[i] ^ keyB1[i];
  }
  CHECK_ARRAYS_EQ(keyA, keyB, ARRAYSIZE(keyA));

  return OTCRYPTO_OK;
}

static status_t test_setup(void) {
  // Initialize the key manager and advance to OwnerRootKey state.  Note: the
  // keymgr testutils set this up using software entropy, so there is no need
  // to initialize the entropy complex first. However, this is of course not
  // the expected setup in production.
  dif_keymgr_t keymgr;
  dif_kmac_t kmac;
  TRY(keymgr_testutils_startup(&keymgr, &kmac));
  TRY(keymgr_testutils_advance_state(&keymgr, &kOwnerIntParams));
  TRY(keymgr_testutils_advance_state(&keymgr, &kOwnerRootKeyParams));
  TRY(keymgr_testutils_check_state(&keymgr, kDifKeymgrStateOwnerRootKey));

  // Initialize entropy complex for cryptolib, which the key manager uses to
  // clear sideloaded keys. The `keymgr_testutils_startup` function restarts
  // the device, so this should happen afterwards.
  return entropy_complex_init();
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t result = OK_STATUS();

  CHECK_STATUS_OK(test_setup());
  EXECUTE_TEST(result, key_exchange_test);

  return status_ok(result);
}
