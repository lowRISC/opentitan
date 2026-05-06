// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/ecc_curve25519.h"
#include "sw/device/lib/crypto/include/entropy_src.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/key_transport.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('x', 's', 't')

enum {
  /**
   * Number of words needed to encode a mode of operation.
   */
  kCurve25519ModeWords = 1,
  /**
   * Number of words needed to encode the verification result.
   */
  kCurve25519ResultWords = 1,
  /**
   * Number of words needed to hold an encoded point for Curve25519.
   */
  kCurve25519PointWords = 8,
  /**
   * Number of bytes needed to hold an encoded point for Curve25519.
   */
  kCurve25519PointBytes = kCurve25519PointWords * 4,
  /**
   * Number of bytes needed to hold a encoded public or private key.
   */
  kCurve25519KeyBytes = 32,
  /**
   * Number of bytes needed to hold a scalar.
   */
  kCurve25519ScalarBytes = 32,
  /**
   * Number of words needed to hold a scalar.
   */
  kCurve25519ScalarWords = kCurve25519ScalarBytes / 4,
  /**
   * Length of a Curve25519 curve point coordinate in bits.
   */
  kCurve25519CoordBits = 256,
  /**
   * Length of a Curve25519 curve point coordinate in bytes.
   */
  kCurve25519CoordBytes = kCurve25519CoordBits / 8,
  /**
   * Length of a Curve25519 curve point coordinate in words.
   */
  kCurve25519CoordWords = kCurve25519CoordBytes / sizeof(uint32_t),
  /**
   * Length of an element in the Curve25519 scalar field in bits.
   */
  kCurve25519ScalarBits = 256,
  /**
   * Number of bytes in an ECDH/X25519 shared key (32 bytes).
   */
  kX25519SharedKeyBytes = 256 / 8,
  /**
   * Number of 32-bit words in an ECDH/X25519 shared key (8 words).
   */
  kX25519SharedKeyWords = kX25519SharedKeyBytes / sizeof(uint32_t),
};

// Versions for private keys A and B.
static const uint32_t kPrivateKeyAVersion = 0;
static const uint32_t kPrivateKeyBVersion = 0;

// Salt for private keys A and B.
static const uint32_t kPrivateKeyASalt[7] = {0xdeadbeef, 0xdeadbeef, 0xdeadbeef,
                                             0xdeadbeef, 0xdeadbeef, 0xdeadbeef,
                                             0xdeadbeef};
static const uint32_t kPrivateKeyBSalt[7] = {0xa0a1a2a3, 0xa4a5a6a7, 0xa8a9aaab,
                                             0xacadaeaf, 0xb0b1b2b3, 0xb4b5b6b7,
                                             0xb8b9babb};

// Configuration for the private key.
static const otcrypto_key_config_t kX25519PrivateKeyConfig = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeX25519,
    .key_length = kCurve25519KeyBytes,
    .hw_backed = kHardenedBoolTrue,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

// Configuration for the X25519 shared (symmetric) key.
static const otcrypto_key_config_t kX25519SharedKeyConfig = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeAesCtr,
    .key_length = kCurve25519KeyBytes,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

status_t key_exchange_test(void) {
  uint32_t keyblobA[keyblob_num_words(kX25519PrivateKeyConfig)];
  otcrypto_blinded_key_t private_keyA = {
      .config = kX25519PrivateKeyConfig,
      .keyblob_length = sizeof(keyblobA),
      .keyblob = keyblobA,
  };
  TRY(otcrypto_hw_backed_key(kPrivateKeyAVersion, kPrivateKeyASalt,
                             &private_keyA));

  uint32_t keyblobB[keyblob_num_words(kX25519PrivateKeyConfig)];
  otcrypto_blinded_key_t private_keyB = {
      .config = kX25519PrivateKeyConfig,
      .keyblob_length = sizeof(keyblobB),
      .keyblob = keyblobB,
  };
  TRY(otcrypto_hw_backed_key(kPrivateKeyBVersion, kPrivateKeyBSalt,
                             &private_keyB));

  uint32_t pkA[kCurve25519PointWords] = {0};
  uint32_t pkB[kCurve25519PointWords] = {0};
  otcrypto_unblinded_key_t public_keyA = {
      .key_mode = kOtcryptoKeyModeX25519,
      .key_length = sizeof(pkA),
      .key = pkA,
  };
  otcrypto_unblinded_key_t public_keyB = {
      .key_mode = kOtcryptoKeyModeX25519,
      .key_length = sizeof(pkB),
      .key = pkB,
  };

  // Generate a keypair.
  LOG_INFO("Generating X25519 keypair A");
  TRY(otcrypto_x25519_keygen(&private_keyA, &public_keyA));

  // Generate a second keypair.
  LOG_INFO("Generating X25519 keypair B");
  TRY(otcrypto_x25519_keygen(&private_keyB, &public_keyB));

  // Public keys should be different from each other.
  CHECK_ARRAYS_NE(pkA, pkB, ARRAYSIZE(pkA));

  uint32_t shared_keyblobA[keyblob_num_words(kX25519SharedKeyConfig)];
  otcrypto_blinded_key_t shared_keyA = {
      .config = kX25519SharedKeyConfig,
      .keyblob_length = sizeof(shared_keyblobA),
      .keyblob = shared_keyblobA,
      .checksum = 0,
  };
  uint32_t shared_keyblobB[keyblob_num_words(kX25519SharedKeyConfig)];
  otcrypto_blinded_key_t shared_keyB = {
      .config = kX25519SharedKeyConfig,
      .keyblob_length = sizeof(shared_keyblobB),
      .keyblob = shared_keyblobB,
      .checksum = 0,
  };

  // Compute the shared secret from A's side.
  LOG_INFO("Generating shared secret (A)");
  TRY(otcrypto_x25519(&private_keyA, &public_keyB, &shared_keyA));

  // Compute the shared secret from B's side.
  LOG_INFO("Generating shared secret (B)");
  TRY(otcrypto_x25519(&private_keyB, &public_keyA, &shared_keyB));

  // Unmask the keys and check that they match.
  uint32_t *keyA0;
  uint32_t *keyA1;
  TRY(keyblob_to_shares(&shared_keyA, &keyA0, &keyA1));
  uint32_t *keyB0;
  uint32_t *keyB1;
  TRY(keyblob_to_shares(&shared_keyB, &keyB0, &keyB1));

  uint32_t keyA[kX25519SharedKeyWords];
  uint32_t keyB[kX25519SharedKeyWords];

  TRY(hardened_add(keyA0, keyA1, kX25519SharedKeyWords, keyA));
  TRY(hardened_add(keyB0, keyB1, kX25519SharedKeyWords, keyB));

  CHECK_ARRAYS_EQ(keyA, keyB, ARRAYSIZE(keyA));

  return OTCRYPTO_OK;
}

static status_t test_setup(void) {
  // Initialize the key manager and advance to OwnerRootKey state.
  dif_keymgr_t keymgr;
  dif_kmac_t kmac;
  dif_keymgr_state_t keymgr_state;
  TRY(keymgr_testutils_try_startup(&keymgr, &kmac, &keymgr_state));

  if (keymgr_state == kDifKeymgrStateCreatorRootKey) {
    TRY(keymgr_testutils_advance_state(&keymgr, &kOwnerIntParams));
    TRY(keymgr_testutils_advance_state(&keymgr, &kOwnerRootKeyParams));
  } else if (keymgr_state == kDifKeymgrStateOwnerIntermediateKey) {
    TRY(keymgr_testutils_advance_state(&keymgr, &kOwnerRootKeyParams));
  }

  TRY(keymgr_testutils_check_state(&keymgr, kDifKeymgrStateOwnerRootKey));

  // Initialize entropy complex for cryptolib.
  return otcrypto_init(kOtcryptoKeySecurityLevelLow);
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t result = OK_STATUS();

  CHECK_STATUS_OK(test_setup());
  EXECUTE_TEST(result, key_exchange_test);

  return status_ok(result);
}
