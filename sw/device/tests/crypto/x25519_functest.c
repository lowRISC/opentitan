// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/ecc_curve25519.h"
#include "sw/device/lib/crypto/include/entropy_src.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

enum {
  /* Number of bytes needed to store the private key. */
  kX25519PrivateKeyBytes = 32,
  /* Number of words needed to store the private key. */
  kX25519PrivateKeyWords = kX25519PrivateKeyBytes / 4,
  /* Number of bytes needed to store the public key. */
  kX25519PublicKeyBytes = 32,
  /* Number of words needed to store the public key. */
  kX25519PublicKeyWords = kX25519PublicKeyBytes / 4,
  /* Number of bytes needed to store the shared secret. */
  kX25519SharedSecretBytes = 32,
  /* Number of words needed to store the shared secret. */
  kX25519SharedSecretWords = kX25519SharedSecretBytes / 4,
};

// Test vectors from RFC 7748, Section 6.1
// https://datatracker.ietf.org/doc/html/rfc7748#section-6.1

// Private key of Alice.
static const uint32_t kPrivateKeyAlice[] = {
    0x0a6d0777, 0x7da51873, 0x72c1163c, 0x4566b251,
    0x872f4cdf, 0x2a99c0eb, 0xa5fb77b1, 0x2a2cb91d,
};

// Public key of Alice.
static const uint32_t kPublicKeyAlice[] = {
    0x09f02085, 0x54a73089, 0xdc7d8b74, 0x5af73eb4,
    0x0d3abf0d, 0xf41a3826, 0x8ea9a4eb, 0x6a4e9baa,
};

// Private key of Bob.
static const uint32_t kPrivateKeyBob[] = {
    0x7e08ab5d, 0x4b8a4a62, 0x8b7fe179, 0xe60e8083,
    0x29b13b6f, 0xfdb61826, 0x278b2f1c, 0xebe088ff,
};

// Public key of Bob.
static const uint32_t kPublicKeyBob[] = {
    0x7ddb9ede, 0xb4c17d7b, 0xc2615bd3, 0x3735e4ec,
    0xc843833f, 0x4d67785b, 0x147efcad, 0x4f2b886f,
};

// The shared secret.
static const uint32_t kSharedSecret[] = {
    0x5b9d5d4a, 0xe12dcea4, 0xf43b8e72, 0x250f3580,
    0xc9217ee0, 0x339ed147, 0x3c9bf076, 0x4217161e,
};

static const otcrypto_key_config_t kPrivateKeyConfig = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeX25519,
    .key_length = kX25519PrivateKeyBytes,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

/**
 * Helper function to securely populate the keyblob array with two shares.
 */
static status_t create_blinded_kat_keyblob(uint32_t *keyblob,
                                           const uint32_t *key) {
  // Zero out the entire blob to avoid checksumming uninitialized padding
  memset(keyblob, 0, keyblob_num_words(kPrivateKeyConfig) * sizeof(uint32_t));

  uint32_t *share0 = keyblob;
  uint32_t *share1 = keyblob + keyblob_share_num_words(kPrivateKeyConfig);

  // Generate a random mask for share0 (only need 8 words for the seed)
  HARDENED_TRY(hardened_memshred(share0, kX25519PrivateKeyWords));

  // Calculate share1 = key - share0 (implicitly modulo 2^256)
  HARDENED_TRY(hardened_sub(key, share0, kX25519PrivateKeyWords, share1));

  return OTCRYPTO_OK;
}

status_t x25519_kat_test(void) {
  LOG_INFO("Running X25519 KAT Test");

  uint32_t keyblob_alice[keyblob_num_words(kPrivateKeyConfig)];
  CHECK_STATUS_OK(create_blinded_kat_keyblob(keyblob_alice, kPrivateKeyAlice));

  otcrypto_blinded_key_t private_key_alice = {
      .config = kPrivateKeyConfig,
      .keyblob_length = sizeof(keyblob_alice),
      .keyblob = keyblob_alice,
  };
  private_key_alice.checksum = integrity_blinded_checksum(&private_key_alice);

  // Set up public_key struct for bob.
  uint32_t public_key_buf_bob[kX25519PublicKeyWords];
  memcpy(public_key_buf_bob, kPublicKeyBob, sizeof(public_key_buf_bob));
  otcrypto_unblinded_key_t public_key_bob = {
      .key_mode = kOtcryptoKeyModeX25519,
      .key_length = kX25519PublicKeyBytes,
      .key = public_key_buf_bob,
  };
  public_key_bob.checksum = integrity_unblinded_checksum(&public_key_bob);

  // Set up shared secret struct.
  uint32_t shared_secret_keyblob[keyblob_num_words(kPrivateKeyConfig)];
  otcrypto_blinded_key_t shared_secret = {
      .config = kPrivateKeyConfig,
      .keyblob_length = sizeof(shared_secret_keyblob),
      .keyblob = shared_secret_keyblob,
  };

  // Run X25519.
  CHECK_STATUS_OK(
      otcrypto_x25519(&private_key_alice, &public_key_bob, &shared_secret));

  // Unmask the shared secret.
  uint32_t shared_secret_unmasked[kX25519SharedSecretWords];
  uint32_t *share0 = shared_secret.keyblob;
  uint32_t *share1 =
      shared_secret.keyblob + keyblob_share_num_words(kPrivateKeyConfig);
  HARDENED_TRY(hardened_add(share0, share1, kX25519SharedSecretWords,
                            shared_secret_unmasked));

  // Check the x25519 result.
  TRY_CHECK_ARRAYS_EQ(kSharedSecret, shared_secret_unmasked,
                      kX25519SharedSecretWords);

  return OTCRYPTO_OK;
}

status_t x25519_keygen_test(void) {
  LOG_INFO("Running X25519 keygen Test");

  uint32_t keyblob_alice[keyblob_num_words(kPrivateKeyConfig)];
  CHECK_STATUS_OK(create_blinded_kat_keyblob(keyblob_alice, kPrivateKeyAlice));

  otcrypto_blinded_key_t private_key_alice = {
      .config = kPrivateKeyConfig,
      .keyblob_length = sizeof(keyblob_alice),
      .keyblob = keyblob_alice,
  };
  private_key_alice.checksum = integrity_blinded_checksum(&private_key_alice);

  // Set up public_key struct for alice.
  uint32_t public_key_buf_alice[kX25519PublicKeyWords];
  otcrypto_unblinded_key_t public_key_alice = {
      .key_mode = kOtcryptoKeyModeX25519,
      .key_length = kX25519PublicKeyBytes,
      .key = public_key_buf_alice,
  };
  public_key_alice.checksum = integrity_unblinded_checksum(&public_key_alice);

  // Run x25519 key generation.
  CHECK_STATUS_OK(
      otcrypto_x25519_keygen(&private_key_alice, &public_key_alice));

  // Check the x25519 key generation result.
  TRY_CHECK_ARRAYS_EQ(kPublicKeyAlice, public_key_alice.key,
                      kX25519PublicKeyWords);

  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t result = OK_STATUS();

  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

  EXECUTE_TEST(result, x25519_kat_test);
  EXECUTE_TEST(result, x25519_keygen_test);

  return status_ok(result);
}
