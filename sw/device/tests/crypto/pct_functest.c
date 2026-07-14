// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/ecc_p256.h"
#include "sw/device/lib/crypto/include/ecc_p384.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

OTTF_DEFINE_TEST_CONFIG();

enum {
  /* Number of 32-bit words in a P-256 public key. */
  kP256PublicKeyWords = 512 / 32,
  /* Number of bytes in a P-256 private key. */
  kP256PrivateKeyBytes = 256 / 8,

  /* Number of 32-bit words in a P-384 public key. */
  kP384PublicKeyWords = 768 / 32,
  /* Number of bytes in a P-384 private key. */
  kP384PrivateKeyBytes = 384 / 8,
};

static const otcrypto_key_config_t kP256PrivateKeyConfig = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeEcdsaP256,
    .key_length = kP256PrivateKeyBytes,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

static const otcrypto_key_config_t kP384PrivateKeyConfig = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeEcdsaP384,
    .key_length = kP384PrivateKeyBytes,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

static status_t p256_pct_keygen_test(void) {
  LOG_INFO("Starting P-256 FIPS PCT Keygen test...");

  // Allocate space for a masked private key.
  uint32_t keyblob[keyblob_num_words(kP256PrivateKeyConfig)];
  otcrypto_blinded_key_t private_key = {
      .config = kP256PrivateKeyConfig,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  private_key.checksum = otcrypto_integrity_blinded_checksum(&private_key);

  // Allocate space for a public key.
  uint32_t pk[kP256PublicKeyWords] = {0};
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = sizeof(pk),
      .key = pk,
  };

  // Generate keypair with OTBN FIPS PCT active.
  CHECK_STATUS_OK(otcrypto_ecdsa_p256_keygen(&private_key, &public_key));

  LOG_INFO("P-256 FIPS PCT Keygen test passed.");
  return OK_STATUS();
}

static status_t p384_pct_keygen_test(void) {
  LOG_INFO("Starting P-384 FIPS PCT Keygen test...");

  // Allocate space for a masked private key.
  uint32_t keyblob[keyblob_num_words(kP384PrivateKeyConfig)];
  otcrypto_blinded_key_t private_key = {
      .config = kP384PrivateKeyConfig,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  private_key.checksum = otcrypto_integrity_blinded_checksum(&private_key);

  // Allocate space for a public key.
  uint32_t pk[kP384PublicKeyWords] = {0};
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdsaP384,
      .key_length = sizeof(pk),
      .key = pk,
  };

  // Generate keypair with OTBN FIPS PCT active.
  CHECK_STATUS_OK(otcrypto_ecdsa_p384_keygen(&private_key, &public_key));

  LOG_INFO("P-384 FIPS PCT Keygen test passed.");
  return OK_STATUS();
}

bool test_main(void) {
  status_t result = OK_STATUS();

  otcrypto_state_t state = {0};
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow, &state));

  EXECUTE_TEST(result, p256_pct_keygen_test);
  EXECUTE_TEST(result, p384_pct_keygen_test);

  return status_ok(result);
}
