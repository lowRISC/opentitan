// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/ecc/p256.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/ecc_p256.h"
#include "sw/device/lib/crypto/include/entropy_src.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

enum {
  /* Number of 32-bit words in a P-256 public key. */
  kP256PublicKeyWords = 512 / 32,
  /* Number of bytes in a P-256 private key. */
  kP256PrivateKeyBytes = 256 / 8,
};

static const otcrypto_key_config_t kPrivateKeyConfig = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeEcdsaP256,
    .key_length = kP256PrivateKeyBytes,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

// We verify the correctness of the base point multiplication by generating
// a random key, then passing the private key to the base point multiplication
// app and verify that it recomputes the public key.
status_t base_point_mult_test(void) {
  // Allocate space for a private key.
  uint32_t keyblob[keyblob_num_words(kPrivateKeyConfig)];
  otcrypto_blinded_key_t private_key = {
      .config = kPrivateKeyConfig,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };

  // Allocate space for a public key.
  uint32_t pk[kP256PublicKeyWords] = {0};
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = sizeof(pk),
      .key = pk,
  };

  // Generate a keypair.
  LOG_INFO("Generating keypair...");
  CHECK_STATUS_OK(otcrypto_ecdsa_p256_keygen(&private_key, &public_key));

  // Allocate space for the recomputed public key.
  uint32_t pk_ver[kP256PublicKeyWords] = {0};
  otcrypto_unblinded_key_t public_key_ver = {
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = sizeof(pk_ver),
      .key = pk_ver,
  };

  LOG_INFO("Calculating base point multiplication...");
  CHECK_STATUS_OK(
      otcrypto_ecc_p256_base_point_mult(&private_key, &public_key_ver));

  // The intial generated public key and the public key from the base point
  // multipliation must match.
  TRY_CHECK_ARRAYS_EQ(pk, pk_ver, kP256PublicKeyWords);

  // Null inputs
  CHECK(otcrypto_ecc_p256_base_point_mult(NULL, &public_key_ver).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p256_base_point_mult(&private_key, NULL).value !=
        OTCRYPTO_OK.value);

  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

  status_t err = base_point_mult_test();
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
