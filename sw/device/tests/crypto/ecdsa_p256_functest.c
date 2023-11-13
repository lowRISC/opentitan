// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/ecc/ecdsa_p256.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/ecc.h"
#include "sw/device/lib/crypto/include/hash.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

enum {
  /* Number of 32-bit words in a SHA256 digest. */
  kSha256DigestWords = 256 / 32,
};

// Message
static const char kMessage[] = "test message";

static const ecc_curve_t kCurveP256 = {
    .curve_type = kEccCurveTypeNistP256,
    .domain_parameter = NULL,
};

static const crypto_key_config_t kPrivateKeyConfig = {
    .version = kCryptoLibVersion1,
    .key_mode = kKeyModeEcdsa,
    .key_length = 258 / 8,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kSecurityLevelLow,
};

status_t sign_then_verify_test(hardened_bool_t *verification_result) {
  // Allocate space for a masked private key.
  uint32_t keyblob[keyblob_num_words(kPrivateKeyConfig)];
  crypto_blinded_key_t private_key = {
      .config = kPrivateKeyConfig,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };

  // Allocate space for a public key.
  uint32_t pk_x[kP256CoordWords] = {0};
  uint32_t pk_y[kP256CoordWords] = {0};
  ecc_public_key_t public_key = {
      .x =
          {
              .key_mode = kKeyModeEcdsa,
              .key_length = sizeof(pk_x),
              .key = pk_x,
          },
      .y =
          {
              .key_mode = kKeyModeEcdsa,
              .key_length = sizeof(pk_y),
              .key = pk_y,
          },
  };
  public_key.x.checksum = integrity_unblinded_checksum(&public_key.x);
  public_key.y.checksum = integrity_unblinded_checksum(&public_key.y);

  // Generate a keypair.
  LOG_INFO("Generating keypair...");
  CHECK_STATUS_OK(
      otcrypto_ecdsa_keygen(&kCurveP256, &private_key, &public_key));

  // Hash the message.
  crypto_const_byte_buf_t msg = {
      .len = sizeof(kMessage) - 1,
      .data = (unsigned char *)&kMessage,
  };
  uint32_t msg_digest_data[kSha256DigestWords];
  hash_digest_t msg_digest = {
      .data = msg_digest_data,
      .len = ARRAYSIZE(msg_digest_data),
      .mode = kHashModeSha256,
  };
  TRY(otcrypto_hash(msg, &msg_digest));

  // Allocate space for the signature.
  uint32_t sigR[kP256ScalarWords] = {0};
  uint32_t sigS[kP256ScalarWords] = {0};
  ecc_signature_t signature = {
      .len_r = sizeof(sigR),
      .r = sigR,
      .len_s = sizeof(sigS),
      .s = sigS,
  };

  // Generate a signature for the message.
  LOG_INFO("Signing...");
  CHECK_STATUS_OK(
      otcrypto_ecdsa_sign(&private_key, &msg_digest, &kCurveP256, &signature));

  // Verify the signature.
  LOG_INFO("Verifying...");
  CHECK_STATUS_OK(otcrypto_ecdsa_verify(&public_key, &msg_digest, &signature,
                                        &kCurveP256, verification_result));

  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  CHECK_STATUS_OK(entropy_testutils_auto_mode_init());

  hardened_bool_t verificationResult;
  status_t err = sign_then_verify_test(&verificationResult);
  if (!status_ok(err)) {
    // If there was an error, print the OTBN error bits and instruction count.
    LOG_INFO("OTBN error bits: 0x%08x", otbn_err_bits_get());
    LOG_INFO("OTBN instruction count: 0x%08x", otbn_instruction_count_get());
    // Print the error.
    CHECK_STATUS_OK(err);
    return false;
  }

  // Signature verification is expected to succeed.
  if (verificationResult != kHardenedBoolTrue) {
    LOG_ERROR("Signature failed to pass verification!");
    return false;
  }

  return true;
}
