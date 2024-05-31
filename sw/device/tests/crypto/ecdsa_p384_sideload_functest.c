// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/ecc.h"
#include "sw/device/lib/crypto/include/hash.h"
#include "sw/device/lib/crypto/include/key_transport.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

enum {
  /* Number of 32-bit words in a SHA384 digest. */
  kSha384DigestWords = 384 / 32,
  /* Number of 32-bit words in a P-384 public key. */
  kP384PublicKeyWords = 768 / 32,
  /* Number of 32-bit words in a P-384 signature. */
  kP384SignatureWords = 768 / 32,
  /* Number of bytes in a P-384 private key. */
  kP384PrivateKeyBytes = 384 / 8,
};

// Message
static const char kMessage[] = "test message";

static const otcrypto_ecc_curve_t kCurveP384 = {
    .curve_type = kOtcryptoEccCurveTypeNistP384,
    .domain_parameter = NULL,
};

static const otcrypto_key_config_t kPrivateKeyConfig = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeEcdsa,
    .key_length = kP384PrivateKeyBytes,
    .hw_backed = kHardenedBoolTrue,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

static const uint32_t kPrivateKeySalt[7] = {0xdeadbeef, 0xdeadbeef, 0xdeadbeef,
                                            0xdeadbeef, 0xdeadbeef, 0xdeadbeef,
                                            0xdeadbeef};

static const uint32_t kPrivateKeyVersion = 0x0;

status_t sign_then_verify_test(void) {
  // Allocate space for a hardware-backed key.
  uint32_t keyblob[keyblob_num_words(kPrivateKeyConfig)];
  otcrypto_blinded_key_t private_key = {
      .config = kPrivateKeyConfig,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };

  // Construct the private key handle.
  TRY(otcrypto_hw_backed_key(kPrivateKeyVersion, kPrivateKeySalt,
                             &private_key));

  // Allocate space for a public key.
  uint32_t pk[kP384PublicKeyWords] = {0};
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdsa,
      .key_length = sizeof(pk),
      .key = pk,
  };

  // Generate a keypair.
  LOG_INFO("Generating keypair...");
  CHECK_STATUS_OK(
      otcrypto_ecdsa_keygen(&kCurveP384, &private_key, &public_key));

  // Hash the message.
  otcrypto_const_byte_buf_t msg = {
      .len = sizeof(kMessage) - 1,
      .data = (unsigned char *)&kMessage,
  };
  uint32_t msg_digest_data[kSha384DigestWords];
  otcrypto_hash_digest_t msg_digest = {
      .data = msg_digest_data,
      .len = ARRAYSIZE(msg_digest_data),
      .mode = kOtcryptoHashModeSha384,
  };
  TRY(otcrypto_hash(msg, msg_digest));

  // Allocate space for the signature.
  uint32_t sig[kP384SignatureWords] = {0};

  // Generate a signature for the message.
  LOG_INFO("Signing...");
  CHECK_STATUS_OK(otcrypto_ecdsa_sign(
      &private_key, msg_digest, &kCurveP384,
      (otcrypto_word32_buf_t){.data = sig, .len = ARRAYSIZE(sig)}));

  // Verify the signature.
  LOG_INFO("Verifying...");
  hardened_bool_t verification_result;
  CHECK_STATUS_OK(otcrypto_ecdsa_verify(
      &public_key, msg_digest,
      (otcrypto_const_word32_buf_t){.data = sig, .len = ARRAYSIZE(sig)},
      &kCurveP384, &verification_result));

  // The signature should pass verification.
  TRY_CHECK(verification_result == kHardenedBoolTrue);
  return OTCRYPTO_OK;
}

static status_t test_setup(void) {
  // Initialize the key manager and advance to OwnerRootKey state.  Note: the
  // keymgr testutils set this up using software entropy, so there is no need
  // to initialize the entropy complex first. However, this is of course not
  // the expected setup in production.
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

  // Initialize entropy complex for cryptolib, which the key manager uses to
  // clear sideloaded keys. The `keymgr_testutils_startup` function restarts
  // the device, so this should happen afterwards.
  return entropy_complex_init();
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t result = OK_STATUS();

  CHECK_STATUS_OK(test_setup());
  EXECUTE_TEST(result, sign_then_verify_test);

  return status_ok(result);

  return true;
}
