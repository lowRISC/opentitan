// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/ecc.h"
#include "sw/device/lib/crypto/include/key_transport.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

enum {
  /* Number of 32-bit words in a P-256 coordinate (256 bits). */
  kP256CoordWords = 256 / 32,
  /* Number of 32-bit words in a P-256 scalar (256 bits). */
  kP256ScalarWords = 256 / 32,
};

// Message
static const char kMessage[] = "test message";

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

static const crypto_key_config_t kPrivateKeyConfig = {
    .version = kCryptoLibVersion1,
    .key_mode = kKeyModeEcdsa,
    .key_length = 258 / 8,
    .hw_backed = kHardenedBoolTrue,
    .security_level = kSecurityLevelLow,
};

static const uint32_t kPrivateKeySalt[7] = {0xdeadbeef, 0xdeadbeef, 0xdeadbeef,
                                            0xdeadbeef, 0xdeadbeef, 0xdeadbeef,
                                            0xdeadbeef};

static const uint32_t kPrivateKeyVersion = 0x9;

status_t sign_then_verify_test(void) {
  // Allocate space for a hardware-backed key.
  uint32_t keyblob[8] = {0};
  crypto_blinded_key_t private_key = {
      .config = kPrivateKeyConfig,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };

  // Construct the private key handle.
  TRY(otcrypto_hw_backed_key(kPrivateKeyVersion, kPrivateKeySalt,
                             &private_key));

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

  // Generate a keypair.
  LOG_INFO("Generating keypair...");
  TRY(otcrypto_ecdsa_keygen(&kCurveP256, &private_key, &public_key));

  // Package message in a cryptolib-style struct.
  crypto_const_byte_buf_t message = {
      .len = sizeof(kMessage) - 1,
      .data = (unsigned char *)&kMessage,
  };

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
  TRY(otcrypto_ecdsa_sign(&private_key, message, &kCurveP256, &signature));

  // Verify the signature.
  LOG_INFO("Verifying...");
  hardened_bool_t verification_result;
  TRY(otcrypto_ecdsa_verify(&public_key, message, &signature, &kCurveP256,
                            &verification_result));

  // The signature should pass verification.
  TRY_CHECK(verification_result == kHardenedBoolTrue);
  return OK_STATUS();
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
  EXECUTE_TEST(result, sign_then_verify_test);

  return status_ok(result);
}
