// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/ecc/p384.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/ecc_p384.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

enum {
  /* Number of 32-bit words in a P-384 public key (x and y coordinates). */
  kP384PublicKeyWords = 2 * kP384CoordWords,
  /* Number of bytes in a P-384 private key. */
  kP384PrivateKeyBytes = 384 / 8,
  /* Number of 32-bit words in a P-384 message digest. */
  kP384DigestWords = 384 / 32,
  /* Number of 32-bit words in a P-384 ECDSA signature. */
  kP384SignatureWords = 768 / 32,
};

static const otcrypto_key_config_t kPrivateKeyConfig = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeEcdsaP384,
    .key_length = kP384PrivateKeyBytes,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

static const char kMessage[] = "test message for public key import";

/**
 * Generate a P-384 keypair, sign a message, re-import the public key
 * coordinates via otcrypto_ecc_p384_public_key_import, and verify the
 * signature with the re-imported key.
 */
static status_t import_then_verify_test(void) {
  // Allocate space for a masked private key.
  uint32_t keyblob[keyblob_num_words(kPrivateKeyConfig)];
  otcrypto_blinded_key_t private_key = {
      .config = kPrivateKeyConfig,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };

  // Allocate space for the generated public key.
  uint32_t pk_buf[kP384PublicKeyWords];
  otcrypto_unblinded_key_t generated_public_key = {
      .key_mode = kOtcryptoKeyModeEcdsaP384,
      .key_length = sizeof(pk_buf),
      .key = pk_buf,
  };

  // Generate a keypair.
  LOG_INFO("Generating keypair...");
  TRY(otcrypto_ecdsa_p384_keygen(&private_key, &generated_public_key));

  // Hash the message.
  otcrypto_const_byte_buf_t msg = {
      .data = (unsigned char *)kMessage,
      .len = sizeof(kMessage) - 1,
  };
  uint32_t msg_digest_data[kP384DigestWords];
  otcrypto_hash_digest_t msg_digest = {
      .data = msg_digest_data,
      .len = ARRAYSIZE(msg_digest_data),
  };
  TRY(otcrypto_sha2_384(msg, &msg_digest));

  // Sign the message with the private key.
  uint32_t sig[kP384SignatureWords] = {0};
  otcrypto_word32_buf_t sig_buf = {
      .data = sig,
      .len = ARRAYSIZE(sig),
  };
  LOG_INFO("Signing...");
  TRY(otcrypto_ecdsa_p384_sign(&private_key, msg_digest, sig_buf));

  // Extract x and y from the generated public key buffer.
  p384_point_t *pt = (p384_point_t *)pk_buf;
  otcrypto_const_word32_buf_t x = {
      .data = pt->x,
      .len = kP384CoordWords,
  };
  otcrypto_const_word32_buf_t y = {
      .data = pt->y,
      .len = kP384CoordWords,
  };

  // Import the public key from its coordinates into a fresh buffer.
  uint32_t imported_pk_buf[kP384PublicKeyWords];
  otcrypto_unblinded_key_t imported_public_key = {
      .key_mode = kOtcryptoKeyModeEcdsaP384,
      .key_length = sizeof(imported_pk_buf),
      .key = imported_pk_buf,
  };
  LOG_INFO("Importing public key from coordinates...");
  TRY(otcrypto_ecc_p384_public_key_import(x, y, &imported_public_key));

  // Confirm that the imported key data matches the original.
  TRY_CHECK_ARRAYS_EQ(imported_pk_buf, pk_buf, kP384PublicKeyWords);

  // Verify the signature using the imported key.
  LOG_INFO("Verifying signature with imported key...");
  otcrypto_const_word32_buf_t const_sig_buf = {
      .data = sig,
      .len = ARRAYSIZE(sig),
  };
  hardened_bool_t verification_result;
  TRY(otcrypto_ecdsa_p384_verify(&imported_public_key, msg_digest,
                                 const_sig_buf, &verification_result));
  TRY_CHECK(verification_result == kHardenedBoolTrue);

  return OK_STATUS();
}

/**
 * Test that the ECDH key mode is also accepted, and that coordinates are
 * stored as [x || y] in the key buffer.
 */
static status_t ecdh_key_mode_test(void) {
  // x and y coordinates of the P-384 generator point G, in little-endian
  // word order as used by the P-384 implementation.
  uint32_t x_data[kP384CoordWords] = {
      0x72760ab7, 0x3a545e38, 0xbf55296c, 0x5502f25d, 0x82542a38, 0x59f741e0,
      0x8ba79b98, 0x6e1d3b62, 0xf320ad74, 0x8eb1c71e, 0xbe8b0537, 0xaa87ca22,
  };
  uint32_t y_data[kP384CoordWords] = {
      0x90ea0e5f, 0x7a431d7c, 0x1d7e819d, 0x0a60b1ce, 0xb5f0b8c0, 0xe9da3113,
      0x289a147c, 0xf8f41dbd, 0x9292dc29, 0x5d9e98bf, 0x96262c6f, 0x3617de4a,
  };

  otcrypto_const_word32_buf_t x = {
      .data = x_data,
      .len = kP384CoordWords,
  };
  otcrypto_const_word32_buf_t y = {
      .data = y_data,
      .len = kP384CoordWords,
  };

  uint32_t pk_buf[kP384PublicKeyWords];
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdhP384,
      .key_length = sizeof(pk_buf),
      .key = pk_buf,
  };
  TRY(otcrypto_ecc_p384_public_key_import(x, y, &public_key));

  // Confirm the coordinates were stored as [x || y].
  TRY_CHECK_ARRAYS_EQ(pk_buf, x_data, kP384CoordWords);
  TRY_CHECK_ARRAYS_EQ(pk_buf + kP384CoordWords, y_data, kP384CoordWords);

  return OK_STATUS();
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  CHECK_STATUS_OK(entropy_testutils_auto_mode_init());

  CHECK_STATUS_OK(ecdh_key_mode_test());

  CHECK_STATUS_OK(import_then_verify_test());

  return true;
}
