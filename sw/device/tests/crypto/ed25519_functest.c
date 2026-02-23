// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/ecc_curve25519.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

enum {
  /* Number of bytes needed to store the private key. */
  kEd25519PrivateKeyBytes = 32,
  /* Number of words needed to store the private key. */
  kEd25519PrivateKeyWords = kEd25519PrivateKeyBytes / 4,
  /* Number of bytes needed to store the private key. */
  kEd25519SignatureBytes = 64,
  /* Number of words needed to store the private key. */
  kEd25519SignatureWords = kEd25519SignatureBytes / 4,
  /* Number of bytes needed to store the public key. */
  kEd25519PublicKeyBytes = 32,
  /* Number of words needed to store the public key. */
  kEd25519PublicKeyWords = kEd25519PublicKeyBytes / 4,
};

// This test vector stems from RFC 8032 section 7.1 TEST 2:
// https://datatracker.ietf.org/doc/html/rfc8032#section-7.1

//  ALGORITHM:
//  Ed25519

//  SECRET KEY:
//  4ccd089b28ff96da9db6c346ec114e0f
//  5b8a319f35aba624da8cf6ed4fb8a6fb

//  PUBLIC KEY:
//  3d4017c3e843895a92b70aa74d1b7ebc
//  9c982ccf2ec4968cc0cd55f12af4660c

//  MESSAGE (length 1 byte):
//  72

//  SIGNATURE:
//  92a009a9f0d4cab8720e820b5f642540
//  a2b27b5416503f8fb3762223ebdb69da
//  085ac1e43e15996e458f3613d0f11d8c
//  387b2eaeb4302aeeb00d291612bb0c00

//  SECRET KEY (WORD & BYTE SWAPPED)
static uint32_t kSecretKey[] = {
    0x9b08cd4c, 0xda96ff28, 0x46c3b69d, 0x0f4e11ec,
    0x9f318a5b, 0x24a6ab35, 0xedf68cda, 0xfba6b84f,
};

//  Public KEY (WORD & BYTE SWAPPED)
static uint32_t kPublicKey[] = {
    0xc317403d, 0x5a8943e8, 0xa70ab792, 0xbc7e1b4d,
    0xcf2c989c, 0x8c96c42e, 0xf155cdc0, 0x0c66f42a,
};

//  Signature
//  R: (WORD SWAPPED)
//  S: (WORD & BYTE SWAPPED)
static uint32_t kSignature[] = {
    // R
    0xebdb69da,
    0xb3762223,
    0x16503f8f,
    0xa2b27b54,
    0x5f642540,
    0x720e820b,
    0xf0d4cab8,
    0x92a009a9,
    // S
    0xe4c15a08,
    0x6e99153e,
    0x13368f45,
    0x8c1df1d0,
    0xae2e7b38,
    0xee2a30b4,
    0x16290db0,
    0x000cbb12,
};

// MESSAGE (length 1 byte):
static const char kMessage[] = {
    0x72,
};

status_t ed25519_kat_test(void) {
  // Set up private_key struct.
  otcrypto_unblinded_key_t private_key = {
      .key_mode = kOtcryptoKeyModeEd25519,
      .key_length = kEd25519PrivateKeyBytes,
      .key = kSecretKey,
  };
  private_key.checksum = integrity_unblinded_checksum(&private_key);
  // Set up public_key struct.
  uint32_t public_key_buf[kEd25519PublicKeyWords];
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEd25519,
      .key_length = kEd25519PublicKeyBytes,
      .key = public_key_buf,
  };

  // Run ed25519 key generation.
  CHECK_STATUS_OK(otcrypto_ed25519_keygen(&private_key, &public_key));
  // Check the ed25519 key generation result.
  TRY_CHECK_ARRAYS_EQ(kPublicKey, public_key.key, kEd25519PublicKeyWords);

  // Set up input_message struct.
  const otcrypto_const_byte_buf_t input_message = {
      .data = (const uint8_t *)kMessage,
      .len = ARRAYSIZE(kMessage),
  };
  // Set up signature struct.
  uint32_t signature_data[kEd25519SignatureWords];
  otcrypto_word32_buf_t signature = {.data = signature_data,
                                     .len = ARRAYSIZE(signature_data)};

  // Run ed25519 signature generation.
  CHECK_STATUS_OK(otcrypto_ed25519_sign(
      &private_key, input_message, kOtcryptoEddsaSignModeEddsa, &signature));
  // Check the ed25519 signature generation result.
  TRY_CHECK_ARRAYS_EQ(kSignature, signature.data, kEd25519SignatureWords);

  // Set up signature struct for verification.
  const uint32_t *const signature_verif_data =
      (const uint32_t *const)signature_data;
  otcrypto_const_word32_buf_t signature_verif = {
      .data = signature_verif_data, .len = ARRAYSIZE(signature_data)};

  // Run ed25519 signature verification.
  hardened_bool_t verification_result;
  CHECK_STATUS_OK(otcrypto_ed25519_verify(
      &public_key, input_message, kOtcryptoEddsaSignModeEddsa, signature_verif,
      &verification_result));

  // Signature verification is expected to succeed.
  TRY_CHECK(verification_result == kHardenedBoolTrue);

  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  CHECK_STATUS_OK(entropy_complex_init());

  // Execute the KAT.
  status_t err = ed25519_kat_test();
  if (!status_ok(err)) {
    // Print the error.
    CHECK_STATUS_OK(err);
    return false;
  }

  return true;
}
