// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/math.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/cryptolib_build_info.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/ecc_curve25519.h"
#include "sw/device/lib/crypto/include/ecc_p256.h"
#include "sw/device/lib/crypto/include/ecc_p384.h"
#include "sw/device/lib/crypto/include/hmac.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/sha1.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

/**
 * Android KeyMint VTS (`SigningOperationsTest.Ecdsa*`, `Hmac*`, and
 * `KeyAgreementTest.Ecdh*`) conformance test suite for `otcrypto`.
 *
 * Upstream AOSP Reference:
 *   `hardware/interfaces/security/keymint/aidl/vts/functional/KeyMintTest.cpp`
 *   (Signing/HMAC lines 3422-3950; KeyAgreement lines 8614-8790)
 *
 * Test Mapping:
 *   - `ecc_p256_p384_point_on_curve_test`:
 *     - `TEST_P(KeyAgreementTest, Ecdh)` (L8614)
 *     - P-256 and P-384 `point_on_curve` validation: valid generator points,
 *       rejection of `(0, 0)`, coordinates `x >= p` or `y >= p`, and off-curve
 *       points.
 *   - `ecdsa_p256_p384_sign_verify_and_invalid_sig_test`:
 *     - `TEST_P(SigningOperationsTest, EcdsaAllDigestsAndCurves)` (L3422)
 *     - `TEST_P(SigningOperationsTest, EcdsaAllCurves)` (L3459)
 *     - P-256 and P-384 ECDSA keygen, sign/verify, and rejection of tampered or
 *       zero `(r = 0, s = 0)` signatures.
 *   - `hmac_vts_test`:
 *     - `TEST_P(SigningOperationsTest, HmacAllDigests)` (L3687)
 *     - `TEST_P(SigningOperationsTest, HmacMessageDigestUnique)` (L3709)
 *     - `TEST_P(SigningOperationsTest, HmacSha256TooLargeMacLength)` (L3746)
 *     - `TEST_P(SigningOperationsTest, HmacRfc4231TestCase3)` (L3805)
 *     - `TEST_P(SigningOperationsTest, HmacRfc4231TestCase5)` (L3844)
 *   - `ecdh_ed25519_and_ecdsa_digest_compliance_test`:
 *     - `TEST_P(KeyAgreementTest, Ecdh)` (L8614)
 *     - `TEST_P(KeyAgreementTest, EcdhCurve25519)` (L8664)
 *     - `TEST_P(KeyAgreementTest, EcdhCurve25519Imported)` (L8690)
 *     - `TEST_P(KeyAgreementTest, EcdhCurve25519InvalidSize)` (L8733)
 *     - `TEST_P(KeyAgreementTest, EcdhCurve25519Mismatch)` (L8762)
 *     - `TEST_P(ImportKeyTest, Ed25519RawSuccess)` (L4330)
 *     - `TEST_P(SigningOperationsTest, EcdsaCurve25519)` (L3482)
 *   - `ecdsa_all_digests_and_curves_vts_test`:
 *     - `TEST_P(SigningOperationsTest, EcdsaAllDigestsAndCurves)` (L3422)
 *   - `ecdh_p256_32b_shared_secret_vts_test`:
 *     - `TEST_P(KeyAgreementTest, Ecdh)` (L8614, 32-byte x-coordinate)
 */

enum {
  kP256CoordWords = 256 / 32,
  kP256PointWords = 2 * kP256CoordWords,
  kP256KeyblobBytes = 80,
  kP384CoordWords = 384 / 32,
  kP384PointWords = 2 * kP384CoordWords,
  kP384KeyblobBytes = 112,
};

// NIST P-256 base point G (little-endian words) and prime p.
static const uint32_t kP256Gx[kP256CoordWords] = {
    0xd898c296, 0xf4a13945, 0x2deb33a0, 0x77037d81,
    0x63a440f2, 0xf8bce6e5, 0xe12c4247, 0x6b17d1f2,
};
static const uint32_t kP256Gy[kP256CoordWords] = {
    0x37bf51f5, 0xcbb64068, 0x6b315ece, 0x2bce3357,
    0x7c0f9e16, 0x8ee7eb4a, 0xfe1a7f9b, 0x4fe342e2,
};
static const uint32_t kP256Prime[kP256CoordWords] = {
    0xffffffff, 0xffffffff, 0xffffffff, 0x00000000,
    0x00000000, 0x00000000, 0x00000001, 0xffffffff,
};

// NIST P-384 base point G (little-endian words) and prime p.
static const uint32_t kP384Gx[kP384CoordWords] = {
    0x72760ab7, 0x3a545e38, 0xbf55296c, 0x5502f25d, 0x82542a38, 0x59f741e0,
    0x8ba79b98, 0x6e1d3b62, 0xf320ad74, 0x8eb1c71e, 0xbe8b0537, 0xaa87ca22,
};
static const uint32_t kP384Gy[kP384CoordWords] = {
    0x90ea0e5f, 0x7a431d7c, 0x1d7e819d, 0x0a60b1ce, 0xb5f0b8c0, 0xe9da3113,
    0x289a147c, 0xf8f41dbd, 0x9292dc29, 0x5d9e98bf, 0x96262c6f, 0x3617de4a,
};
static const uint32_t kP384Prime[kP384CoordWords] = {
    0xffffffff, 0x00000000, 0x00000000, 0xffffffff, 0xfffffffe, 0xffffffff,
    0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
};

static const uint32_t kHmacKeyMask[8] = {
    0x1b81540c, 0x220733c9, 0xbf8b380d, 0x05850b42,
    0x3370c9a2, 0x8922d979, 0x1663b2a7, 0xc3b2a580,
};

/**
 * Source:
 *   - `KeyMintTest.cpp:8614` — `TEST_P(KeyAgreementTest, Ecdh)`
 *   - NIST SP 800-56A Section 5.6.2.3.3 full public-key validation
 *
 * Verifies `otcrypto_ecc_p256_point_on_curve` and
 * `otcrypto_ecc_p384_point_on_curve` accept valid curve points and reject
 * `(0, 0)`, coordinates `>= p`, and off-curve coordinates.
 */
static status_t ecc_p256_p384_point_on_curve_test(void) {
  LOG_INFO("Testing P-256 & P-384 point_on_curve validation");

  // 1. P-256 point checks.
  uint32_t p256_pub_buf[kP256PointWords];
  otcrypto_unblinded_key_t p256_pt = {
      .key_mode = kOtcryptoKeyModeEcdhP256,
      .key_length = sizeof(p256_pub_buf),
      .key = p256_pub_buf,
  };
  otcrypto_const_word32_buf_t gx256 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, kP256Gx, kP256CoordWords);
  otcrypto_const_word32_buf_t gy256 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, kP256Gy, kP256CoordWords);
  TRY(otcrypto_ecc_p256_public_key_import(gx256, gy256, &p256_pt));

  hardened_bool_t on_curve = kHardenedBoolFalse;
  TRY(otcrypto_ecc_p256_point_on_curve(&p256_pt, &on_curve));
  TRY_CHECK(on_curve == kHardenedBoolTrue);

  // Off-curve point (Gx, Gy ^ 1).
  uint32_t bad_y256[kP256CoordWords];
  memcpy(bad_y256, kP256Gy, sizeof(bad_y256));
  bad_y256[0] ^= 1u;
  otcrypto_const_word32_buf_t bad_gy256 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, bad_y256, kP256CoordWords);
  TRY(otcrypto_ecc_p256_public_key_import(gx256, bad_gy256, &p256_pt));
  on_curve = kHardenedBoolTrue;
  TRY(otcrypto_ecc_p256_point_on_curve(&p256_pt, &on_curve));
  TRY_CHECK(on_curve == kHardenedBoolFalse);

  // Zero point (0, 0) is not on the curve.
  uint32_t zero256[kP256CoordWords] = {0};
  otcrypto_const_word32_buf_t z256 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, zero256, kP256CoordWords);
  TRY(otcrypto_ecc_p256_public_key_import(z256, z256, &p256_pt));
  on_curve = kHardenedBoolTrue;
  TRY(otcrypto_ecc_p256_point_on_curve(&p256_pt, &on_curve));
  TRY_CHECK(on_curve == kHardenedBoolFalse);

  // Coordinate x == p (out of field range [0, p-1]).
  otcrypto_const_word32_buf_t p256_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kP256Prime, kP256CoordWords);
  TRY(otcrypto_ecc_p256_public_key_import(p256_buf, gy256, &p256_pt));
  on_curve = kHardenedBoolTrue;
  TRY(otcrypto_ecc_p256_point_on_curve(&p256_pt, &on_curve));
  TRY_CHECK(on_curve == kHardenedBoolFalse);

  // 2. P-384 point checks.
  uint32_t p384_pub_buf[kP384PointWords];
  otcrypto_unblinded_key_t p384_pt = {
      .key_mode = kOtcryptoKeyModeEcdhP384,
      .key_length = sizeof(p384_pub_buf),
      .key = p384_pub_buf,
  };
  otcrypto_const_word32_buf_t gx384 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, kP384Gx, kP384CoordWords);
  otcrypto_const_word32_buf_t gy384 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, kP384Gy, kP384CoordWords);
  TRY(otcrypto_ecc_p384_public_key_import(gx384, gy384, &p384_pt));

  on_curve = kHardenedBoolFalse;
  TRY(otcrypto_ecc_p384_point_on_curve(&p384_pt, &on_curve));
  TRY_CHECK(on_curve == kHardenedBoolTrue);

  // Off-curve P-384 point (Gx, Gy ^ 1).
  uint32_t bad_y384[kP384CoordWords];
  memcpy(bad_y384, kP384Gy, sizeof(bad_y384));
  bad_y384[0] ^= 1u;
  otcrypto_const_word32_buf_t bad_gy384 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, bad_y384, kP384CoordWords);
  TRY(otcrypto_ecc_p384_public_key_import(gx384, bad_gy384, &p384_pt));
  on_curve = kHardenedBoolTrue;
  TRY(otcrypto_ecc_p384_point_on_curve(&p384_pt, &on_curve));
  TRY_CHECK(on_curve == kHardenedBoolFalse);

  // Coordinate x == p on P-384.
  otcrypto_const_word32_buf_t p384_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kP384Prime, kP384CoordWords);
  TRY(otcrypto_ecc_p384_public_key_import(p384_buf, gy384, &p384_pt));
  on_curve = kHardenedBoolTrue;
  TRY(otcrypto_ecc_p384_point_on_curve(&p384_pt, &on_curve));
  TRY_CHECK(on_curve == kHardenedBoolFalse);

  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:3422` —
 *     `TEST_P(SigningOperationsTest, EcdsaAllDigestsAndCurves)`
 *   - `KeyMintTest.cpp:3459` —
 *     `TEST_P(SigningOperationsTest, EcdsaAllCurves)`
 *
 * Verifies P-256 and P-384 ECDSA keygen, sign_verify, verify, and rejection of
 * tampered or zero `(r, s)` signatures.
 */
static status_t ecdsa_p256_p384_sign_verify_and_invalid_sig_test(void) {
  LOG_INFO(
      "Testing P-256 & P-384 ECDSA sign/verify and invalid signature "
      "rejection");
  uint32_t keyblob[kP256KeyblobBytes / sizeof(uint32_t)];
  otcrypto_blinded_key_t priv_key = {
      .config =
          {
              .version = otcrypto_lib_version(),
              .key_mode = kOtcryptoKeyModeEcdsaP256,
              .key_length = 32,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = kP256KeyblobBytes,
      .keyblob = keyblob,
  };
  uint32_t pub_buf[kP256PointWords];
  otcrypto_unblinded_key_t pub_key = {
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = sizeof(pub_buf),
      .key = pub_buf,
  };
  TRY(otcrypto_ecdsa_p256_keygen(&priv_key, &pub_key));

  const uint8_t kMsg[] = "KeyMint VTS ECDSA P-256 test payload";
  otcrypto_const_byte_buf_t msg_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kMsg, sizeof(kMsg) - 1);
  uint32_t sig_words[kP256PointWords];
  otcrypto_word32_buf_t sig_out =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig_words, ARRAYSIZE(sig_words));

  TRY(otcrypto_ecdsa_p256_hash_sign_verify(
      &priv_key, &pub_key, kOtcryptoHashModeSha256, &msg_buf, &sig_out));

  otcrypto_const_word32_buf_t sig_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, sig_words, ARRAYSIZE(sig_words));
  hardened_bool_t verif_ok = kHardenedBoolFalse;
  TRY(otcrypto_ecdsa_p256_hash_verify(&pub_key, kOtcryptoHashModeSha256,
                                      &msg_buf, &sig_in, &verif_ok));
  TRY_CHECK(verif_ok == kHardenedBoolTrue);

  // Flip a bit in s and verify signature is rejected.
  sig_words[kP256CoordWords] ^= 1u;
  otcrypto_const_word32_buf_t tampered_sig_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, sig_words, ARRAYSIZE(sig_words));
  verif_ok = kHardenedBoolTrue;
  TRY(otcrypto_ecdsa_p256_hash_verify(&pub_key, kOtcryptoHashModeSha256,
                                      &msg_buf, &tampered_sig_in, &verif_ok));
  TRY_CHECK(verif_ok == kHardenedBoolFalse);

  // Zero signature (r = 0, s = 0) must be rejected (either via
  // OTCRYPTO_BAD_ARGS or verif_ok == kHardenedBoolFalse).
  memset(sig_words, 0, sizeof(sig_words));
  otcrypto_const_word32_buf_t zero_sig_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, sig_words, ARRAYSIZE(sig_words));
  verif_ok = kHardenedBoolTrue;
  otcrypto_status_t zero_status = otcrypto_ecdsa_p256_hash_verify(
      &pub_key, kOtcryptoHashModeSha256, &msg_buf, &zero_sig_in, &verif_ok);
  TRY_CHECK(zero_status.value == OTCRYPTO_BAD_ARGS.value ||
            (zero_status.value == OTCRYPTO_OK.value &&
             verif_ok == kHardenedBoolFalse));

  // KeyMintTest.cpp:3459 (`SigningOperationsTest.EcdsaAllCurves`):
  // Also verify ECDSA P-384 keygen, sign_verify, verify, and tampered signature
  // rejection.
  uint32_t p384_keyblob[112 / sizeof(uint32_t)];
  otcrypto_blinded_key_t p384_priv = {
      .config =
          {
              .version = otcrypto_lib_version(),
              .key_mode = kOtcryptoKeyModeEcdsaP384,
              .key_length = 48,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = sizeof(p384_keyblob),
      .keyblob = p384_keyblob,
  };
  uint32_t p384_pub_buf[kP384PointWords];
  otcrypto_unblinded_key_t p384_pub = {
      .key_mode = kOtcryptoKeyModeEcdsaP384,
      .key_length = sizeof(p384_pub_buf),
      .key = p384_pub_buf,
  };
  TRY(otcrypto_ecdsa_p384_keygen(&p384_priv, &p384_pub));
  uint32_t p384_sig[kP384PointWords];
  otcrypto_word32_buf_t p384_sig_out =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, p384_sig, ARRAYSIZE(p384_sig));
  TRY(otcrypto_ecdsa_p384_hash_sign_verify(
      &p384_priv, &p384_pub, kOtcryptoHashModeSha384, &msg_buf, &p384_sig_out));
  otcrypto_const_word32_buf_t p384_sig_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, p384_sig, ARRAYSIZE(p384_sig));
  verif_ok = kHardenedBoolFalse;
  TRY(otcrypto_ecdsa_p384_hash_verify(&p384_pub, kOtcryptoHashModeSha384,
                                      &msg_buf, &p384_sig_in, &verif_ok));
  TRY_CHECK(verif_ok == kHardenedBoolTrue);

  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:3687` —
 *     `TEST_P(SigningOperationsTest, HmacAllDigests)`
 *   - `KeyMintTest.cpp:3709` —
 *     `TEST_P(SigningOperationsTest, HmacMessageDigestUnique)`
 *   - `KeyMintTest.cpp:3746` —
 *     `TEST_P(SigningOperationsTest, HmacSha256TooLargeMacLength)`
 *   - `KeyMintTest.cpp:3805` —
 *     `TEST_P(SigningOperationsTest, HmacRfc4231TestCase3)`
 *   - `KeyMintTest.cpp:3844` —
 *     `TEST_P(SigningOperationsTest, HmacRfc4231TestCase5)`
 */
static status_t hmac_vts_test(void) {
  LOG_INFO(
      "Testing KeyMint VTS HmacAllDigests, HmacRfc4231TestCase3, and "
      "HmacRfc4231TestCase5");

  // 1. Streaming HMAC-SHA256 (1-byte updates vs one-shot) &
  // `HmacMessageDigestUnique` (`KeyMintTest.cpp:3709`).
  uint32_t hmac_keyblob[16];
  for (size_t i = 0; i < 8; ++i) {
    hmac_keyblob[i] = (0x01020304u + (uint32_t)i) ^ kHmacKeyMask[i];
    hmac_keyblob[8 + i] = kHmacKeyMask[i];
  }
  otcrypto_blinded_key_t hmac_key = {
      .config =
          {
              .version = otcrypto_lib_version(),
              .key_mode = kOtcryptoKeyModeHmacSha256,
              .key_length = 32,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = sizeof(hmac_keyblob),
      .keyblob = hmac_keyblob,
  };
  hmac_key.checksum = otcrypto_integrity_blinded_checksum(&hmac_key);

  uint8_t hmac_msg[100];
  for (size_t i = 0; i < sizeof(hmac_msg); ++i) {
    hmac_msg[i] = (uint8_t)(i ^ 0x5c);
  }
  otcrypto_const_byte_buf_t hmac_msg_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, hmac_msg, sizeof(hmac_msg));
  uint32_t hmac_oneshot[8] = {0};
  otcrypto_word32_buf_t hmac_oneshot_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, hmac_oneshot, ARRAYSIZE(hmac_oneshot));
  TRY(otcrypto_hmac(&hmac_key, &hmac_msg_buf, &hmac_oneshot_buf));

  otcrypto_hmac_context_t hmac_ctx;
  TRY(otcrypto_hmac_init(&hmac_ctx, &hmac_key));
  for (size_t i = 0; i < sizeof(hmac_msg); ++i) {
    otcrypto_const_byte_buf_t byte_in =
        OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, hmac_msg + i, 1);
    TRY(otcrypto_hmac_update(&hmac_ctx, &byte_in));
  }
  uint32_t hmac_stream[8] = {0};
  otcrypto_word32_buf_t hmac_stream_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, hmac_stream, ARRAYSIZE(hmac_stream));
  TRY(otcrypto_hmac_final(&hmac_ctx, &hmac_stream_buf));
  TRY_CHECK_ARRAYS_EQ(hmac_stream, hmac_oneshot, ARRAYSIZE(hmac_oneshot));

  // `HmacSha256TooLargeMacLength` (`KeyMintTest.cpp:3746`): requesting a
  // > 256-bit (9-word) tag on HMAC-SHA256 must fail with `OTCRYPTO_BAD_ARGS`.
  uint32_t too_large_tag[9] = {0};
  otcrypto_word32_buf_t too_large_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, too_large_tag, 9);
  TRY_CHECK(otcrypto_hmac(&hmac_key, &hmac_msg_buf, &too_large_buf).value ==
            OTCRYPTO_BAD_ARGS.value);

  // 2. `KeyMintTest.cpp:3805` (`SigningOperationsTest.HmacRfc4231TestCase3`):
  // 20-byte key `0xaa..aa`, 50-byte message `0xdd..dd` across HMAC-SHA256,
  // HMAC-SHA384, and HMAC-SHA512.
  uint32_t rfc4231_tc3_keyblob[10] = {0};
  memset(rfc4231_tc3_keyblob, 0xaa, 20);
  uint8_t rfc4231_tc3_msg[50];
  memset(rfc4231_tc3_msg, 0xdd, sizeof(rfc4231_tc3_msg));
  otcrypto_const_byte_buf_t tc3_msg_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, rfc4231_tc3_msg, sizeof(rfc4231_tc3_msg));

  const uint8_t kExpectedTc3Sha256[32] = {
      0x77, 0x3e, 0xa9, 0x1e, 0x36, 0x80, 0x0e, 0x46, 0x85, 0x4d, 0xb8,
      0xeb, 0xd0, 0x91, 0x81, 0xa7, 0x29, 0x59, 0x09, 0x8b, 0x3e, 0xf8,
      0xc1, 0x22, 0xd9, 0x63, 0x55, 0x14, 0xce, 0xd5, 0x65, 0xfe,
  };
  const uint8_t kExpectedTc3Sha384[48] = {
      0x88, 0x06, 0x26, 0x08, 0xd3, 0xe6, 0xad, 0x8a, 0x0a, 0xa2, 0xac, 0xe0,
      0x14, 0xc8, 0xa8, 0x6f, 0x0a, 0xa6, 0x35, 0xd9, 0x47, 0xac, 0x9f, 0xeb,
      0xe8, 0x3e, 0xf4, 0xe5, 0x59, 0x66, 0x14, 0x4b, 0x2a, 0x5a, 0xb3, 0x9d,
      0xc1, 0x38, 0x14, 0xb9, 0x4e, 0x3a, 0xb6, 0xe1, 0x01, 0xa3, 0x4f, 0x27,
  };
  const uint8_t kExpectedTc3Sha512[64] = {
      0xfa, 0x73, 0xb0, 0x08, 0x9d, 0x56, 0xa2, 0x84, 0xef, 0xb0, 0xf0,
      0x75, 0x6c, 0x89, 0x0b, 0xe9, 0xb1, 0xb5, 0xdb, 0xdd, 0x8e, 0xe8,
      0x1a, 0x36, 0x55, 0xf8, 0x3e, 0x33, 0xb2, 0x27, 0x9d, 0x39, 0xbf,
      0x3e, 0x84, 0x82, 0x79, 0xa7, 0x22, 0xc8, 0x06, 0xb4, 0x85, 0xa4,
      0x7e, 0x67, 0xc8, 0x07, 0xb9, 0x46, 0xa3, 0x37, 0xbe, 0xe8, 0x94,
      0x26, 0x74, 0x27, 0x88, 0x59, 0xe1, 0x32, 0x92, 0xfb,
  };

  const struct {
    otcrypto_key_mode_t mode;
    size_t tag_words;
    const uint8_t *expected;
  } kTc3Modes[3] = {
      {kOtcryptoKeyModeHmacSha256, 8, kExpectedTc3Sha256},
      {kOtcryptoKeyModeHmacSha384, 12, kExpectedTc3Sha384},
      {kOtcryptoKeyModeHmacSha512, 16, kExpectedTc3Sha512},
  };
  for (size_t m = 0; m < ARRAYSIZE(kTc3Modes); ++m) {
    otcrypto_blinded_key_t tc3_key = {
        .config =
            {
                .version = otcrypto_lib_version(),
                .key_mode = kTc3Modes[m].mode,
                .key_length = 20,
                .hw_backed = kHardenedBoolFalse,
                .security_level = kOtcryptoKeySecurityLevelLow,
            },
        .keyblob_length = sizeof(rfc4231_tc3_keyblob),
        .keyblob = rfc4231_tc3_keyblob,
    };
    tc3_key.checksum = otcrypto_integrity_blinded_checksum(&tc3_key);
    uint32_t tc3_tag[16] = {0};
    otcrypto_word32_buf_t tc3_tag_buf = OTCRYPTO_MAKE_BUF(
        otcrypto_word32_buf_t, tc3_tag, kTc3Modes[m].tag_words);
    TRY(otcrypto_hmac(&tc3_key, &tc3_msg_in, &tc3_tag_buf));
    TRY_CHECK_ARRAYS_EQ((const uint8_t *)tc3_tag, kTc3Modes[m].expected,
                        kTc3Modes[m].tag_words * sizeof(uint32_t));
  }

  // 2b. Android CTS `MacTest.java:95-198` (`SHORT_MSG_KAT_MACS` /
  // `testSmallMsgKat`): 9 KAT vectors (3 each for HmacSHA256, HmacSHA384, and
  // HmacSHA512, including non-word-aligned and >64-byte keys) over the 9-byte
  // message `a16037e3c901c9a1ab`.
  const uint8_t kCtsMacMsg[9] = {
      0xa1, 0x60, 0x37, 0xe3, 0xc9, 0x01, 0xc9, 0xa1, 0xab,
  };
  otcrypto_const_byte_buf_t cts_mac_msg_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, kCtsMacMsg, sizeof(kCtsMacMsg));
  const uint8_t kCtsSha256Key1[30] = {
      0x74, 0xa7, 0xec, 0x4c, 0x79, 0x41, 0x9d, 0x76, 0xfa, 0x5d,
      0x3b, 0xdb, 0xed, 0xc1, 0x7e, 0x5b, 0xeb, 0xf0, 0xee, 0x01,
      0x1c, 0x60, 0x9b, 0x9f, 0x4c, 0x91, 0x26, 0x09, 0x16, 0x13,
  };
  const uint8_t kCtsSha256Mac1[32] = {
      0xc1, 0x7b, 0x62, 0x51, 0x91, 0x55, 0xb0, 0xd7, 0xf0, 0x05, 0xf4,
      0x65, 0xbe, 0xcf, 0x9a, 0x16, 0x10, 0x63, 0x5a, 0xe4, 0x6a, 0x2c,
      0x4d, 0x2b, 0x25, 0x58, 0x51, 0xf2, 0x01, 0x68, 0x9b, 0xa5,
  };
  const uint8_t kCtsSha256Key2[32] = {
      0x42, 0xb4, 0x4e, 0x6a, 0x16, 0x00, 0xbe, 0xd1, 0x0c, 0xa6, 0xc6,
      0xdc, 0x24, 0xdf, 0x28, 0x71, 0x79, 0x0f, 0x94, 0x8e, 0x73, 0xf9,
      0x45, 0x7f, 0xa4, 0x88, 0x9c, 0x34, 0x0c, 0xf6, 0x94, 0x96,
  };
  const uint8_t kCtsSha256Mac2[32] = {
      0xe9, 0x08, 0x2a, 0x5d, 0xb9, 0x8c, 0x80, 0x86, 0xad, 0x30, 0x6a,
      0xc2, 0x3a, 0x1d, 0xa9, 0x47, 0x8e, 0xb5, 0x73, 0x37, 0x57, 0xaf,
      0x6b, 0x11, 0x48, 0xd2, 0x5f, 0xa1, 0x45, 0x92, 0x90, 0xde,
  };
  const uint8_t kCtsSha256Key3[33] = {
      0x20, 0xbf, 0xc4, 0x07, 0xc6, 0x20, 0x22, 0xfe, 0xa9, 0x5f, 0x04,
      0x6f, 0x8a, 0xde, 0x6e, 0xe4, 0xb2, 0x32, 0x66, 0x5a, 0x9e, 0x97,
      0xf7, 0x5d, 0x3e, 0x35, 0xf1, 0xa9, 0x44, 0x79, 0x91, 0x65, 0x1a,
  };
  const uint8_t kCtsSha256Mac3[32] = {
      0xdb, 0xf1, 0x0c, 0xa8, 0xc3, 0x62, 0xaa, 0x66, 0x55, 0x62, 0x06,
      0x5e, 0x76, 0xe4, 0x2b, 0xeb, 0x19, 0x44, 0x4f, 0x61, 0xab, 0x08,
      0x28, 0x43, 0x87, 0x14, 0xc8, 0x27, 0x79, 0xb7, 0x1a, 0x0d,
  };
  const uint8_t kCtsSha384Key1[33] = {
      0x7d, 0x27, 0x7b, 0x2e, 0xc9, 0x5f, 0xca, 0x68, 0xfe, 0x6c, 0xe0,
      0xb6, 0x65, 0xb2, 0x8b, 0x48, 0xe1, 0x28, 0x76, 0x27, 0x14, 0xc6,
      0x6c, 0xa2, 0xc3, 0x40, 0x5b, 0x43, 0x2f, 0x6a, 0xb8, 0x35, 0xe3,
  };
  const uint8_t kCtsSha384Mac1[48] = {
      0xbf, 0x85, 0x55, 0x81, 0x6d, 0x8f, 0xa0, 0x58, 0xe1, 0xd0, 0xed, 0x4b,
      0xe2, 0x3a, 0xbd, 0xa5, 0x22, 0xad, 0xfa, 0xe6, 0x29, 0xb6, 0xa8, 0x81,
      0x9d, 0xcc, 0x24, 0x16, 0xd0, 0x05, 0x07, 0x78, 0x2a, 0xc7, 0x14, 0xfd,
      0xbf, 0xc7, 0xa3, 0x40, 0xda, 0x4e, 0x6c, 0xf6, 0x46, 0xa6, 0x19, 0xf1,
  };
  const uint8_t kCtsSha384Key2[48] = {
      0x7b, 0x30, 0xab, 0xe9, 0x48, 0xce, 0xab, 0x9d, 0x94, 0x96, 0x5f, 0x27,
      0x4f, 0xd2, 0xa2, 0x1c, 0x96, 0x6a, 0xa9, 0xbd, 0xf0, 0x64, 0x76, 0xf9,
      0x4a, 0x0b, 0xcc, 0x6c, 0x20, 0xfd, 0x5d, 0x2b, 0xdc, 0xe2, 0x1a, 0xf7,
      0xc6, 0xfd, 0xf6, 0x01, 0x7b, 0xce, 0x34, 0x2a, 0x70, 0x1f, 0x55, 0xc3,
  };
  const uint8_t kCtsSha384Mac2[48] = {
      0x0f, 0xe5, 0x17, 0x98, 0x52, 0x84, 0x07, 0x11, 0x9a, 0x58, 0x84, 0xf6,
      0x5a, 0xd7, 0x64, 0x09, 0x98, 0x3e, 0x97, 0x8e, 0x25, 0xab, 0x8f, 0x82,
      0xaa, 0x41, 0x2c, 0x08, 0xe7, 0x6c, 0x80, 0x65, 0xd2, 0x6d, 0xfd, 0xb1,
      0x93, 0x5d, 0xe4, 0x90, 0x36, 0xfb, 0x24, 0x26, 0x2a, 0x53, 0x2a, 0x29,
  };
  const uint8_t kCtsSha384Key3[65] = {
      0x26, 0xf2, 0x32, 0xa4, 0x0a, 0xda, 0x35, 0x85, 0x0a, 0x14, 0xed,
      0xf8, 0xf2, 0x3c, 0x9c, 0xa9, 0x78, 0x98, 0xac, 0x0f, 0xa1, 0x86,
      0x40, 0xe5, 0xa7, 0x83, 0x52, 0x30, 0xfa, 0x68, 0xf6, 0x30, 0xb1,
      0xc4, 0x57, 0x9b, 0xc0, 0x59, 0xc3, 0x18, 0xbb, 0x2c, 0x5d, 0xa6,
      0x09, 0xdb, 0x13, 0xf1, 0x56, 0x7f, 0xa1, 0x75, 0xa6, 0x43, 0x9e,
      0x1d, 0x72, 0x97, 0x13, 0xd1, 0xfa, 0x10, 0x39, 0xa3, 0xdb,
  };
  const uint8_t kCtsSha384Mac3[48] = {
      0xa0, 0x86, 0xc6, 0x10, 0xa3, 0x82, 0xc2, 0x4b, 0xb0, 0x5e, 0x8b, 0xdd,
      0x12, 0xcf, 0xfc, 0x01, 0x05, 0x5e, 0xc9, 0x8a, 0x8f, 0x07, 0x12, 0x39,
      0x36, 0x0c, 0xf8, 0x13, 0x52, 0x05, 0xff, 0xee, 0x33, 0x2d, 0xa2, 0x13,
      0x4b, 0xed, 0x2e, 0xc3, 0xef, 0xde, 0x8b, 0xf1, 0x45, 0xd1, 0xd2, 0x57,
  };
  const uint8_t kCtsSha512Key1[17] = {
      0x46, 0xfb, 0x12, 0xef, 0x48, 0xd4, 0xe8, 0x16, 0x2f,
      0x08, 0x28, 0xa6, 0x6c, 0x9f, 0x71, 0x24, 0xde,
  };
  const uint8_t kCtsSha512Mac1[64] = {
      0x03, 0x63, 0x20, 0xb5, 0x13, 0x76, 0xf5, 0x84, 0x0b, 0x03, 0xfd,
      0xab, 0xab, 0xac, 0x53, 0xc1, 0x89, 0xd4, 0xd6, 0xb3, 0x5f, 0x26,
      0xf5, 0x62, 0xa9, 0x09, 0xf8, 0xec, 0xac, 0x4a, 0x02, 0xc2, 0x44,
      0xbf, 0xdd, 0xc8, 0xf4, 0xeb, 0x89, 0xe0, 0xd0, 0x90, 0x9f, 0xd2,
      0xd8, 0xa4, 0x6b, 0x79, 0x61, 0x75, 0xe6, 0x19, 0xcf, 0xf2, 0x15,
      0xa6, 0x75, 0xce, 0x30, 0x95, 0x40, 0x42, 0xb1, 0xc9,
  };
  const uint8_t kCtsSha512Key2[64] = {
      0x45, 0xb3, 0xf1, 0x6b, 0x1a, 0x24, 0x7d, 0xd7, 0x6f, 0x72, 0xab,
      0x2d, 0x50, 0x19, 0xf8, 0x7b, 0x94, 0xef, 0xeb, 0x9a, 0x2f, 0xc0,
      0x1d, 0xa3, 0xca, 0x34, 0x70, 0x50, 0x30, 0x2d, 0xbd, 0xa9, 0xc1,
      0x19, 0xcf, 0x99, 0x1a, 0xaa, 0x30, 0xb7, 0x47, 0xc8, 0x08, 0xec,
      0x6b, 0xc1, 0x9b, 0xe7, 0xb5, 0xae, 0x5e, 0x66, 0x17, 0x6e, 0x38,
      0xf2, 0x22, 0x34, 0x7a, 0x16, 0x59, 0x15, 0xd0, 0x07,
  };
  const uint8_t kCtsSha512Mac2[64] = {
      0x92, 0x81, 0x7c, 0xe3, 0x68, 0x58, 0xcc, 0xad, 0x20, 0xa9, 0x03,
      0xe1, 0x59, 0x52, 0x56, 0x5d, 0x24, 0x1e, 0xba, 0xa8, 0x7e, 0x07,
      0x65, 0x57, 0x54, 0x47, 0x00, 0x90, 0xf1, 0xc6, 0xb9, 0x25, 0x2a,
      0xcf, 0xf9, 0xb8, 0x73, 0xf3, 0x68, 0x40, 0xfa, 0x8f, 0xda, 0xaf,
      0x91, 0xc6, 0xf9, 0xde, 0x3b, 0x82, 0xf4, 0x6d, 0xe0, 0xb1, 0xfd,
      0xfa, 0x58, 0x4e, 0xaf, 0x27, 0xde, 0xf5, 0x2c, 0x65,
  };
  const uint8_t kCtsSha512Key3[65] = {
      0xe9, 0x16, 0x30, 0xc6, 0x9c, 0x8c, 0x29, 0x47, 0x55, 0xe2, 0x7e,
      0x5c, 0xcf, 0x01, 0xfe, 0x09, 0xe0, 0x6d, 0xe6, 0xc4, 0xe4, 0x23,
      0xc1, 0xc4, 0xef, 0x0a, 0xc9, 0xb6, 0x7f, 0x9a, 0xf3, 0xcc, 0x6b,
      0xbc, 0x62, 0x92, 0xd1, 0x8c, 0xf6, 0xe7, 0x67, 0x38, 0x88, 0x8a,
      0x94, 0x8b, 0x49, 0xf9, 0x50, 0x9b, 0x44, 0xeb, 0x3a, 0xf6, 0x97,
      0x4c, 0xa7, 0xe6, 0x1f, 0x52, 0x08, 0xb9, 0xf7, 0xdc, 0xa3,
  };
  const uint8_t kCtsSha512Mac3[64] = {
      0x6f, 0xf5, 0x61, 0x6e, 0x9c, 0x38, 0xce, 0xf3, 0xd2, 0x00, 0x76,
      0x84, 0x1c, 0x65, 0xb8, 0x74, 0x71, 0x93, 0xeb, 0x80, 0x33, 0xea,
      0x61, 0xe8, 0x69, 0x37, 0x15, 0x10, 0x9e, 0x0e, 0x44, 0x89, 0x66,
      0x3d, 0x8a, 0xbc, 0xb2, 0xb7, 0xcf, 0x09, 0x11, 0xe4, 0x61, 0x20,
      0x21, 0x12, 0x81, 0x9f, 0xb8, 0x65, 0x0b, 0xa0, 0x2b, 0xdc, 0xe0,
      0x8a, 0xa0, 0xd2, 0x4b, 0x38, 0x73, 0x30, 0xf1, 0x8f,
  };
  const struct {
    otcrypto_key_mode_t mode;
    const uint8_t *key;
    size_t key_len;
    size_t tag_words;
    const uint8_t *expected_mac;
  } kCtsMacVectors[9] = {
      {kOtcryptoKeyModeHmacSha256, kCtsSha256Key1, 30, 8, kCtsSha256Mac1},
      {kOtcryptoKeyModeHmacSha256, kCtsSha256Key2, 32, 8, kCtsSha256Mac2},
      {kOtcryptoKeyModeHmacSha256, kCtsSha256Key3, 33, 8, kCtsSha256Mac3},
      {kOtcryptoKeyModeHmacSha384, kCtsSha384Key1, 33, 12, kCtsSha384Mac1},
      {kOtcryptoKeyModeHmacSha384, kCtsSha384Key2, 48, 12, kCtsSha384Mac2},
      {kOtcryptoKeyModeHmacSha384, kCtsSha384Key3, 65, 12, kCtsSha384Mac3},
      {kOtcryptoKeyModeHmacSha512, kCtsSha512Key1, 17, 16, kCtsSha512Mac1},
      {kOtcryptoKeyModeHmacSha512, kCtsSha512Key2, 64, 16, kCtsSha512Mac2},
      {kOtcryptoKeyModeHmacSha512, kCtsSha512Key3, 65, 16, kCtsSha512Mac3},
  };
  for (size_t v = 0; v < ARRAYSIZE(kCtsMacVectors); ++v) {
    size_t share_words = ceil_div(kCtsMacVectors[v].key_len, sizeof(uint32_t));
    uint32_t cts_keyblob[36] = {0};
    memcpy(cts_keyblob, kCtsMacVectors[v].key, kCtsMacVectors[v].key_len);
    otcrypto_blinded_key_t cts_key = {
        .config =
            {
                .version = otcrypto_lib_version(),
                .key_mode = kCtsMacVectors[v].mode,
                .key_length = kCtsMacVectors[v].key_len,
                .hw_backed = kHardenedBoolFalse,
                .security_level = kOtcryptoKeySecurityLevelLow,
            },
        .keyblob_length = 2 * share_words * sizeof(uint32_t),
        .keyblob = cts_keyblob,
    };
    cts_key.checksum = otcrypto_integrity_blinded_checksum(&cts_key);
    uint32_t cts_tag[16] = {0};
    otcrypto_word32_buf_t cts_tag_buf = OTCRYPTO_MAKE_BUF(
        otcrypto_word32_buf_t, cts_tag, kCtsMacVectors[v].tag_words);
    TRY(otcrypto_hmac(&cts_key, &cts_mac_msg_in, &cts_tag_buf));
    TRY_CHECK_ARRAYS_EQ((const uint8_t *)cts_tag,
                        kCtsMacVectors[v].expected_mac,
                        kCtsMacVectors[v].tag_words * sizeof(uint32_t));
  }

  // 3. `KeyMintTest.cpp:3844` (`SigningOperationsTest.HmacRfc4231TestCase5`):
  // 20-byte key `0x0c..0c`, message `"Test With Truncation"` (20B), expecting
  // 128-bit (16-byte / 4-word) truncated HMAC tags across SHA-256, SHA-384,
  // and SHA-512!
  // (Currently fails in `hmac.c:345` and `hmac.c:567`, which reject
  // `tag->len != digest_words` with `OTCRYPTO_BAD_ARGS`).
  uint32_t rfc4231_tc5_keyblob[10] = {0};
  memset(rfc4231_tc5_keyblob, 0x0c, 20);
  const uint8_t kTc5Msg[20] = "Test With Truncation";
  otcrypto_const_byte_buf_t tc5_msg_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kTc5Msg, sizeof(kTc5Msg));
  const uint8_t kExpectedTc5Sha256Trunc[16] = {
      0xa3, 0xb6, 0x16, 0x74, 0x73, 0x10, 0x0e, 0xe0,
      0x6e, 0x0c, 0x79, 0x6c, 0x29, 0x55, 0x55, 0x2b,
  };
  const uint8_t kExpectedTc5Sha384Trunc[16] = {
      0x3a, 0xbf, 0x34, 0xc3, 0x50, 0x3b, 0x2a, 0x23,
      0xa4, 0x6e, 0xfc, 0x61, 0x9b, 0xae, 0xf8, 0x97,
  };
  const uint8_t kExpectedTc5Sha512Trunc[16] = {
      0x41, 0x5f, 0xad, 0x62, 0x71, 0x58, 0x0a, 0x53,
      0x1d, 0x41, 0x79, 0xbc, 0x89, 0x1d, 0x87, 0xa6,
  };
  const struct {
    otcrypto_key_mode_t mode;
    const uint8_t *expected;
  } kTc5Modes[3] = {
      {kOtcryptoKeyModeHmacSha256, kExpectedTc5Sha256Trunc},
      {kOtcryptoKeyModeHmacSha384, kExpectedTc5Sha384Trunc},
      {kOtcryptoKeyModeHmacSha512, kExpectedTc5Sha512Trunc},
  };
  otcrypto_status_t tc5_status = OTCRYPTO_OK;
  for (size_t m = 0; m < ARRAYSIZE(kTc5Modes); ++m) {
    otcrypto_blinded_key_t tc5_key = {
        .config =
            {
                .version = otcrypto_lib_version(),
                .key_mode = kTc5Modes[m].mode,
                .key_length = 20,
                .hw_backed = kHardenedBoolFalse,
                .security_level = kOtcryptoKeySecurityLevelLow,
            },
        .keyblob_length = sizeof(rfc4231_tc5_keyblob),
        .keyblob = rfc4231_tc5_keyblob,
    };
    tc5_key.checksum = otcrypto_integrity_blinded_checksum(&tc5_key);
    uint32_t tc5_trunc_tag[4] = {0};
    otcrypto_word32_buf_t tc5_trunc_buf =
        OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, tc5_trunc_tag, 4);
    otcrypto_status_t st = otcrypto_hmac(&tc5_key, &tc5_msg_in, &tc5_trunc_buf);
    if (!status_ok(st)) {
      tc5_status = st;
    } else {
      TRY_CHECK_ARRAYS_EQ((const uint8_t *)tc5_trunc_tag, kTc5Modes[m].expected,
                          16);
    }
  }
  TRY(tc5_status);

  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:8614` — `TEST_P(KeyAgreementTest, Ecdh)`
 *   - `KeyMintTest.cpp:8664` — `TEST_P(KeyAgreementTest, EcdhCurve25519)`
 *   - `KeyMintTest.cpp:8690` —
 *     `TEST_P(KeyAgreementTest, EcdhCurve25519Imported)`
 *   - `KeyMintTest.cpp:8733` —
 *     `TEST_P(KeyAgreementTest, EcdhCurve25519InvalidSize)`
 *   - `KeyMintTest.cpp:8762` —
 *     `TEST_P(KeyAgreementTest, EcdhCurve25519Mismatch)`
 *   - `KeyMintTest.cpp:3482` — `TEST_P(SigningOperationsTest, EcdsaCurve25519)`
 *   - `KeyMintTest.cpp:3422` —
 *     `TEST_P(SigningOperationsTest, EcdsaAllDigestsAndCurves)`
 */
static status_t ecdh_ed25519_and_ecdsa_digest_compliance_test(void) {
  LOG_INFO(
      "Testing P-256 ECDH, X25519, Ed25519, and ECDSA digest-size compliance");

  // 1. P-256 ECDH key agreement between Alice and Bob.
  uint32_t alice_pub_data[kP256PointWords];
  uint32_t alice_priv_blob[kP256KeyblobBytes / sizeof(uint32_t)];
  uint32_t bob_pub_data[kP256PointWords];
  uint32_t bob_priv_blob[kP256KeyblobBytes / sizeof(uint32_t)];

  otcrypto_unblinded_key_t alice_pub = {
      .key_mode = kOtcryptoKeyModeEcdhP256,
      .key_length = sizeof(alice_pub_data),
      .key = alice_pub_data,
  };
  otcrypto_blinded_key_t alice_priv = {
      .config =
          {
              .version = otcrypto_lib_version(),
              .key_mode = kOtcryptoKeyModeEcdhP256,
              .key_length = 32,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = kP256KeyblobBytes,
      .keyblob = alice_priv_blob,
  };
  otcrypto_unblinded_key_t bob_pub = alice_pub;
  bob_pub.key = bob_pub_data;
  otcrypto_blinded_key_t bob_priv = alice_priv;
  bob_priv.keyblob = bob_priv_blob;

  TRY(otcrypto_ecdh_p256_keygen(&alice_priv, &alice_pub));
  TRY(otcrypto_ecdh_p256_keygen(&bob_priv, &bob_pub));

  uint32_t ss_alice_blob[2 * kP256PointWords];
  uint32_t ss_bob_blob[2 * kP256PointWords];
  otcrypto_blinded_key_t ss_alice = {
      .config =
          {
              .version = otcrypto_lib_version(),
              .key_mode = kOtcryptoKeyModeHmacSha512,
              .key_length = 64,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = sizeof(ss_alice_blob),
      .keyblob = ss_alice_blob,
  };
  otcrypto_blinded_key_t ss_bob = ss_alice;
  ss_bob.keyblob = ss_bob_blob;

  TRY(otcrypto_ecdh_p256(&alice_priv, &bob_pub, &ss_alice));
  TRY(otcrypto_ecdh_p256(&bob_priv, &alice_pub, &ss_bob));

  uint32_t ss_a_unmasked[kP256PointWords];
  uint32_t ss_b_unmasked[kP256PointWords];
  for (size_t i = 0; i < kP256PointWords; ++i) {
    ss_a_unmasked[i] = ss_alice_blob[i] ^ ss_alice_blob[kP256PointWords + i];
    ss_b_unmasked[i] = ss_bob_blob[i] ^ ss_bob_blob[kP256PointWords + i];
  }
  TRY_CHECK_ARRAYS_EQ(ss_a_unmasked, ss_b_unmasked, kP256PointWords);

  // 1b. P-384 ECDH key agreement between Alice and Bob (`KeyMintTest.cpp:8614`
  // `KeyAgreementTest.Ecdh`).
  uint32_t p384_alice_pub_data[kP384PointWords];
  uint32_t p384_alice_priv_blob[kP384KeyblobBytes / sizeof(uint32_t)];
  uint32_t p384_bob_pub_data[kP384PointWords];
  uint32_t p384_bob_priv_blob[kP384KeyblobBytes / sizeof(uint32_t)];
  otcrypto_unblinded_key_t p384_alice_pub = {
      .key_mode = kOtcryptoKeyModeEcdhP384,
      .key_length = sizeof(p384_alice_pub_data),
      .key = p384_alice_pub_data,
  };
  otcrypto_blinded_key_t p384_alice_priv = {
      .config =
          {
              .version = otcrypto_lib_version(),
              .key_mode = kOtcryptoKeyModeEcdhP384,
              .key_length = 48,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = kP384KeyblobBytes,
      .keyblob = p384_alice_priv_blob,
  };
  otcrypto_unblinded_key_t p384_bob_pub = p384_alice_pub;
  p384_bob_pub.key = p384_bob_pub_data;
  otcrypto_blinded_key_t p384_bob_priv = p384_alice_priv;
  p384_bob_priv.keyblob = p384_bob_priv_blob;
  TRY(otcrypto_ecdh_p384_keygen(&p384_alice_priv, &p384_alice_pub));
  TRY(otcrypto_ecdh_p384_keygen(&p384_bob_priv, &p384_bob_pub));

  uint32_t p384_ss_alice_blob[2 * kP384PointWords];
  uint32_t p384_ss_bob_blob[2 * kP384PointWords];
  otcrypto_blinded_key_t p384_ss_alice = {
      .config =
          {
              .version = otcrypto_lib_version(),
              .key_mode = kOtcryptoKeyModeHmacSha512,
              .key_length = 96,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = sizeof(p384_ss_alice_blob),
      .keyblob = p384_ss_alice_blob,
  };
  otcrypto_blinded_key_t p384_ss_bob = p384_ss_alice;
  p384_ss_bob.keyblob = p384_ss_bob_blob;
  TRY(otcrypto_ecdh_p384(&p384_alice_priv, &p384_bob_pub, &p384_ss_alice));
  TRY(otcrypto_ecdh_p384(&p384_bob_priv, &p384_alice_pub, &p384_ss_bob));
  uint32_t p384_ss_a_unmasked[kP384PointWords];
  uint32_t p384_ss_b_unmasked[kP384PointWords];
  for (size_t i = 0; i < kP384PointWords; ++i) {
    p384_ss_a_unmasked[i] =
        p384_ss_alice_blob[i] ^ p384_ss_alice_blob[kP384PointWords + i];
    p384_ss_b_unmasked[i] =
        p384_ss_bob_blob[i] ^ p384_ss_bob_blob[kP384PointWords + i];
  }
  TRY_CHECK_ARRAYS_EQ(p384_ss_a_unmasked, p384_ss_b_unmasked, kP384PointWords);

  // KeyMintTest.cpp:8664 (`KeyAgreementTest.EcdhCurve25519`), 8690
  // (`EcdhCurve25519Imported`), 8733 (`EcdhCurve25519InvalidSize`), & 8762
  // (`EcdhCurve25519Mismatch`):
  // Use the imported X25519 key pair from `KeyMintTest.cpp:534-546`:
  const uint8_t kVtsX25519PrivKey[32] = {
      0x68, 0x0f, 0xc0, 0x5d, 0xcd, 0x2f, 0x04, 0x31, 0xfd, 0x27, 0xf0,
      0xaf, 0x69, 0xdf, 0x26, 0xf5, 0xe2, 0xb7, 0x09, 0x43, 0x36, 0x1d,
      0xd2, 0x93, 0x38, 0x7e, 0x4c, 0x84, 0x8d, 0xff, 0x2d, 0x42,
  };
  const uint8_t kVtsX25519PubKey[32] = {
      0xbe, 0x46, 0x92, 0x5a, 0x85, 0x7f, 0x17, 0x83, 0x1d, 0x6d, 0x45,
      0x4b, 0x9d, 0x3d, 0x36, 0xa4, 0xa3, 0x01, 0x66, 0xed, 0xf8, 0x0e,
      0xb8, 0x2b, 0x68, 0x46, 0x61, 0xc3, 0xe2, 0x58, 0xf7, 0x68,
  };
  uint32_t x25519_alice_pub_data[8];
  uint32_t x25519_alice_priv_blob[kP256KeyblobBytes / sizeof(uint32_t)] = {0};
  memcpy(x25519_alice_pub_data, kVtsX25519PubKey, 32);
  memcpy(x25519_alice_priv_blob, kVtsX25519PrivKey, 32);
  uint32_t x25519_bob_pub_data[8];
  uint32_t x25519_bob_priv_blob[kP256KeyblobBytes / sizeof(uint32_t)];
  otcrypto_unblinded_key_t x25519_alice_pub = {
      .key_mode = kOtcryptoKeyModeX25519,
      .key_length = 32,
      .key = x25519_alice_pub_data,
  };
  x25519_alice_pub.checksum =
      otcrypto_integrity_unblinded_checksum(&x25519_alice_pub);
  otcrypto_blinded_key_t x25519_alice_priv = {
      .config =
          {
              .version = otcrypto_lib_version(),
              .key_mode = kOtcryptoKeyModeX25519,
              .key_length = 32,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = sizeof(x25519_alice_priv_blob),
      .keyblob = x25519_alice_priv_blob,
  };
  x25519_alice_priv.checksum =
      otcrypto_integrity_blinded_checksum(&x25519_alice_priv);

  // Verify `otcrypto_x25519_public_key_from_private` reproduces the exact
  // `x25519_pubkey` from `KeyMintTest.cpp:542-546`:
  uint32_t derived_alice_pub_data[8] = {0};
  otcrypto_unblinded_key_t derived_alice_pub = {
      .key_mode = kOtcryptoKeyModeX25519,
      .key_length = 32,
      .key = derived_alice_pub_data,
  };
  TRY(otcrypto_x25519_public_key_from_private(&x25519_alice_priv,
                                              &derived_alice_pub));
  TRY_CHECK_ARRAYS_EQ((const uint8_t *)derived_alice_pub_data, kVtsX25519PubKey,
                      sizeof(kVtsX25519PubKey));

  otcrypto_unblinded_key_t x25519_bob_pub = x25519_alice_pub;
  x25519_bob_pub.key = x25519_bob_pub_data;
  otcrypto_blinded_key_t x25519_bob_priv = {
      .config = x25519_alice_priv.config,
      .keyblob_length = sizeof(x25519_bob_priv_blob),
      .keyblob = x25519_bob_priv_blob,
  };

  TRY(otcrypto_x25519_keygen(&x25519_bob_priv, &x25519_bob_pub));

  uint32_t x25519_ss_a_blob[16];
  uint32_t x25519_ss_b_blob[16];
  otcrypto_blinded_key_t x25519_ss_a = {
      .config =
          {
              .version = otcrypto_lib_version(),
              .key_mode = kOtcryptoKeyModeAesCtr,
              .key_length = 32,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = sizeof(x25519_ss_a_blob),
      .keyblob = x25519_ss_a_blob,
  };
  otcrypto_blinded_key_t x25519_ss_b = x25519_ss_a;
  x25519_ss_b.keyblob = x25519_ss_b_blob;

  TRY(otcrypto_x25519(&x25519_alice_priv, &x25519_bob_pub, &x25519_ss_a));
  TRY(otcrypto_x25519(&x25519_bob_priv, &x25519_alice_pub, &x25519_ss_b));
  uint32_t x25519_a_unmasked[8];
  uint32_t x25519_b_unmasked[8];
  for (size_t i = 0; i < 8; ++i) {
    x25519_a_unmasked[i] = x25519_ss_a_blob[i] ^ x25519_ss_a_blob[8 + i];
    x25519_b_unmasked[i] = x25519_ss_b_blob[i] ^ x25519_ss_b_blob[8 + i];
  }
  TRY_CHECK_ARRAYS_EQ(x25519_a_unmasked, x25519_b_unmasked, 8);

  // `EcdhCurve25519InvalidSize` (`KeyMintTest.cpp:8733`): wrong public key size
  // (`31` bytes) -> `OTCRYPTO_BAD_ARGS`.
  otcrypto_unblinded_key_t x25519_bad_size = x25519_bob_pub;
  x25519_bad_size.key_length = 31;
  x25519_bad_size.checksum =
      otcrypto_integrity_unblinded_checksum(&x25519_bad_size);
  TRY_CHECK(otcrypto_x25519(&x25519_alice_priv, &x25519_bad_size, &x25519_ss_a)
                .value == OTCRYPTO_BAD_ARGS.value);

  // `EcdhCurve25519Mismatch` (`KeyMintTest.cpp:8762`): passing P-256 public key
  // (`bob_pub`) to `otcrypto_x25519` -> `OTCRYPTO_BAD_ARGS`.
  TRY_CHECK(otcrypto_x25519(&x25519_alice_priv, &bob_pub, &x25519_ss_a).value ==
            OTCRYPTO_BAD_ARGS.value);

  // 2. `SigningOperationsTest.EcdsaCurve25519` (`KeyMintTest.cpp:3482`) &
  // `ImportKeyTest.Ed25519RawSuccess` (`KeyMintTest.cpp:495-510, 4330-4363`):
  // Ed25519 imported keypair public-key derivation + sign/verify, keygen,
  // sign/verify, and tampered signature rejection.
  const uint8_t kVtsEd25519PrivKey[32] = {
      0xa9, 0x77, 0x03, 0x9a, 0xae, 0x37, 0x2c, 0x1c, 0x8f, 0x53, 0xfe,
      0xd1, 0x72, 0x3d, 0x48, 0x16, 0xa5, 0x14, 0xf2, 0x2f, 0x3b, 0x9d,
      0x8d, 0xc5, 0xc7, 0x8c, 0x2d, 0x11, 0xfa, 0x75, 0x59, 0x91,
  };
  const uint8_t kVtsEd25519PubKey[32] = {
      0xef, 0xbb, 0x01, 0xf3, 0xfb, 0x74, 0xda, 0x43, 0xaf, 0x43, 0xd9,
      0xd8, 0xa0, 0xc6, 0x5c, 0xf4, 0x7c, 0x57, 0xec, 0x66, 0x0d, 0x2b,
      0x3e, 0xa8, 0x10, 0x69, 0xed, 0xe3, 0x04, 0xf4, 0x56, 0x91,
  };
  uint32_t ed_imported_pub_data[8];
  uint32_t ed_imported_priv_blob[kP256KeyblobBytes / sizeof(uint32_t)] = {0};
  memcpy(ed_imported_pub_data, kVtsEd25519PubKey, 32);
  memcpy(ed_imported_priv_blob, kVtsEd25519PrivKey, 32);
  otcrypto_unblinded_key_t ed_imported_pub = {
      .key_mode = kOtcryptoKeyModeEd25519,
      .key_length = 32,
      .key = ed_imported_pub_data,
  };
  ed_imported_pub.checksum =
      otcrypto_integrity_unblinded_checksum(&ed_imported_pub);
  otcrypto_blinded_key_t ed_imported_priv = {
      .config =
          {
              .version = otcrypto_lib_version(),
              .key_mode = kOtcryptoKeyModeEd25519,
              .key_length = 32,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = sizeof(ed_imported_priv_blob),
      .keyblob = ed_imported_priv_blob,
  };
  ed_imported_priv.checksum =
      otcrypto_integrity_blinded_checksum(&ed_imported_priv);

  uint32_t derived_ed_pub_data[8] = {0};
  otcrypto_unblinded_key_t derived_ed_pub = {
      .key_mode = kOtcryptoKeyModeEd25519,
      .key_length = 32,
      .key = derived_ed_pub_data,
  };
  TRY(otcrypto_ed25519_public_key_from_private(&ed_imported_priv,
                                               &derived_ed_pub));
  TRY_CHECK_ARRAYS_EQ((const uint8_t *)derived_ed_pub_data, kVtsEd25519PubKey,
                      sizeof(kVtsEd25519PubKey));

  uint8_t ed_import_msg[32];
  memset(ed_import_msg, 'a', sizeof(ed_import_msg));
  otcrypto_const_byte_buf_t ed_import_msg_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, ed_import_msg, sizeof(ed_import_msg));
  uint32_t ed_sig[16];
  otcrypto_word32_buf_t ed_sig_out =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, ed_sig, ARRAYSIZE(ed_sig));
  otcrypto_const_word32_buf_t ed_sig_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, ed_sig, ARRAYSIZE(ed_sig));
  TRY(otcrypto_ed25519_sign(&ed_imported_priv, &ed_import_msg_in,
                            kOtcryptoEddsaSignModeEddsa, &ed_sig_out));
  hardened_bool_t ed_ok = kHardenedBoolFalse;
  TRY(otcrypto_ed25519_verify(&ed_imported_pub, &ed_import_msg_in,
                              kOtcryptoEddsaSignModeEddsa, &ed_sig_in, &ed_ok));
  TRY_CHECK(ed_ok == kHardenedBoolTrue);

  uint32_t ed_pub_data[8];
  uint32_t ed_priv_blob[kP256KeyblobBytes / sizeof(uint32_t)];
  otcrypto_unblinded_key_t ed_pub = {
      .key_mode = kOtcryptoKeyModeEd25519,
      .key_length = 32,
      .key = ed_pub_data,
  };
  otcrypto_blinded_key_t ed_priv = {
      .config =
          {
              .version = otcrypto_lib_version(),
              .key_mode = kOtcryptoKeyModeEd25519,
              .key_length = 32,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = sizeof(ed_priv_blob),
      .keyblob = ed_priv_blob,
  };
  TRY(otcrypto_ed25519_keygen(&ed_priv, &ed_pub));

  const uint8_t kEdMsg[] = "KeyMint VTS Ed25519 message";
  otcrypto_const_byte_buf_t ed_msg_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kEdMsg, sizeof(kEdMsg) - 1);
  TRY(otcrypto_ed25519_sign(&ed_priv, &ed_msg_in, kOtcryptoEddsaSignModeEddsa,
                            &ed_sig_out));
  ed_ok = kHardenedBoolFalse;
  TRY(otcrypto_ed25519_verify(&ed_pub, &ed_msg_in, kOtcryptoEddsaSignModeEddsa,
                              &ed_sig_in, &ed_ok));
  TRY_CHECK(ed_ok == kHardenedBoolTrue);

  // Tamper with scalar S (`ed_sig[8]`): `otcrypto_ed25519_verify` must return
  // `OTCRYPTO_OK` with `ed_ok == kHardenedBoolFalse`.
  ed_sig[8] ^= 1u;
  ed_ok = kHardenedBoolTrue;
  TRY(otcrypto_ed25519_verify(&ed_pub, &ed_msg_in, kOtcryptoEddsaSignModeEddsa,
                              &ed_sig_in, &ed_ok));
  TRY_CHECK(ed_ok == kHardenedBoolFalse);
  ed_sig[8] ^= 1u;

  // Tampering with point R (`ed_sig[0]`) must also return `OTCRYPTO_OK` with
  // `ed_ok == kHardenedBoolFalse` (currently fails in
  // `curve25519_verify_finalize` at `curve25519.c:318-321`, which returns
  // `OTCRYPTO_BAD_ARGS` when the corrupted R point is not on the curve).
  otcrypto_status_t ed_r_status = OTCRYPTO_OK;
  for (uint32_t bit = 0; bit < 8; ++bit) {
    ed_sig[0] ^= (1u << bit);
    ed_ok = kHardenedBoolTrue;
    otcrypto_status_t st = otcrypto_ed25519_verify(
        &ed_pub, &ed_msg_in, kOtcryptoEddsaSignModeEddsa, &ed_sig_in, &ed_ok);
    ed_sig[0] ^= (1u << bit);
    if (!status_ok(st)) {
      ed_r_status = st;
    } else {
      TRY_CHECK(ed_ok == kHardenedBoolFalse);
    }
  }
  TRY(ed_r_status);

  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:3422` —
 *     `TEST_P(SigningOperationsTest, EcdsaAllDigestsAndCurves)`
 *
 * Verifies ECDSA P-256 and P-384 signing and verification across all VTS
 * digests (`SHA-1`, `SHA-256`, `SHA-384`, `SHA-512`) (currently fails in
 * `ecc_p256.c:295` and `ecc_p384.c:302`, which reject digests whose length
 * does not match the curve scalar size).
 */
static status_t ecdsa_all_digests_and_curves_vts_test(void) {
  LOG_INFO(
      "Testing KeyMint VTS EcdsaAllDigestsAndCurves (SHA-1, SHA-256, SHA-384, "
      "SHA-512)");
  uint32_t pub_data[kP256PointWords];
  uint32_t priv_blob[kP256KeyblobBytes / sizeof(uint32_t)];
  otcrypto_unblinded_key_t pub = {
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = sizeof(pub_data),
      .key = pub_data,
  };
  otcrypto_blinded_key_t priv = {
      .config =
          {
              .version = otcrypto_lib_version(),
              .key_mode = kOtcryptoKeyModeEcdsaP256,
              .key_length = 32,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = kP256KeyblobBytes,
      .keyblob = priv_blob,
  };
  TRY(otcrypto_ecdsa_p256_keygen(&priv, &pub));

  const uint8_t kMsg[] = "KeyMint VTS EcdsaAllDigestsAndCurves";
  otcrypto_const_byte_buf_t msg_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kMsg, sizeof(kMsg) - 1);
  uint32_t ecdsa_sig[kP256PointWords];
  otcrypto_word32_buf_t ecdsa_sig_out =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, ecdsa_sig, ARRAYSIZE(ecdsa_sig));
  TRY(otcrypto_ecdsa_p256_hash_sign_verify(&priv, &pub, kOtcryptoHashModeSha256,
                                           &msg_in, &ecdsa_sig_out));
  otcrypto_status_t p256_sha1_st = otcrypto_ecdsa_p256_hash_sign_verify(
      &priv, &pub, kOtcryptoHashModeSha1, &msg_in, &ecdsa_sig_out);
  otcrypto_status_t p256_sha384_st = otcrypto_ecdsa_p256_hash_sign_verify(
      &priv, &pub, kOtcryptoHashModeSha384, &msg_in, &ecdsa_sig_out);
  otcrypto_status_t p256_sha512_st = otcrypto_ecdsa_p256_hash_sign_verify(
      &priv, &pub, kOtcryptoHashModeSha512, &msg_in, &ecdsa_sig_out);

  uint32_t p384_pub_data[kP384PointWords];
  uint32_t p384_priv_blob[kP384KeyblobBytes / sizeof(uint32_t)];
  otcrypto_unblinded_key_t p384_pub = {
      .key_mode = kOtcryptoKeyModeEcdsaP384,
      .key_length = sizeof(p384_pub_data),
      .key = p384_pub_data,
  };
  otcrypto_blinded_key_t p384_priv = {
      .config =
          {
              .version = otcrypto_lib_version(),
              .key_mode = kOtcryptoKeyModeEcdsaP384,
              .key_length = 48,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = kP384KeyblobBytes,
      .keyblob = p384_priv_blob,
  };
  TRY(otcrypto_ecdsa_p384_keygen(&p384_priv, &p384_pub));
  uint32_t p384_sig[kP384PointWords];
  otcrypto_word32_buf_t p384_sig_out =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, p384_sig, ARRAYSIZE(p384_sig));
  TRY(otcrypto_ecdsa_p384_hash_sign_verify(
      &p384_priv, &p384_pub, kOtcryptoHashModeSha384, &msg_in, &p384_sig_out));
  otcrypto_status_t p384_sha1_st = otcrypto_ecdsa_p384_hash_sign_verify(
      &p384_priv, &p384_pub, kOtcryptoHashModeSha1, &msg_in, &p384_sig_out);
  otcrypto_status_t p384_sha256_st = otcrypto_ecdsa_p384_hash_sign_verify(
      &p384_priv, &p384_pub, kOtcryptoHashModeSha256, &msg_in, &p384_sig_out);
  otcrypto_status_t p384_sha512_st = otcrypto_ecdsa_p384_hash_sign_verify(
      &p384_priv, &p384_pub, kOtcryptoHashModeSha512, &msg_in, &p384_sig_out);

  TRY_CHECK(status_ok(p256_sha1_st) && status_ok(p256_sha384_st) &&
            status_ok(p256_sha512_st) && status_ok(p384_sha1_st) &&
            status_ok(p384_sha256_st) && status_ok(p384_sha512_st));
  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:8614` — `TEST_P(KeyAgreementTest, Ecdh)`
 *
 * Verifies 32-byte (`x`-coordinate only) ECDH P-256 shared secret output
 * (currently fails in `ecc_p256.c:1055`, which requires `key_length == 64` and
 * leaves OTBN running in the background after returning `OTCRYPTO_BAD_ARGS`).
 */
static status_t ecdh_p256_32b_shared_secret_vts_test(void) {
  LOG_INFO("Testing KeyMint VTS KeyAgreementTest.Ecdh (32B x-coordinate)");
  uint32_t alice_pub_data[kP256PointWords];
  uint32_t alice_priv_blob[kP256KeyblobBytes / sizeof(uint32_t)];
  uint32_t bob_pub_data[kP256PointWords];
  uint32_t bob_priv_blob[kP256KeyblobBytes / sizeof(uint32_t)];

  otcrypto_unblinded_key_t alice_pub = {
      .key_mode = kOtcryptoKeyModeEcdhP256,
      .key_length = sizeof(alice_pub_data),
      .key = alice_pub_data,
  };
  otcrypto_blinded_key_t alice_priv = {
      .config =
          {
              .version = otcrypto_lib_version(),
              .key_mode = kOtcryptoKeyModeEcdhP256,
              .key_length = 32,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = kP256KeyblobBytes,
      .keyblob = alice_priv_blob,
  };
  otcrypto_unblinded_key_t bob_pub = alice_pub;
  bob_pub.key = bob_pub_data;
  otcrypto_blinded_key_t bob_priv = alice_priv;
  bob_priv.keyblob = bob_priv_blob;

  TRY(otcrypto_ecdh_p256_keygen(&alice_priv, &alice_pub));
  TRY(otcrypto_ecdh_p256_keygen(&bob_priv, &bob_pub));

  uint32_t ss_32b_blob[2 * kP256CoordWords];
  otcrypto_blinded_key_t ss_32b = {
      .config =
          {
              .version = otcrypto_lib_version(),
              .key_mode = kOtcryptoKeyModeAesCtr,
              .key_length = 32,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = sizeof(ss_32b_blob),
      .keyblob = ss_32b_blob,
  };
  TRY(otcrypto_ecdh_p256(&alice_priv, &bob_pub, &ss_32b));
  return OK_STATUS();
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t result = OK_STATUS();
  otcrypto_state_t state = {0};
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow, &state));

  EXECUTE_TEST(result, ecc_p256_p384_point_on_curve_test);
  EXECUTE_TEST(result, ecdsa_p256_p384_sign_verify_and_invalid_sig_test);
  EXECUTE_TEST(result, hmac_vts_test);
  EXECUTE_TEST(result, ecdh_ed25519_and_ecdsa_digest_compliance_test);
  EXECUTE_TEST(result, ecdsa_all_digests_and_curves_vts_test);
  EXECUTE_TEST(result, ecdh_p256_32b_shared_secret_vts_test);

  return status_ok(result);
}
