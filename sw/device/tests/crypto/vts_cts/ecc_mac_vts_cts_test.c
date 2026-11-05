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
#include "sw/device/lib/crypto/include/ecc_p256.h"
#include "sw/device/lib/crypto/include/hkdf.h"
#include "sw/device/lib/crypto/include/hmac.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/key_transport.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

/**
 * Android KeyMint VTS (`SecurityLevel::STRONGBOX`:
 * `SigningOperationsTest.Ecdsa*`, `Hmac*`, and `KeyAgreementTest.Ecdh*`) and
 * Android CTS (`StrongboxMacTest`, `StrongboxECDSASignatureTest`,
 * `StrongboxKeyAgreementTest`, and `SignatureTest` with `isStrongbox = true`)
 * conformance test suite for `otcrypto`.
 *
 * StrongBox Profile (`KeyMintAidlTestBase.cpp:1597-1645`, `MacTest.java:76`,
 * `util/TestUtils.java:160`):
 *   - `ValidCurves()`: `{EcCurve::P_256}` (P-224, P-384, P-521, and CURVE_25519
 *     are not required on StrongBox).
 *   - `ValidDigests(withNone, withMD5)`: `{Digest::NONE, Digest::SHA_2_256}`.
 *   - `EXPECTED_ALGORITHMS_STRONGBOX` (`MacTest.java:76`): `{"HmacSHA256"}`.
 *
 * Upstream AOSP References:
 *   - `hardware/interfaces/security/keymint/aidl/vts/functional/`
 *     - `KeyMintAidlTestBase.cpp` (lines 1597-1645)
 *     - `KeyMintTest.cpp` (Signing/HMAC lines 3422-3950; KeyAgreement lines
 *       8614-8660)
 *   - `cts/tests/tests/keystore/src/android/keystore/cts/`
 *     - `MacTest.java` & `StrongboxMacTest.java`
 *     - `SignatureTest.java`, `ECDSASignatureTest.java`, &
 *       `StrongboxECDSASignatureTest.java`
 *     - `KeyAgreementTest.java` & `StrongboxKeyAgreementTest.java`
 *     - `util/TestUtils.java`
 *   - `cts/tests/tests/keystore/res/raw/`
 *     - `ec_key1_pkcs8.der` & `ec_key4_secp256r1_pkcs8.der`
 *
 * Test Mapping:
 *   - `ecc_p256_point_on_curve_test`:
 *     - `TEST_P(KeyAgreementTest, Ecdh)` (L8614)
 *     - P-256 `point_on_curve` validation: valid generator point, rejection of
 *       `(0, 0)`, coordinates `x >= p` or `y >= p`, and off-curve points.
 *   - `ecdsa_p256_sign_verify_and_invalid_sig_test`:
 *     - `TEST_P(SigningOperationsTest, EcdsaAllDigestsAndCurves)` (L3422)
 *     - `TEST_P(SigningOperationsTest, EcdsaAllCurves)` (L3459)
 *     - `KeyMintTest.cpp:307` (`ec_256_key` imported P-256 key)
 *     - `SignatureTest.java:114-119` (`SHA256withECDSA` short-message KAT)
 *     - `SignatureTest.java:242-248, 756` (`SHA256withECDSA` long-message KAT)
 *     - `ECDSASignatureTest.java:282` (`ec_key4_secp256r1_pkcs8.der` imported
 *       key)
 *     - P-256 ECDSA keygen, sign/verify with `SHA-256`, and rejection of
 *       tampered or zero `(r = 0, s = 0)` signatures.
 *   - `hmac_vts_test`:
 *     - `TEST_P(SigningOperationsTest, HmacAllDigests)` (L3687, `SHA_2_256`)
 *     - `TEST_P(SigningOperationsTest, HmacMessageDigestUnique)` (L3709)
 *     - `TEST_P(SigningOperationsTest, HmacSha256TooLargeMacLength)` (L3746)
 *     - `TEST_P(SigningOperationsTest, HmacSha256TooSmallMacLength)` (L3786)
 *     - `TEST_P(SigningOperationsTest, HmacRfc4231TestCase3)` (L3805)
 *     - `MacTest.java:94, 112-135, 273, 380-403, 640` (`StrongboxMacTest`
 *       `HmacSHA256` default 64B `KAT_KEY`, 0-byte empty message, short-message
 *       KATs in one-shot, 1B chunks, and 3B chunks, and streaming long-message)
 *   - `ecdh_p256_vts_test`:
 *     - `TEST_P(KeyAgreementTest, Ecdh)` (L8614, `EcCurve::P_256`)
 *     - `KeyAgreementTest.java:121` (`testGenerateSecret_withImportedKey` with
 *       `ec_key4_secp256r1_pkcs8.der` and `KeyMintTest.cpp:307` `ec_256_key`)
 *   - `ecdsa_all_digests_and_curves_vts_test`:
 *     - `TEST_P(SigningOperationsTest, EcdsaAllDigestsAndCurves)` (L3422,
 *       `EcCurve::P_256` with `Digest::NONE` and `Digest::SHA_2_256`)
 *     - `TEST_P(SigningOperationsTest, EcdsaNoDigestHugeData)` (L3580)
 *     - `SignatureTest.java:103-107` (`NONEwithECDSA` short-message KAT)
 *     - `SignatureTest.java:236-241, 756` (`NONEwithECDSA` long-message KAT)
 *     - `ECDSASignatureTest.java:69`
 *       (`testNONEwithECDSATruncatesInputToFieldSize`)
 *     - `ECDSASignatureTest.java:120`
 *       (`testNONEwithECDSASupportsMessagesShorterThanFieldSize`)
 *     - `ECDSASignatureTest.java:142` (`testECDSANonceReuse`)
 *     - `ECDSASignatureTest.java:155` (`testBoringSslKat` 50B truncated to 32B)
 *   - `hmac_rfc4231_truncated_tag_vts_test`:
 *     - `TEST_P(SigningOperationsTest, HmacRfc4231TestCase5)` (L3844, 16B
 *       truncated tag)
 *   - `ecdsa_p256_hash_null_mode_test`:
 *     - `TEST_P(SigningOperationsTest, EcdsaAllDigestsAndCurves)` (L3422) &
 *       `SignatureTest.java:103-107` (`NONEwithECDSA` via
 *       `otcrypto_ecdsa_p256_sign_verify` with `kOtcryptoHashModeNull`)
 *   - `ecdh_p256_32b_shared_secret_vts_test`:
 *     - `TEST_P(KeyAgreementTest, Ecdh)` (L8614, 32-byte x-coordinate)
 */

enum {
  kP256CoordWords = 256 / 32,
  kSha256DigestWords = 256 / 32,
  kP256PointWords = 2 * kP256CoordWords,
  kP256MaskedScalarShareWords = 10,
  kP256KeyblobBytes = 80,
};

// Android CTS `R.raw.ec_key4_secp256r1_pkcs8` (`ECDSASignatureTest.java:282`,
// `KeyAgreementTest.java:121`).
static const uint32_t kCtsEcKey4D[kP256CoordWords] = {
    0xd9369dfe, 0x6ddbd9d5, 0x02baa8d4, 0x09c61630,
    0x27d60af7, 0xe532e19d, 0x5a2b8803, 0xdceadcd7,
};
static const uint32_t kCtsEcKey4X[kP256CoordWords] = {
    0x28fbca79, 0x4ce60e3e, 0x7eb31d61, 0x7228a458,
    0x9ef646b4, 0xedc3449f, 0xf1c0028c, 0xa04f338a,
};
static const uint32_t kCtsEcKey4Y[kP256CoordWords] = {
    0x568313a7, 0x55c1f79d, 0x140a63a2, 0x36f92676,
    0x74437f5f, 0x60cb8d01, 0x2496d8ae, 0xe636fc5e,
};

// Android KeyMint VTS `ec_256_key` (`KeyMintTest.cpp:307`).
static const uint32_t kVtsEcP256D[kP256CoordWords] = {
    0xf3a4d859, 0x99986481, 0x366bc032, 0x941eed09,
    0x9b4ed3ff, 0xbf2930aa, 0x7b8d1940, 0x737c2ecd,
};
static const uint32_t kVtsEcP256X[kP256CoordWords] = {
    0xb2b528bb, 0x8c7ddd9a, 0x024e3bdd, 0x9a14dd8a,
    0x48b4778a, 0x61683bc6, 0x0d07c254, 0xbf85d772,
};
static const uint32_t kVtsEcP256Y[kP256CoordWords] = {
    0xb2183bfe, 0xd44949e0, 0x3376d11f, 0xb00083cf,
    0xbcc41c6e, 0x0bd0ce21, 0xf14ebbbb, 0xc7aa1b51,
};

// Android CTS `SignatureTest.java:232-248, 756` (`testLongMsgKat` over
// `3 * 1024 * 1024 + 123` bytes generated via `TestUtils.generateLargeKatMsg`
// from `kCtsEcdsaMsg`): leftmost 32 bytes (used by `NONEwithECDSA`) and
// SHA-256 digest (used by `SHA256withECDSA`).
static const uint8_t kCtsSigLongMsgPrefix32[32] = {
    0x85, 0xb9, 0xfe, 0x4b, 0xe3, 0x6c, 0x65, 0xdd, 0xb0, 0xb3, 0x4b,
    0x82, 0xac, 0x19, 0x9f, 0x8e, 0xa6, 0xa4, 0x9b, 0x49, 0xf3, 0x33,
    0x04, 0x77, 0xd7, 0x6f, 0x0a, 0x6e, 0xdf, 0xf8, 0x6f, 0xa0,
};
static const uint32_t kCtsSigLongMsgSha256Digest[kP256CoordWords] = {
    0x4fddb69b, 0x635b84a3, 0x2ee8a8c5, 0x6c4c6ba9,
    0x4552820f, 0x36f4d81d, 0x75b8a434, 0x4124bc8b,
};
static const uint8_t kCtsEcdsaMsg[23] = {
    0xec, 0x17, 0x47, 0x29, 0xc4, 0xf5, 0xc5, 0x70, 0xba, 0x0d, 0xe4, 0xc4,
    0x24, 0xcd, 0xcb, 0xf0, 0x36, 0x2a, 0x77, 0x18, 0x03, 0x94, 0x64,
};
// Android CTS `R.raw.ec_key1_pkcs8` P-256 public key coordinates (little-endian
// words).
static const uint32_t kCtsEcKey1X[kP256CoordWords] = {
    0x0c35eac5, 0x161fb212, 0xd7cd5d92, 0xa1ca828f,
    0x5f20dca1, 0x53b9f6ac, 0x03ea81e8, 0x7e05188a,
};
static const uint32_t kCtsEcKey1Y[kP256CoordWords] = {
    0x1de707f8, 0x58d161d7, 0x055bc908, 0x239d6063,
    0x2ddff95e, 0x23057c32, 0xd01a5101, 0x2eab079e,
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

static const uint32_t kHmacKeyMask[8] = {
    0x1b81540c, 0x220733c9, 0xbf8b380d, 0x05850b42,
    0x3370c9a2, 0x8922d979, 0x1663b2a7, 0xc3b2a580,
};

/**
 * Source:
 *   - `KeyMintTest.cpp:8614` — `TEST_P(KeyAgreementTest, Ecdh)`
 *   - NIST SP 800-56A Section 5.6.2.3.3 full public-key validation
 *
 * Verifies `otcrypto_ecc_p256_point_on_curve` accepts valid curve points and
 * rejects `(0, 0)`, coordinates `>= p`, and off-curve coordinates.
 */
static status_t ecc_p256_point_on_curve_test(void) {
  LOG_INFO("Testing StrongBox P-256 point_on_curve validation");

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

  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:3422` —
 *     `TEST_P(SigningOperationsTest, EcdsaAllDigestsAndCurves)`
 *   - `KeyMintTest.cpp:3459` —
 *     `TEST_P(SigningOperationsTest, EcdsaAllCurves)`
 *   - `SignatureTest.java:114-119` (`SHA256withECDSA` KAT signature)
 *
 * Verifies StrongBox P-256 ECDSA keygen, sign_verify, verify with `SHA-256`,
 * rejection of tampered or zero `(r, s)` signatures, and the Android CTS
 * `SHA256withECDSA` KAT vector.
 */
static status_t ecdsa_p256_sign_verify_and_invalid_sig_test(void) {
  LOG_INFO(
      "Testing StrongBox P-256 ECDSA sign/verify (SHA-256) and invalid "
      "signature rejection");
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
  uint32_t msg_digest_words[kSha256DigestWords];
  otcrypto_hash_digest_t msg_digest = {
      .mode = kOtcryptoHashModeSha256,
      .data = msg_digest_words,
      .len = ARRAYSIZE(msg_digest_words),
  };
  TRY(otcrypto_sha2_256(&msg_buf, &msg_digest));

  uint32_t sig_words[kP256PointWords];
  otcrypto_word32_buf_t sig_out =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig_words, ARRAYSIZE(sig_words));

  TRY(otcrypto_ecdsa_p256_sign_verify(&priv_key, &pub_key, msg_digest,
                                      &sig_out));

  otcrypto_const_word32_buf_t sig_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, sig_words, ARRAYSIZE(sig_words));
  hardened_bool_t verif_ok = kHardenedBoolFalse;
  TRY(otcrypto_ecdsa_p256_verify(&pub_key, msg_digest, &sig_in, &verif_ok));
  TRY_CHECK(verif_ok == kHardenedBoolTrue);

  // Flip a bit in s and verify signature is rejected.
  sig_words[kP256CoordWords] ^= 1u;
  otcrypto_const_word32_buf_t tampered_sig_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, sig_words, ARRAYSIZE(sig_words));
  verif_ok = kHardenedBoolTrue;
  TRY(otcrypto_ecdsa_p256_verify(&pub_key, msg_digest, &tampered_sig_in,
                                 &verif_ok));
  TRY_CHECK(verif_ok == kHardenedBoolFalse);

  // Zero signature (r = 0, s = 0) must be rejected (either via
  // OTCRYPTO_BAD_ARGS or verif_ok == kHardenedBoolFalse).
  memset(sig_words, 0, sizeof(sig_words));
  otcrypto_const_word32_buf_t zero_sig_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, sig_words, ARRAYSIZE(sig_words));
  verif_ok = kHardenedBoolTrue;
  otcrypto_status_t zero_status =
      otcrypto_ecdsa_p256_verify(&pub_key, msg_digest, &zero_sig_in, &verif_ok);
  TRY_CHECK(zero_status.value == OTCRYPTO_BAD_ARGS.value ||
            (zero_status.value == OTCRYPTO_OK.value &&
             verif_ok == kHardenedBoolFalse));

  // Android CTS `SignatureTest.java:114-119` (`SHORT_MSG_KAT_SIGNATURES` /
  // `testSmallMsgKat`): Verify the `SHA256withECDSA` P-256 KAT signature using
  // `R.raw.ec_key1_pkcs8` over the 23-byte message
  // `ec174729c4f5c570ba0de4c424cdcbf0362a7718039464`.
  static const uint32_t kCtsEcdsaSha256Sig[kP256PointWords] = {
      0xba8ce45d, 0x6144346f, 0x7d9166af, 0xf2ec7860, 0x0d9410fe, 0xe729155b,
      0xd888beea, 0x4443b560, 0x41819281, 0xc7c0e83b, 0xa6abbd3b, 0x14eb15f2,
      0xf46c614c, 0x1395c8bc, 0xa630050f, 0x5b0727bf,
  };

  uint32_t cts_ec_pub_buf[kP256PointWords];
  otcrypto_unblinded_key_t cts_ec_pub = {
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = sizeof(cts_ec_pub_buf),
      .key = cts_ec_pub_buf,
  };
  otcrypto_const_word32_buf_t cts_ec_x = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kCtsEcKey1X, kP256CoordWords);
  otcrypto_const_word32_buf_t cts_ec_y = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kCtsEcKey1Y, kP256CoordWords);
  TRY(otcrypto_ecc_p256_public_key_import(cts_ec_x, cts_ec_y, &cts_ec_pub));

  otcrypto_const_byte_buf_t cts_ecdsa_msg_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, kCtsEcdsaMsg, sizeof(kCtsEcdsaMsg));
  otcrypto_const_word32_buf_t cts_sha256_sig_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kCtsEcdsaSha256Sig, kP256PointWords);
  uint32_t cts_msg_digest_words[kSha256DigestWords];
  otcrypto_hash_digest_t cts_msg_digest = {
      .mode = kOtcryptoHashModeSha256,
      .data = cts_msg_digest_words,
      .len = ARRAYSIZE(cts_msg_digest_words),
  };
  TRY(otcrypto_sha2_256(&cts_ecdsa_msg_buf, &cts_msg_digest));
  verif_ok = kHardenedBoolFalse;
  TRY(otcrypto_ecdsa_p256_verify(&cts_ec_pub, cts_msg_digest,
                                 &cts_sha256_sig_in, &verif_ok));
  TRY_CHECK(verif_ok == kHardenedBoolTrue);

  // Android CTS `SignatureTest.java:242-248, 756`
  // (`LONG_MSG_KAT_SIGNATURES["SHA256withECDSA"]` / `testLongMsgKat`):
  // First verify on-device that `TestUtils.generateLargeKatMsg(kCtsEcdsaMsg)`
  // (`SHA-512` PRNG stream) produces `kCtsSigLongMsgPrefix32`, then verify the
  // `SHA256withECDSA` KAT signature over the `3 * 1024 * 1024 + 123`-byte
  // message digest `kCtsSigLongMsgSha256Digest`.
  uint32_t sha512_words[512 / 32];
  otcrypto_hash_digest_t sha512_digest = {
      .mode = kOtcryptoHashModeSha512,
      .data = sha512_words,
      .len = ARRAYSIZE(sha512_words),
  };
  TRY(otcrypto_sha2_512(&cts_ecdsa_msg_buf, &sha512_digest));
  TRY_CHECK_ARRAYS_EQ((const uint8_t *)sha512_words, kCtsSigLongMsgPrefix32,
                      sizeof(kCtsSigLongMsgPrefix32));

  static const uint32_t kCtsEcdsaLongMsgSha256Sig[kP256PointWords] = {
      0x53f9f21a, 0xfbbc7b2d, 0xd5026ac4, 0xf2f16395, 0x7718e3f2, 0x19b36e3c,
      0xc373e8da, 0x501946a2, 0x0f27eed1, 0x78969658, 0x39082784, 0x351228ea,
      0xb25ae92b, 0x08bacd5f, 0x685282f3, 0x347d7a46,
  };
  otcrypto_hash_digest_t long_msg_sha256_digest = {
      .mode = kOtcryptoHashModeSha256,
      .data = (uint32_t *)kCtsSigLongMsgSha256Digest,
      .len = ARRAYSIZE(kCtsSigLongMsgSha256Digest),
  };
  otcrypto_const_word32_buf_t cts_long_sha256_sig_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kCtsEcdsaLongMsgSha256Sig, kP256PointWords);
  verif_ok = kHardenedBoolFalse;
  TRY(otcrypto_ecdsa_p256_verify(&cts_ec_pub, long_msg_sha256_digest,
                                 &cts_long_sha256_sig_in, &verif_ok));
  TRY_CHECK(verif_ok == kHardenedBoolTrue);

  // Android CTS `ECDSASignatureTest.java:282` (`StrongboxECDSASignatureTest`,
  // `R.raw.ec_key4_secp256r1_pkcs8`) and KeyMint VTS `KeyMintTest.cpp:307`
  // (`ec_256_key`): Import both P-256 keypairs and verify ECDSA sign + verify.
  const struct {
    const uint32_t *d;
    const uint32_t *x;
    const uint32_t *y;
  } kImportedKeys[2] = {
      {kCtsEcKey4D, kCtsEcKey4X, kCtsEcKey4Y},
      {kVtsEcP256D, kVtsEcP256X, kVtsEcP256Y},
  };
  for (size_t k = 0; k < ARRAYSIZE(kImportedKeys); ++k) {
    uint32_t imp_share0[kP256MaskedScalarShareWords] = {0};
    uint32_t imp_share1[kP256MaskedScalarShareWords] = {0};
    memcpy(imp_share0, kImportedKeys[k].d, kP256CoordWords * sizeof(uint32_t));
    otcrypto_const_word32_buf_t s0_buf = OTCRYPTO_MAKE_BUF(
        otcrypto_const_word32_buf_t, imp_share0, kP256MaskedScalarShareWords);
    otcrypto_const_word32_buf_t s1_buf = OTCRYPTO_MAKE_BUF(
        otcrypto_const_word32_buf_t, imp_share1, kP256MaskedScalarShareWords);
    TRY(otcrypto_ecc_p256_private_key_import(s0_buf, s1_buf, &priv_key));

    otcrypto_const_word32_buf_t kx_buf = OTCRYPTO_MAKE_BUF(
        otcrypto_const_word32_buf_t, kImportedKeys[k].x, kP256CoordWords);
    otcrypto_const_word32_buf_t ky_buf = OTCRYPTO_MAKE_BUF(
        otcrypto_const_word32_buf_t, kImportedKeys[k].y, kP256CoordWords);
    TRY(otcrypto_ecc_p256_public_key_import(kx_buf, ky_buf, &pub_key));

    hardened_bool_t on_curve = kHardenedBoolFalse;
    TRY(otcrypto_ecc_p256_point_on_curve(&pub_key, &on_curve));
    TRY_CHECK(on_curve == kHardenedBoolTrue);

    TRY(otcrypto_ecdsa_p256_sign_verify(&priv_key, &pub_key, msg_digest,
                                        &sig_out));
    verif_ok = kHardenedBoolFalse;
    TRY(otcrypto_ecdsa_p256_verify(&pub_key, msg_digest, &sig_in, &verif_ok));
    TRY_CHECK(verif_ok == kHardenedBoolTrue);
  }

  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:3687` —
 *     `TEST_P(SigningOperationsTest, HmacAllDigests)` (`SHA_2_256` on
 *     StrongBox)
 *   - `KeyMintTest.cpp:3709` —
 *     `TEST_P(SigningOperationsTest, HmacMessageDigestUnique)`
 *   - `KeyMintTest.cpp:3746` —
 *     `TEST_P(SigningOperationsTest, HmacSha256TooLargeMacLength)`
 *   - `KeyMintTest.cpp:3786` —
 *     `TEST_P(SigningOperationsTest, HmacSha256TooSmallMacLength)`
 *   - `KeyMintTest.cpp:3805` —
 *     `TEST_P(SigningOperationsTest, HmacRfc4231TestCase3)` (`SHA_2_256` on
 *     StrongBox)
 *   - `MacTest.java:76, 94, 112-135, 273, 380-403, 640`
 *     (`StrongboxMacTest.java` `EXPECTED_ALGORITHMS_STRONGBOX =
 * {"HmacSHA256"}`)
 */
static status_t hmac_vts_test(void) {
  LOG_INFO(
      "Testing StrongBox KeyMint VTS & CTS HmacSHA256 (HmacAllDigests, "
      "StrongboxMacTest KATs, and HmacRfc4231TestCase3)");

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

  // `HmacSha256TooSmallMacLength` (`KeyMintTest.cpp:3786`): requesting a
  // < 64-bit (1-word / 4-byte) tag on HMAC-SHA256 must fail with
  // `OTCRYPTO_BAD_ARGS`.
  uint32_t too_small_tag[1] = {0};
  otcrypto_word32_buf_t too_small_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, too_small_tag, 1);
  TRY_CHECK(otcrypto_hmac(&hmac_key, &hmac_msg_buf, &too_small_buf).value ==
            OTCRYPTO_BAD_ARGS.value);

  // 2. `KeyMintTest.cpp:3805` (`SigningOperationsTest.HmacRfc4231TestCase3`):
  // 20-byte key `0xaa..aa`, 50-byte message `0xdd..dd` with StrongBox
  // `Digest::SHA_2_256` (`KeyMintTest.cpp:3832`).
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
  otcrypto_blinded_key_t tc3_key = {
      .config =
          {
              .version = otcrypto_lib_version(),
              .key_mode = kOtcryptoKeyModeHmacSha256,
              .key_length = 20,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = sizeof(rfc4231_tc3_keyblob),
      .keyblob = rfc4231_tc3_keyblob,
  };
  tc3_key.checksum = otcrypto_integrity_blinded_checksum(&tc3_key);
  uint32_t tc3_tag[8] = {0};
  otcrypto_word32_buf_t tc3_tag_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, tc3_tag, ARRAYSIZE(tc3_tag));
  TRY(otcrypto_hmac(&tc3_key, &tc3_msg_in, &tc3_tag_buf));
  TRY_CHECK_ARRAYS_EQ((const uint8_t *)tc3_tag, kExpectedTc3Sha256,
                      sizeof(kExpectedTc3Sha256));

  // 3. Android CTS `StrongboxMacTest.java` / `MacTest.java:76, 112-135,
  // 380-383`
  // (`SHORT_MSG_KAT_MACS["HmacSHA256"]` / `testSmallMsgKat`): 3 StrongBox
  // `HmacSHA256` KAT vectors (30B, 32B, and 33B keys) over the 9-byte message
  // `a16037e3c901c9a1ab`, tested in one-shot, 1-byte chunks, and 3-byte chunks.
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
  const struct {
    const uint8_t *key;
    size_t key_len;
    const uint8_t *expected_mac;
  } kCtsMacVectors[3] = {
      {kCtsSha256Key1, sizeof(kCtsSha256Key1), kCtsSha256Mac1},
      {kCtsSha256Key2, sizeof(kCtsSha256Key2), kCtsSha256Mac2},
      {kCtsSha256Key3, sizeof(kCtsSha256Key3), kCtsSha256Mac3},
  };
  for (size_t v = 0; v < ARRAYSIZE(kCtsMacVectors); ++v) {
    size_t share_words = ceil_div(kCtsMacVectors[v].key_len, sizeof(uint32_t));
    uint32_t cts_keyblob[18] = {0};
    memcpy(cts_keyblob, kCtsMacVectors[v].key, kCtsMacVectors[v].key_len);
    otcrypto_blinded_key_t cts_key = {
        .config =
            {
                .version = otcrypto_lib_version(),
                .key_mode = kOtcryptoKeyModeHmacSha256,
                .key_length = kCtsMacVectors[v].key_len,
                .hw_backed = kHardenedBoolFalse,
                .security_level = kOtcryptoKeySecurityLevelLow,
            },
        .keyblob_length = 2 * share_words * sizeof(uint32_t),
        .keyblob = cts_keyblob,
    };
    cts_key.checksum = otcrypto_integrity_blinded_checksum(&cts_key);
    uint32_t cts_tag[8] = {0};
    otcrypto_word32_buf_t cts_tag_buf =
        OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, cts_tag, ARRAYSIZE(cts_tag));

    // One-shot (`MacTest.verifyKatVector`, chunkSize = Integer.MAX_VALUE):
    TRY(otcrypto_hmac(&cts_key, &cts_mac_msg_in, &cts_tag_buf));
    TRY_CHECK_ARRAYS_EQ((const uint8_t *)cts_tag,
                        kCtsMacVectors[v].expected_mac, sizeof(cts_tag));

    // Streaming in 1-byte and 3-byte chunks (`MacTest.java:380-383`):
    const size_t kChunkSizes[2] = {1, 3};
    for (size_t c = 0; c < ARRAYSIZE(kChunkSizes); ++c) {
      size_t chunk_sz = kChunkSizes[c];
      TRY(otcrypto_hmac_init(&hmac_ctx, &cts_key));
      for (size_t off = 0; off < sizeof(kCtsMacMsg); off += chunk_sz) {
        size_t n = sizeof(kCtsMacMsg) - off < chunk_sz
                       ? sizeof(kCtsMacMsg) - off
                       : chunk_sz;
        otcrypto_const_byte_buf_t chunk_in =
            OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kCtsMacMsg + off, n);
        TRY(otcrypto_hmac_update(&hmac_ctx, &chunk_in));
      }
      memset(cts_tag, 0, sizeof(cts_tag));
      TRY(otcrypto_hmac_final(&hmac_ctx, &cts_tag_buf));
      TRY_CHECK_ARRAYS_EQ((const uint8_t *)cts_tag,
                          kCtsMacVectors[v].expected_mac, sizeof(cts_tag));
    }
  }

  // 4. Android CTS `StrongboxMacTest.java` / `MacTest.java:94, 273, 403, 640`
  // (`KAT_KEY` / `getDefaultKatKey("HmacSHA256")`,
  // `testMacGeneratedForEmptyMessage`, and `testLongMsgKat`):
  // `MacTest.java:640` `getDefaultKatKey` uses the full 64-byte `KAT_KEY` for
  // HMAC keys. Verify:
  //   - 0-byte empty message (`testMacGeneratedForEmptyMessage`, L273)
  //   - 9-byte `kCtsMacMsg` with full 64-byte `KAT_KEY`
  //   - Streaming `TestUtils.generateLargeKatMsg(kCtsMacMsg, 1024 + 149)`
  static const uint8_t kCtsHmacDefaultKatKey[64] = {
      0x22, 0x7b, 0x21, 0x2b, 0xeb, 0xd7, 0x75, 0x49, 0x39, 0x29, 0xef,
      0x62, 0x67, 0x29, 0xa5, 0x87, 0xd3, 0xf8, 0x1b, 0x8e, 0x18, 0xa3,
      0xed, 0x48, 0x2d, 0x40, 0x39, 0x10, 0xe1, 0x84, 0x47, 0x9b, 0x44,
      0x8c, 0xfa, 0x79, 0xb6, 0x2b, 0xd9, 0x05, 0x95, 0xef, 0xdd, 0x15,
      0xf8, 0x7b, 0xd7, 0xb2, 0xd2, 0xda, 0xc4, 0x80, 0xc6, 0x1e, 0x96,
      0x9b, 0xa9, 0x0a, 0x7b, 0x8c, 0xea, 0xdd, 0x32, 0x84,
  };
  static const uint8_t kCtsHmacFull64BKeyEmptyMsgMac[32] = {
      0x9d, 0xbc, 0x88, 0xec, 0x69, 0x83, 0xd8, 0x6f, 0x57, 0x64, 0xbb,
      0xa1, 0x36, 0x91, 0x65, 0x5b, 0x1c, 0x27, 0x8e, 0x11, 0x08, 0xa2,
      0x8c, 0x30, 0x97, 0xab, 0x48, 0x9f, 0xef, 0x7c, 0xc0, 0x07,
  };
  static const uint8_t kCtsHmacFull64BKeyShortMsgMac[32] = {
      0x17, 0xfe, 0xed, 0x3d, 0xe0, 0xb2, 0xd5, 0x3b, 0x69, 0xb2, 0x28,
      0xc2, 0xd9, 0xd2, 0x6e, 0x9d, 0x57, 0xb3, 0x14, 0xc5, 0x0d, 0x36,
      0x66, 0x25, 0x96, 0x77, 0x7f, 0x49, 0x44, 0x5d, 0xf7, 0x29,
  };
  static const uint8_t kCtsHmacFull64BKeyStream1173BMac[32] = {
      0x19, 0x67, 0x1a, 0x1a, 0x04, 0x8b, 0xc7, 0xd1, 0x24, 0xbb, 0x6c,
      0xe9, 0xb3, 0x3d, 0x63, 0x64, 0xac, 0x6f, 0x3b, 0x3a, 0x1e, 0xa1,
      0x13, 0x75, 0x05, 0x41, 0x0f, 0xe8, 0x7c, 0xd7, 0x9a, 0x32,
  };

  uint32_t cts_def64_keyblob[32] = {0};
  memcpy(cts_def64_keyblob, kCtsHmacDefaultKatKey,
         sizeof(kCtsHmacDefaultKatKey));
  otcrypto_blinded_key_t cts_def64_key = {
      .config =
          {
              .version = otcrypto_lib_version(),
              .key_mode = kOtcryptoKeyModeHmacSha256,
              .key_length = sizeof(kCtsHmacDefaultKatKey),
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = sizeof(cts_def64_keyblob),
      .keyblob = cts_def64_keyblob,
  };
  cts_def64_key.checksum = otcrypto_integrity_blinded_checksum(&cts_def64_key);
  uint32_t cts_def_tag[8] = {0};
  otcrypto_word32_buf_t cts_def_tag_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, cts_def_tag, ARRAYSIZE(cts_def_tag));

  // `MacTest.testMacGeneratedForEmptyMessage` (`MacTest.java:273`): 0-byte
  // message one-shot and streaming `init` + `final`.
  otcrypto_const_byte_buf_t empty_msg_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 0);
  TRY(otcrypto_hmac(&cts_def64_key, &empty_msg_in, &cts_def_tag_buf));
  TRY_CHECK_ARRAYS_EQ((const uint8_t *)cts_def_tag,
                      kCtsHmacFull64BKeyEmptyMsgMac, sizeof(cts_def_tag));
  memset(cts_def_tag, 0, sizeof(cts_def_tag));
  TRY(otcrypto_hmac_init(&hmac_ctx, &cts_def64_key));
  TRY(otcrypto_hmac_final(&hmac_ctx, &cts_def_tag_buf));
  TRY_CHECK_ARRAYS_EQ((const uint8_t *)cts_def_tag,
                      kCtsHmacFull64BKeyEmptyMsgMac, sizeof(cts_def_tag));

  // 9-byte `kCtsMacMsg` with 64-byte `KAT_KEY`:
  TRY(otcrypto_hmac(&cts_def64_key, &cts_mac_msg_in, &cts_def_tag_buf));
  TRY_CHECK_ARRAYS_EQ((const uint8_t *)cts_def_tag,
                      kCtsHmacFull64BKeyShortMsgMac, sizeof(cts_def_tag));

  // Streaming `TestUtils.generateLargeKatMsg(kCtsMacMsg, 1024 + 149)`:
  TRY(otcrypto_hmac_init(&hmac_ctx, &cts_def64_key));
  uint32_t prng_seed_words[512 / 32];
  otcrypto_hash_digest_t prng_digest = {
      .mode = kOtcryptoHashModeSha512,
      .data = prng_seed_words,
      .len = ARRAYSIZE(prng_seed_words),
  };
  size_t remaining = 1024 + 149;
  bool first_chunk = true;
  while (remaining > 0) {
    if (first_chunk) {
      TRY(otcrypto_sha2_512(&cts_mac_msg_in, &prng_digest));
      first_chunk = false;
    } else {
      otcrypto_const_byte_buf_t prev_seed = OTCRYPTO_MAKE_BUF(
          otcrypto_const_byte_buf_t, (const uint8_t *)prng_seed_words,
          sizeof(prng_seed_words));
      TRY(otcrypto_sha2_512(&prev_seed, &prng_digest));
    }
    size_t chunk_len = remaining < sizeof(prng_seed_words)
                           ? remaining
                           : sizeof(prng_seed_words);
    otcrypto_const_byte_buf_t chunk_in = OTCRYPTO_MAKE_BUF(
        otcrypto_const_byte_buf_t, (const uint8_t *)prng_seed_words, chunk_len);
    TRY(otcrypto_hmac_update(&hmac_ctx, &chunk_in));
    remaining -= chunk_len;
  }
  TRY(otcrypto_hmac_final(&hmac_ctx, &cts_def_tag_buf));
  TRY_CHECK_ARRAYS_EQ((const uint8_t *)cts_def_tag,
                      kCtsHmacFull64BKeyStream1173BMac, sizeof(cts_def_tag));

  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:3844` —
 *     `TEST_P(SigningOperationsTest, HmacRfc4231TestCase5)` (`SHA_2_256` on
 *     StrongBox)
 *
 * 20-byte key `0x0c..0c`, message `"Test With Truncation"` (20B), expecting
 * 128-bit (16-byte / 4-word) truncated HMAC-SHA256 tag on StrongBox
 * (`KeyMintTest.cpp:3866`).
 */
static status_t hmac_rfc4231_truncated_tag_vts_test(void) {
  LOG_INFO(
      "Testing KeyMint VTS SigningOperationsTest.HmacRfc4231TestCase5 "
      "(128-bit truncated HMAC-SHA256 tag)");
  uint32_t rfc4231_tc5_keyblob[10] = {0};
  memset(rfc4231_tc5_keyblob, 0x0c, 20);
  const uint8_t kTc5Msg[20] = "Test With Truncation";
  otcrypto_const_byte_buf_t tc5_msg_in =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, kTc5Msg, sizeof(kTc5Msg));
  const uint8_t kExpectedTc5Sha256Trunc[16] = {
      0xa3, 0xb6, 0x16, 0x74, 0x73, 0x10, 0x0e, 0xe0,
      0x6e, 0x0c, 0x79, 0x6c, 0x29, 0x55, 0x55, 0x2b,
  };
  otcrypto_blinded_key_t tc5_key = {
      .config =
          {
              .version = otcrypto_lib_version(),
              .key_mode = kOtcryptoKeyModeHmacSha256,
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
  TRY(otcrypto_hmac(&tc5_key, &tc5_msg_in, &tc5_trunc_buf));
  TRY_CHECK_ARRAYS_EQ((const uint8_t *)tc5_trunc_tag, kExpectedTc5Sha256Trunc,
                      sizeof(kExpectedTc5Sha256Trunc));
  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:8614` — `TEST_P(KeyAgreementTest, Ecdh)`
 *     (`ValidCurves()` on StrongBox is `{EcCurve::P_256}`)
 */
static status_t ecdh_p256_vts_test(void) {
  LOG_INFO("Testing StrongBox P-256 ECDH key agreement");

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
              .key_mode = kOtcryptoKeyModeHmacSha256,
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

  // Android CTS `KeyAgreementTest.java:121`
  // (`StrongboxKeyAgreementTest.testGenerateSecret_withImportedKey`) and
  // KeyMint VTS `KeyMintTest.cpp:307, 8614` (`KeyAgreementTest.Ecdh` with
  // imported P-256 keys `kCtsEcKey4` and `kVtsEcP256`):
  static const uint32_t kExpectedImportedEcdhSharedPoint[kP256PointWords] = {
      // Shared X:
      0x8e72908d,
      0x8b039518,
      0x7b8f1a01,
      0xbf0864e0,
      0x2aa603f8,
      0x475aefb6,
      0xa5f623bf,
      0xc374da82,
      // Shared Y:
      0xd7b77b3e,
      0xb18e8864,
      0xa451924d,
      0xe604c11a,
      0x6aeb741d,
      0xbae8e179,
      0x9743a353,
      0xe877abf2,
  };
  uint32_t ec4_share0[kP256MaskedScalarShareWords] = {0};
  uint32_t vts_share0[kP256MaskedScalarShareWords] = {0};
  uint32_t zero_share1[kP256MaskedScalarShareWords] = {0};
  memcpy(ec4_share0, kCtsEcKey4D, sizeof(kCtsEcKey4D));
  memcpy(vts_share0, kVtsEcP256D, sizeof(kVtsEcP256D));
  otcrypto_const_word32_buf_t ec4_s0_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, ec4_share0, kP256MaskedScalarShareWords);
  otcrypto_const_word32_buf_t vts_s0_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, vts_share0, kP256MaskedScalarShareWords);
  otcrypto_const_word32_buf_t z_s1_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, zero_share1, kP256MaskedScalarShareWords);
  TRY(otcrypto_ecc_p256_private_key_import(ec4_s0_buf, z_s1_buf, &alice_priv));
  TRY(otcrypto_ecc_p256_private_key_import(vts_s0_buf, z_s1_buf, &bob_priv));

  otcrypto_const_word32_buf_t ec4_x_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kCtsEcKey4X, kP256CoordWords);
  otcrypto_const_word32_buf_t ec4_y_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kCtsEcKey4Y, kP256CoordWords);
  otcrypto_const_word32_buf_t vts_x_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kVtsEcP256X, kP256CoordWords);
  otcrypto_const_word32_buf_t vts_y_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kVtsEcP256Y, kP256CoordWords);
  TRY(otcrypto_ecc_p256_public_key_import(ec4_x_buf, ec4_y_buf, &alice_pub));
  TRY(otcrypto_ecc_p256_public_key_import(vts_x_buf, vts_y_buf, &bob_pub));

  TRY(otcrypto_ecdh_p256(&alice_priv, &bob_pub, &ss_alice));
  TRY(otcrypto_ecdh_p256(&bob_priv, &alice_pub, &ss_bob));
  for (size_t i = 0; i < kP256PointWords; ++i) {
    ss_a_unmasked[i] = ss_alice_blob[i] ^ ss_alice_blob[kP256PointWords + i];
    ss_b_unmasked[i] = ss_bob_blob[i] ^ ss_bob_blob[kP256PointWords + i];
  }
  TRY_CHECK_ARRAYS_EQ(ss_a_unmasked, kExpectedImportedEcdhSharedPoint,
                      kP256PointWords);
  TRY_CHECK_ARRAYS_EQ(ss_b_unmasked, kExpectedImportedEcdhSharedPoint,
                      kP256PointWords);

  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:3422` —
 *     `TEST_P(SigningOperationsTest, EcdsaAllDigestsAndCurves)`
 *     (StrongBox `ValidCurves()` = `{EcCurve::P_256}`,
 *      `ValidDigests(true, false)` = `{Digest::NONE, Digest::SHA_2_256}`)
 *   - `KeyMintTest.cpp:3580` —
 *     `TEST_P(SigningOperationsTest, EcdsaNoDigestHugeData)`
 *   - `SignatureTest.java:103-107` (`NONEwithECDSA` short-message KAT)
 *   - `SignatureTest.java:236-241, 756` (`NONEwithECDSA` long-message KAT)
 *   - `ECDSASignatureTest.java:69`
 *     (`testNONEwithECDSATruncatesInputToFieldSize`, 96B -> 32B)
 *   - `ECDSASignatureTest.java:120`
 *     (`testNONEwithECDSASupportsMessagesShorterThanFieldSize`, 24B -> 32B)
 *   - `ECDSASignatureTest.java:142` (`testECDSANonceReuse`)
 *   - `ECDSASignatureTest.java:155` (`testBoringSslKat`, 50B -> 32B)
 */
static status_t ecdsa_all_digests_and_curves_vts_test(void) {
  LOG_INFO(
      "Testing StrongBox KeyMint VTS EcdsaAllDigestsAndCurves & CTS "
      "ECDSASignatureTest (P-256 with SHA-256 and Digest::NONE / "
      "NONEwithECDSA)");
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
  uint32_t msg_digest_words[kSha256DigestWords];
  otcrypto_hash_digest_t msg_digest = {
      .mode = kOtcryptoHashModeSha256,
      .data = msg_digest_words,
      .len = ARRAYSIZE(msg_digest_words),
  };
  TRY(otcrypto_sha2_256(&msg_in, &msg_digest));

  uint32_t ecdsa_sig[kP256PointWords];
  otcrypto_word32_buf_t ecdsa_sig_out =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, ecdsa_sig, ARRAYSIZE(ecdsa_sig));
  TRY(otcrypto_ecdsa_p256_sign_verify(&priv, &pub, msg_digest, &ecdsa_sig_out));

  // `ECDSASignatureTest.testECDSANonceReuse` (`ECDSASignatureTest.java:142`):
  // Signing the same message twice must produce distinct `(r, s)` signatures,
  // and both signatures must verify as valid.
  uint32_t ecdsa_sig2[kP256PointWords];
  otcrypto_word32_buf_t ecdsa_sig2_out = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, ecdsa_sig2, ARRAYSIZE(ecdsa_sig2));
  TRY(otcrypto_ecdsa_p256_sign_verify(&priv, &pub, msg_digest,
                                      &ecdsa_sig2_out));
  TRY_CHECK(memcmp(ecdsa_sig, ecdsa_sig2, sizeof(ecdsa_sig)) != 0);

  // 1. Android CTS `SignatureTest.java:103-107` (`NONEwithECDSA` short-message
  // KAT over 23-byte `kCtsEcdsaMsg`) and `SignatureTest.java:236-241, 756`
  // (`NONEwithECDSA` long-message KAT over `kCtsSigLongMsgPrefix32`):
  static const uint32_t kCtsEcdsaNoneSig[kP256PointWords] = {
      0xd28b5889, 0x834cfc20, 0x64e400a5, 0xf359b606, 0xec658ee7, 0x39d103bf,
      0xb5719916, 0x1ea57c2f, 0x0aebc967, 0x00e2efd5, 0xfcae2c3b, 0xd0913a6c,
      0x256ea399, 0xf8d238ea, 0x07d2b03b, 0x2433f5eb,
  };
  static const uint32_t kCtsEcdsaLongMsgNoneSig[kP256PointWords] = {
      0x0e3cd58b, 0xa13f4901, 0xe8089685, 0x30f51d1c, 0x3e2af7f5, 0x8821eeca,
      0x8a66ce11, 0x6e403960, 0x21cb3193, 0x36524742, 0x6e024878, 0x3d6b6333,
      0x12128a22, 0xd775fad7, 0xa171f1b1, 0x83a5fe62,
  };
  uint32_t cts_ec_pub_buf[kP256PointWords];
  otcrypto_unblinded_key_t cts_ec_pub = {
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = sizeof(cts_ec_pub_buf),
      .key = cts_ec_pub_buf,
  };
  otcrypto_const_word32_buf_t cts_ec_x = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kCtsEcKey1X, kP256CoordWords);
  otcrypto_const_word32_buf_t cts_ec_y = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kCtsEcKey1Y, kP256CoordWords);
  TRY(otcrypto_ecc_p256_public_key_import(cts_ec_x, cts_ec_y, &cts_ec_pub));

  // For `NONEwithECDSA` on a message shorter than 32 bytes (23B), FIPS 186-4 /
  // BoringSSL interprets the message as a 184-bit big-endian integer, which is
  // equivalent to left-padding with 9 leading `0x00` bytes into a 32-byte
  // (`kP256CoordWords`-word) digest buffer (`p256_ecdsa_verify_start` reverses
  // the 32 bytes to form the little-endian scalar z).
  uint32_t cts_none_words[kP256CoordWords] = {0};
  memcpy((uint8_t *)cts_none_words +
             (sizeof(cts_none_words) - sizeof(kCtsEcdsaMsg)),
         kCtsEcdsaMsg, sizeof(kCtsEcdsaMsg));
  uint32_t cts_long_none_words[kP256CoordWords] = {0};
  memcpy(cts_long_none_words, kCtsSigLongMsgPrefix32,
         sizeof(kCtsSigLongMsgPrefix32));

  otcrypto_const_word32_buf_t cts_none_sig_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kCtsEcdsaNoneSig, kP256PointWords);
  otcrypto_const_word32_buf_t cts_long_none_sig_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kCtsEcdsaLongMsgNoneSig, kP256PointWords);

  // Verify both `NONEwithECDSA` KAT signatures using `kOtcryptoHashModeNull`
  // (`Digest::NONE`).
  hardened_bool_t verif_ok = kHardenedBoolFalse;
  otcrypto_hash_digest_t cts_none_digest = {
      .mode = kOtcryptoHashModeNull,
      .data = cts_none_words,
      .len = ARRAYSIZE(cts_none_words),
  };
  TRY(otcrypto_ecdsa_p256_verify(&cts_ec_pub, cts_none_digest, &cts_none_sig_in,
                                 &verif_ok));
  TRY_CHECK(verif_ok == kHardenedBoolTrue);

  verif_ok = kHardenedBoolFalse;
  otcrypto_hash_digest_t cts_long_none_digest = {
      .mode = kOtcryptoHashModeNull,
      .data = cts_long_none_words,
      .len = ARRAYSIZE(cts_long_none_words),
  };
  TRY(otcrypto_ecdsa_p256_verify(&cts_ec_pub, cts_long_none_digest,
                                 &cts_long_none_sig_in, &verif_ok));
  TRY_CHECK(verif_ok == kHardenedBoolTrue);

  // 2. KeyMint VTS `EcdsaAllDigestsAndCurves` (`Digest::NONE`, 32B),
  // `EcdsaNoDigestHugeData` (`Digest::NONE`, >32B left-truncated to 32B), &
  // `ECDSASignatureTest.java:155` (`testBoringSslKat`, 50B left-truncated to
  // 32B):
  static const uint8_t kCtsBoringSslKat50BMsg[50] = {
      0x99, 0x86, 0x62, 0x9b, 0x05, 0x10, 0x1a, 0x71, 0x69, 0x65,
      0x68, 0x26, 0x93, 0x45, 0x7a, 0x41, 0x80, 0x3b, 0x38, 0x4b,
      0x03, 0x16, 0x04, 0x38, 0x99, 0x89, 0x0e, 0x3e, 0x3e, 0x42,
      0x34, 0x80, 0x31, 0x3e, 0x68, 0x04, 0x29, 0x9e, 0x6e, 0x4c,
      0x79, 0x23, 0x7e, 0x77, 0x20, 0x2b, 0x3b, 0x39, 0x6c, 0x0c,
  };
  uint32_t raw_32b_words[kP256CoordWords];
  memcpy(raw_32b_words, kCtsBoringSslKat50BMsg, sizeof(raw_32b_words));
  otcrypto_hash_digest_t raw_32b_digest = {
      .mode = kOtcryptoHashModeNull,
      .data = raw_32b_words,
      .len = ARRAYSIZE(raw_32b_words),
  };
  TRY(otcrypto_ecdsa_p256_sign_verify(&priv, &pub, raw_32b_digest,
                                      &ecdsa_sig_out));
  otcrypto_const_word32_buf_t ecdsa_sig_in = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, ecdsa_sig, ARRAYSIZE(ecdsa_sig));
  verif_ok = kHardenedBoolFalse;
  TRY(otcrypto_ecdsa_p256_verify(&pub, raw_32b_digest, &ecdsa_sig_in,
                                 &verif_ok));
  TRY_CHECK(verif_ok == kHardenedBoolTrue);

  // 3. `ECDSASignatureTest.testNONEwithECDSATruncatesInputToFieldSize`
  // (`ECDSASignatureTest.java:69`): 96-byte message `{1..96}` truncated to
  // first 32 bytes `{1..32}`. Verify signature matches 32-byte prefix and
  // fails if byte 0 of the 32-byte prefix is modified.
  uint8_t msg_96b[96];
  for (size_t i = 0; i < sizeof(msg_96b); ++i) {
    msg_96b[i] = (uint8_t)(i + 1);
  }
  uint32_t trunc_32b_words[kP256CoordWords];
  memcpy(trunc_32b_words, msg_96b, sizeof(trunc_32b_words));
  otcrypto_hash_digest_t trunc_32b_digest = {
      .mode = kOtcryptoHashModeNull,
      .data = trunc_32b_words,
      .len = ARRAYSIZE(trunc_32b_words),
  };
  TRY(otcrypto_ecdsa_p256_sign_verify(&priv, &pub, trunc_32b_digest,
                                      &ecdsa_sig_out));
  verif_ok = kHardenedBoolFalse;
  TRY(otcrypto_ecdsa_p256_verify(&pub, trunc_32b_digest, &ecdsa_sig_in,
                                 &verif_ok));
  TRY_CHECK(verif_ok == kHardenedBoolTrue);
  trunc_32b_words[0] ^= 1u;
  verif_ok = kHardenedBoolTrue;
  TRY(otcrypto_ecdsa_p256_verify(&pub, trunc_32b_digest, &ecdsa_sig_in,
                                 &verif_ok));
  TRY_CHECK(verif_ok == kHardenedBoolFalse);

  // 4.
  // `ECDSASignatureTest.testNONEwithECDSASupportsMessagesShorterThanFieldSize`
  // (`ECDSASignatureTest.java:120`): 24-byte message `{1..24}` left-padded with
  // 8 leading `0x00` bytes into 32 bytes.
  uint8_t msg_24b[24];
  for (size_t i = 0; i < sizeof(msg_24b); ++i) {
    msg_24b[i] = (uint8_t)(i + 1);
  }
  uint32_t short_24b_words[kP256CoordWords] = {0};
  memcpy(
      (uint8_t *)short_24b_words + (sizeof(short_24b_words) - sizeof(msg_24b)),
      msg_24b, sizeof(msg_24b));
  otcrypto_hash_digest_t short_24b_digest = {
      .mode = kOtcryptoHashModeNull,
      .data = short_24b_words,
      .len = ARRAYSIZE(short_24b_words),
  };
  TRY(otcrypto_ecdsa_p256_sign_verify(&priv, &pub, short_24b_digest,
                                      &ecdsa_sig_out));
  verif_ok = kHardenedBoolFalse;
  TRY(otcrypto_ecdsa_p256_verify(&pub, short_24b_digest, &ecdsa_sig_in,
                                 &verif_ok));
  TRY_CHECK(verif_ok == kHardenedBoolTrue);

  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:3422` —
 *     `TEST_P(SigningOperationsTest, EcdsaAllDigestsAndCurves)`
 * (`Digest::NONE`)
 *   - `SignatureTest.java:103-107` (`NONEwithECDSA` over raw 23-byte
 *     `kCtsEcdsaMsg`)
 *
 * Exercises `otcrypto_ecdsa_p256_sign_verify` with `kOtcryptoHashModeNull`
 * after right-aligning the 23-byte `kCtsEcdsaMsg` into a 32-byte digest buffer.
 */
static status_t ecdsa_p256_hash_null_mode_test(void) {
  LOG_INFO(
      "Testing otcrypto_ecdsa_p256_sign_verify with kOtcryptoHashModeNull "
      "(23B kCtsEcdsaMsg)");
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

  uint32_t padded_words[kP256CoordWords] = {0};
  memcpy(
      (uint8_t *)padded_words + (sizeof(padded_words) - sizeof(kCtsEcdsaMsg)),
      kCtsEcdsaMsg, sizeof(kCtsEcdsaMsg));
  otcrypto_hash_digest_t null_digest = {
      .mode = kOtcryptoHashModeNull,
      .data = padded_words,
      .len = ARRAYSIZE(padded_words),
  };
  uint32_t sig[kP256PointWords];
  otcrypto_word32_buf_t sig_out =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig, ARRAYSIZE(sig));
  TRY(otcrypto_ecdsa_p256_sign_verify(&priv, &pub, null_digest, &sig_out));
  return OK_STATUS();
}

/**
 * Source:
 *   - `KeyMintTest.cpp:8614` — `TEST_P(KeyAgreementTest, Ecdh)`
 *
 * Verifies 32-byte (`x`-coordinate only) ECDH P-256 shared secret output and
 * checks that both parties derive the same unmasked 32-byte secret.
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

  uint32_t ss_alice_blob[2 * kP256CoordWords];
  uint32_t ss_bob_blob[2 * kP256CoordWords];
  otcrypto_blinded_key_t ss_alice = {
      .config =
          {
              .version = otcrypto_lib_version(),
              .key_mode = kOtcryptoKeyModeAesCtr,
              .key_length = 32,
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

  uint32_t ss_a_unmasked[kP256CoordWords];
  uint32_t ss_b_unmasked[kP256CoordWords];
  for (size_t i = 0; i < kP256CoordWords; ++i) {
    ss_a_unmasked[i] = ss_alice_blob[i] ^ ss_alice_blob[kP256CoordWords + i];
    ss_b_unmasked[i] = ss_bob_blob[i] ^ ss_bob_blob[kP256CoordWords + i];
  }
  TRY_CHECK_ARRAYS_EQ(ss_a_unmasked, ss_b_unmasked, kP256CoordWords);

  // Imported-key KAT (`kCtsEcKey4` and `kVtsEcP256`) with 32-byte shared secret
  // fed into `otcrypto_hkdf` via per-share byte reversal (never unmasking x_S
  // in software):
  //   reverse_bytes(share0) ^ reverse_bytes(share1) = reverse_bytes(x_S) = Z.
  uint32_t ec4_share0[kP256MaskedScalarShareWords] = {0};
  uint32_t zero_share1[kP256MaskedScalarShareWords] = {0};
  memcpy(ec4_share0, kCtsEcKey4D, sizeof(kCtsEcKey4D));
  otcrypto_const_word32_buf_t ec4_s0_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, ec4_share0, kP256MaskedScalarShareWords);
  otcrypto_const_word32_buf_t z_s1_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, zero_share1, kP256MaskedScalarShareWords);
  TRY(otcrypto_ecc_p256_private_key_import(ec4_s0_buf, z_s1_buf, &alice_priv));

  otcrypto_const_word32_buf_t vts_x_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kVtsEcP256X, kP256CoordWords);
  otcrypto_const_word32_buf_t vts_y_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, kVtsEcP256Y, kP256CoordWords);
  TRY(otcrypto_ecc_p256_public_key_import(vts_x_buf, vts_y_buf, &bob_pub));

  ss_alice.config.key_mode = kOtcryptoKeyModeHmacSha256;
  ss_alice.config.exportable = kHardenedBoolTrue;
  TRY(otcrypto_ecdh_p256(&alice_priv, &bob_pub, &ss_alice));

  uint32_t share0_le[kP256CoordWords];
  uint32_t share1_le[kP256CoordWords];
  otcrypto_word32_buf_t share0_le_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, share0_le, kP256CoordWords);
  otcrypto_word32_buf_t share1_le_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, share1_le, kP256CoordWords);
  TRY(otcrypto_export_blinded_key(&ss_alice, &share0_le_buf, &share1_le_buf));

  // Reverse each share independently to convert from OTBN's little-endian word
  // order to the standard big-endian byte string Z = FE2OSP(x_S) without ever
  // unmasking the shared secret.
  uint32_t share0_be[kP256CoordWords];
  uint32_t share1_be[kP256CoordWords];
  for (size_t i = 0; i < kP256CoordWords; ++i) {
    share0_be[i] = __builtin_bswap32(share0_le[kP256CoordWords - 1 - i]);
    share1_be[i] = __builtin_bswap32(share1_le[kP256CoordWords - 1 - i]);
  }

  uint32_t hkdf_ikm_blob[2 * kP256CoordWords];
  otcrypto_blinded_key_t hkdf_ikm = {
      .config =
          {
              .version = otcrypto_lib_version(),
              .key_mode = kOtcryptoKeyModeHmacSha256,
              .key_length = 32,
              .hw_backed = kHardenedBoolFalse,
              .exportable = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = sizeof(hkdf_ikm_blob),
      .keyblob = hkdf_ikm_blob,
  };
  otcrypto_const_word32_buf_t share0_be_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, share0_be, kP256CoordWords);
  otcrypto_const_word32_buf_t share1_be_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, share1_be, kP256CoordWords);
  TRY(otcrypto_import_blinded_key(&share0_be_buf, &share1_be_buf, &hkdf_ikm));

  static const uint8_t kHkdfSalt[] = {
      0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06,
      0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c,
  };
  static const uint8_t kHkdfInfo[] = {
      0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9,
  };
  // Expected HKDF-SHA256(ikm = Z, salt = kHkdfSalt, info = kHkdfInfo) over the
  // 32-byte big-endian shared secret
  // Z = c374da82a5f623bf475aefb62aa603f8bf0864e07b8f1a018b0395188e72908d.
  static const uint32_t kExpectedHkdfOkm[kP256CoordWords] = {
      0x3bbaccc5, 0x882b002e, 0xf6b1b214, 0x836d6e88,
      0xae4406fa, 0x0491fea7, 0xa2996032, 0x1eea1559,
  };

  otcrypto_const_byte_buf_t salt_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, kHkdfSalt, sizeof(kHkdfSalt));
  otcrypto_const_byte_buf_t info_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, kHkdfInfo, sizeof(kHkdfInfo));

  uint32_t okm_blob[2 * kP256CoordWords];
  otcrypto_blinded_key_t okm = {
      .config =
          {
              .version = otcrypto_lib_version(),
              .key_mode = kOtcryptoKeyModeAesCtr,
              .key_length = 32,
              .hw_backed = kHardenedBoolFalse,
              .exportable = kHardenedBoolTrue,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = sizeof(okm_blob),
      .keyblob = okm_blob,
  };
  TRY(otcrypto_hkdf(&hkdf_ikm, &salt_buf, &info_buf, &okm));

  uint32_t okm_s0[kP256CoordWords];
  uint32_t okm_s1[kP256CoordWords];
  otcrypto_word32_buf_t okm_s0_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, okm_s0, kP256CoordWords);
  otcrypto_word32_buf_t okm_s1_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, okm_s1, kP256CoordWords);
  TRY(otcrypto_export_blinded_key(&okm, &okm_s0_buf, &okm_s1_buf));

  uint32_t actual_okm[kP256CoordWords];
  for (size_t i = 0; i < kP256CoordWords; ++i) {
    actual_okm[i] = okm_s0[i] ^ okm_s1[i];
  }
  TRY_CHECK_ARRAYS_EQ(actual_okm, kExpectedHkdfOkm, kP256CoordWords);

  return OK_STATUS();
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t result = OK_STATUS();
  otcrypto_state_t state = {0};
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow, &state));

  EXECUTE_TEST(result, ecc_p256_point_on_curve_test);
  EXECUTE_TEST(result, ecdsa_p256_sign_verify_and_invalid_sig_test);
  EXECUTE_TEST(result, hmac_vts_test);
  EXECUTE_TEST(result, ecdh_p256_vts_test);
  EXECUTE_TEST(result, ecdsa_all_digests_and_curves_vts_test);
  EXECUTE_TEST(result, hmac_rfc4231_truncated_tag_vts_test);
  EXECUTE_TEST(result, ecdsa_p256_hash_null_mode_test);
  EXECUTE_TEST(result, ecdh_p256_32b_shared_secret_vts_test);

  return status_ok(result);
}
