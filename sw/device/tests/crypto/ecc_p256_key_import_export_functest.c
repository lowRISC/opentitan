// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/ecc/p256.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/ecc_p256.h"
#include "sw/device/lib/crypto/include/entropy_src.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

enum {
  /* Number of 32-bit words in a P-256 public key (x and y coordinates). */
  kP256PublicKeyWords = 2 * kP256CoordWords,
  /* Number of bytes in a P-256 private key. */
  kP256PrivateKeyBytes = 256 / 8,
  /* Number of 32-bit words in a P-256 message digest. */
  kP256DigestWords = 256 / 32,
  /* Number of 32-bit words in a P-256 ECDSA signature. */
  kP256SignatureWords = 512 / 32,
};

static const otcrypto_key_config_t kPrivateKeyConfig = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeEcdsaP256,
    .key_length = kP256PrivateKeyBytes,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

static const char kMessage[] = "test message for public key import";

/**
 * Generate a P-256 keypair, re-import both the private key shares and the
 * public key coordinates, then sign with the imported private key and verify
 * with the imported public key.
 *
 * This tests otcrypto_ecc_p256_private_key_import,
 * otcrypto_ecc_p256_private_key_export, otcrypto_ecc_p256_public_key_import,
 * and otcrypto_ecc_p256_public_key_export together: a valid signature can only
 * be produced and verified if both imports round-tripped the key material
 * correctly, and both exports are verified against the original raw values.
 */
static status_t import_then_verify_test(void) {
  // Allocate space for the generated private key.
  uint32_t keyblob[kP256MaskedScalarTotalShareWords];
  otcrypto_blinded_key_t private_key = {
      .config = kPrivateKeyConfig,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };

  // Allocate space for the generated public key.
  uint32_t pk_buf[kP256PublicKeyWords];
  otcrypto_unblinded_key_t generated_public_key = {
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = sizeof(pk_buf),
      .key = pk_buf,
  };

  // Generate a keypair.
  LOG_INFO("Generating keypair...");
  TRY(otcrypto_ecdsa_p256_keygen(&private_key, &generated_public_key));

  // Import the private key shares into a fresh blinded key struct.
  // Use an exportable config so we can round-trip via export below.
  static const otcrypto_key_config_t kExportableKeyConfig = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = kP256PrivateKeyBytes,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolTrue,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  otcrypto_const_word32_buf_t share0 = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, keyblob, kP256MaskedScalarShareWords);

  otcrypto_const_word32_buf_t share1 = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, keyblob + kP256MaskedScalarShareWords,
      kP256MaskedScalarShareWords);

  uint32_t imported_keyblob[kP256MaskedScalarTotalShareWords];
  otcrypto_blinded_key_t imported_private_key = {
      .config = kExportableKeyConfig,
      .keyblob_length = sizeof(imported_keyblob),
      .keyblob = imported_keyblob,
  };
  LOG_INFO("Importing private key shares...");
  TRY(otcrypto_ecc_p256_private_key_import(share0, share1,
                                           &imported_private_key));

  // Export the imported private key back to shares and verify they match the
  // originals.
  uint32_t exported_share0_data[kP256MaskedScalarShareWords];
  uint32_t exported_share1_data[kP256MaskedScalarShareWords];
  otcrypto_word32_buf_t exported_share0 = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, exported_share0_data, kP256MaskedScalarShareWords);
  otcrypto_word32_buf_t exported_share1 = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, exported_share1_data, kP256MaskedScalarShareWords);

  LOG_INFO("Exporting private key shares...");
  TRY(otcrypto_ecc_p256_private_key_export(&imported_private_key,
                                           &exported_share0, &exported_share1));
  TRY_CHECK_ARRAYS_EQ(exported_share0_data, keyblob,
                      kP256MaskedScalarShareWords);
  TRY_CHECK_ARRAYS_EQ(exported_share1_data,
                      keyblob + kP256MaskedScalarShareWords,
                      kP256MaskedScalarShareWords);

  // Import the public key from its coordinates into a fresh buffer.
  p256_point_t *pt = (p256_point_t *)pk_buf;
  otcrypto_const_word32_buf_t x =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, pt->x, kP256CoordWords);

  otcrypto_const_word32_buf_t y =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, pt->y, kP256CoordWords);

  uint32_t imported_pk_buf[kP256PublicKeyWords];
  otcrypto_unblinded_key_t imported_public_key = {
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = sizeof(imported_pk_buf),
      .key = imported_pk_buf,
  };
  LOG_INFO("Importing public key from coordinates...");
  TRY(otcrypto_ecc_p256_public_key_import(x, y, &imported_public_key));
  TRY_CHECK_ARRAYS_EQ(imported_pk_buf, pk_buf, kP256PublicKeyWords);

  // Export the imported public key back to affine coordinates and confirm they
  // match the originals.
  uint32_t exported_x_data[kP256CoordWords];
  uint32_t exported_y_data[kP256CoordWords];
  otcrypto_word32_buf_t exported_x = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, exported_x_data, kP256CoordWords);
  otcrypto_word32_buf_t exported_y = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, exported_y_data, kP256CoordWords);
  LOG_INFO("Exporting public key to coordinates...");
  TRY(otcrypto_ecc_p256_public_key_export(&imported_public_key, &exported_x,
                                          &exported_y));
  TRY_CHECK_ARRAYS_EQ(exported_x_data, pt->x, kP256CoordWords);
  TRY_CHECK_ARRAYS_EQ(exported_y_data, pt->y, kP256CoordWords);

  // Hash the message.
  otcrypto_const_byte_buf_t msg =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, (unsigned char *)kMessage,
                        sizeof(kMessage) - 1);

  uint32_t msg_digest_data[kP256DigestWords];
  otcrypto_hash_digest_t msg_digest = {
      .data = msg_digest_data,
      .len = ARRAYSIZE(msg_digest_data),
  };
  TRY(otcrypto_sha2_256(&msg, &msg_digest));

  // Sign with the imported private key.
  uint32_t sig[kP256SignatureWords] = {0};
  otcrypto_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig, ARRAYSIZE(sig));
  LOG_INFO("Signing with imported private key...");
  TRY(otcrypto_ecdsa_p256_sign(&imported_private_key, msg_digest, &sig_buf));

  // Verify the signature with the imported public key.
  LOG_INFO("Verifying signature with imported public key...");
  otcrypto_const_word32_buf_t const_sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, sig, ARRAYSIZE(sig));

  hardened_bool_t verification_result;
  TRY(otcrypto_ecdsa_p256_verify(&imported_public_key, msg_digest,
                                 &const_sig_buf, &verification_result));
  TRY_CHECK(verification_result == kHardenedBoolTrue);

  return OK_STATUS();
}

/**
 * Test that the ECDH key mode is also accepted, and that coordinates are
 * stored as [x || y] in the key buffer.
 */
static status_t ecdh_key_mode_test(void) {
  // x and y coordinates of the P-256 generator point G, in little-endian
  // word order as used by the P-256 implementation.
  uint32_t x_data[kP256CoordWords] = {
      0xd898c296, 0xf4a13945, 0x2deb33a0, 0x77037d81,
      0x63a440f2, 0xf8bce6e5, 0x63b3b2da, 0x6b17d1f2,
  };
  uint32_t y_data[kP256CoordWords] = {
      0x37bf51f5, 0xcbb64068, 0x6b315ece, 0x2bce3357,
      0x7c0f9e16, 0x8ee7eb4a, 0xfe1a7f9b, 0x4fe342e2,
  };

  otcrypto_const_word32_buf_t x =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, x_data, kP256CoordWords);

  otcrypto_const_word32_buf_t y =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, y_data, kP256CoordWords);

  uint32_t pk_buf[kP256PublicKeyWords];
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdhP256,
      .key_length = sizeof(pk_buf),
      .key = pk_buf,
  };
  TRY(otcrypto_ecc_p256_public_key_import(x, y, &public_key));

  // Confirm the coordinates were stored as [x || y].
  TRY_CHECK_ARRAYS_EQ(pk_buf, x_data, kP256CoordWords);
  TRY_CHECK_ARRAYS_EQ(pk_buf + kP256CoordWords, y_data, kP256CoordWords);

  return OK_STATUS();
}

static status_t run_import_export_negative_tests(void) {
  LOG_INFO("Running import/export negative tests.");

  uint32_t x_data[8] = {0};
  uint32_t y_data[8] = {0};
  otcrypto_const_word32_buf_t x =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, x_data, 8);
  otcrypto_const_word32_buf_t y =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, y_data, 8);
  otcrypto_word32_buf_t x_out =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, x_data, 8);
  otcrypto_word32_buf_t y_out =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, y_data, 8);

  otcrypto_const_word32_buf_t x_bad_len = {.data = x_data, .len = 7};
  otcrypto_const_word32_buf_t y_bad_len = {.data = y_data, .len = 7};
  otcrypto_word32_buf_t x_out_bad = {.data = x_data, .len = 7};
  otcrypto_word32_buf_t y_out_bad = {.data = y_data, .len = 7};

  uint32_t pk_buf[16] = {0};
  otcrypto_unblinded_key_t pub_key = {
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = sizeof(pk_buf),
      .key = pk_buf,
  };
  pub_key.checksum = integrity_unblinded_checksum(&pub_key);

  uint32_t share0_data[10] = {0};
  uint32_t share1_data[10] = {0};
  otcrypto_const_word32_buf_t share0 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, share0_data, 10);
  otcrypto_const_word32_buf_t share1 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, share1_data, 10);
  otcrypto_word32_buf_t share0_out =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, share0_data, 10);
  otcrypto_word32_buf_t share1_out =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, share1_data, 10);

  otcrypto_const_word32_buf_t share0_bad_len = {.data = share0_data, .len = 9};
  otcrypto_const_word32_buf_t share1_bad_len = {.data = share1_data, .len = 9};
  otcrypto_word32_buf_t share0_out_bad = {.data = share0_data, .len = 9};
  otcrypto_word32_buf_t share1_out_bad = {.data = share1_data, .len = 9};

  uint32_t keyblob[20] = {0};
  otcrypto_key_config_t priv_cfg = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = 32,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolTrue,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  otcrypto_blinded_key_t priv_key = {
      .config = priv_cfg,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  priv_key.checksum = integrity_blinded_checksum(&priv_key);

  otcrypto_const_word32_buf_t null_in_buf = {0};
  otcrypto_word32_buf_t null_out_buf = {0};

  // -- Public Key Import --
  // Null inputs
  CHECK(otcrypto_ecc_p256_public_key_import(null_in_buf, y, &pub_key).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p256_public_key_import(x, null_in_buf, &pub_key).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p256_public_key_import(x, y, NULL).value !=
        OTCRYPTO_OK.value);

  otcrypto_unblinded_key_t pub_null_key = pub_key;
  pub_null_key.key = NULL;
  CHECK(otcrypto_ecc_p256_public_key_import(x, y, &pub_null_key).value !=
        OTCRYPTO_OK.value);

  // Bad length inputs
  CHECK(otcrypto_ecc_p256_public_key_import(x_bad_len, y, &pub_key).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p256_public_key_import(x, y_bad_len, &pub_key).value !=
        OTCRYPTO_OK.value);

  // Bad key mode
  otcrypto_unblinded_key_t pub_bad_mode = {
      .key_mode = kOtcryptoKeyModeAesCtr,
      .key_length = sizeof(pk_buf),
      .key = pk_buf,
  };
  CHECK(otcrypto_ecc_p256_public_key_import(x, y, &pub_bad_mode).value !=
        OTCRYPTO_OK.value);

  // -- Public Key Export --
  // Null inputs
  CHECK(otcrypto_ecc_p256_public_key_export(NULL, &x_out, &y_out).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p256_public_key_export(&pub_key, NULL, &y_out).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p256_public_key_export(&pub_key, &x_out, NULL).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p256_public_key_export(&pub_key, &null_out_buf, &y_out)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p256_public_key_export(&pub_null_key, &x_out, &y_out)
            .value != OTCRYPTO_OK.value);

  // Bad length inputs
  CHECK(
      otcrypto_ecc_p256_public_key_export(&pub_key, &x_out_bad, &y_out).value !=
      OTCRYPTO_OK.value);
  CHECK(
      otcrypto_ecc_p256_public_key_export(&pub_key, &x_out, &y_out_bad).value !=
      OTCRYPTO_OK.value);

  // Bad mode & integrity
  pub_bad_mode.checksum = integrity_unblinded_checksum(&pub_bad_mode);
  CHECK(otcrypto_ecc_p256_public_key_export(&pub_bad_mode, &x_out, &y_out)
            .value != OTCRYPTO_OK.value);

  otcrypto_unblinded_key_t pub_bad_integ = pub_key;
  pub_bad_integ.checksum ^= 0xFFFFFFFF;
  CHECK(otcrypto_ecc_p256_public_key_export(&pub_bad_integ, &x_out, &y_out)
            .value != OTCRYPTO_OK.value);

  // -- Private Key configs for bad mode/hw/null --
  otcrypto_key_config_t priv_bad_mode_cfg = priv_cfg;
  priv_bad_mode_cfg.key_mode = kOtcryptoKeyModeAesCtr;
  otcrypto_blinded_key_t priv_bad_mode = {
      .config = priv_bad_mode_cfg,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };

  otcrypto_key_config_t priv_bad_hw_cfg = priv_cfg;
  priv_bad_hw_cfg.hw_backed = kHardenedBoolTrue;
  otcrypto_blinded_key_t priv_bad_hw = {
      .config = priv_bad_hw_cfg,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };

  otcrypto_blinded_key_t priv_null_blob = {
      .config = priv_cfg,
      .keyblob_length = sizeof(keyblob),
      .keyblob = NULL,
      .checksum = 0,
  };

  // -- Private Key Import --
  // Null inputs
  CHECK(otcrypto_ecc_p256_private_key_import(null_in_buf, share1, &priv_key)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p256_private_key_import(share0, null_in_buf, &priv_key)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p256_private_key_import(share0, share1, NULL).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p256_private_key_import(share0, share1, &priv_null_blob)
            .value != OTCRYPTO_OK.value);

  // Bad length inputs
  CHECK(otcrypto_ecc_p256_private_key_import(share0_bad_len, share1, &priv_key)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p256_private_key_import(share0, share1_bad_len, &priv_key)
            .value != OTCRYPTO_OK.value);

  // Bad mode & hw_backed
  CHECK(otcrypto_ecc_p256_private_key_import(share0, share1, &priv_bad_mode)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p256_private_key_import(share0, share1, &priv_bad_hw)
            .value != OTCRYPTO_OK.value);

  // -- Private Key Export --
  // Null inputs
  CHECK(otcrypto_ecc_p256_private_key_export(NULL, &share0_out, &share1_out)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p256_private_key_export(&priv_key, NULL, &share1_out)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p256_private_key_export(&priv_key, &share0_out, NULL)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p256_private_key_export(&priv_key, &null_out_buf,
                                             &share1_out)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p256_private_key_export(&priv_null_blob, &share0_out,
                                             &share1_out)
            .value != OTCRYPTO_OK.value);

  // Bad length inputs
  CHECK(otcrypto_ecc_p256_private_key_export(&priv_key, &share0_out_bad,
                                             &share1_out)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p256_private_key_export(&priv_key, &share0_out,
                                             &share1_out_bad)
            .value != OTCRYPTO_OK.value);

  // Bad mode & hw_backed
  priv_bad_mode.checksum = integrity_blinded_checksum(&priv_bad_mode);
  CHECK(otcrypto_ecc_p256_private_key_export(&priv_bad_mode, &share0_out,
                                             &share1_out)
            .value != OTCRYPTO_OK.value);

  priv_bad_hw.checksum = integrity_blinded_checksum(&priv_bad_hw);
  CHECK(otcrypto_ecc_p256_private_key_export(&priv_bad_hw, &share0_out,
                                             &share1_out)
            .value != OTCRYPTO_OK.value);

  // Non exportable
  otcrypto_key_config_t priv_no_export_cfg = priv_cfg;
  priv_no_export_cfg.exportable = kHardenedBoolFalse;
  otcrypto_blinded_key_t priv_no_export = {
      .config = priv_no_export_cfg,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  priv_no_export.checksum = integrity_blinded_checksum(&priv_no_export);
  CHECK(otcrypto_ecc_p256_private_key_export(&priv_no_export, &share0_out,
                                             &share1_out)
            .value != OTCRYPTO_OK.value);

  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

  CHECK_STATUS_OK(ecdh_key_mode_test());

  CHECK_STATUS_OK(import_then_verify_test());

  CHECK_STATUS_OK(run_import_export_negative_tests());

  return true;
}
