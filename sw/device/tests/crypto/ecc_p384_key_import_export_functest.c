// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/ecc/p384.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/ecc_p384.h"
#include "sw/device/lib/crypto/include/entropy_src.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/runtime/log.h"
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
 * Generate a P-384 keypair, re-import both the private key shares and the
 * public key coordinates, then sign with the imported private key and verify
 * with the imported public key.
 *
 * This tests otcrypto_ecc_p384_private_key_import,
 * otcrypto_ecc_p384_private_key_export, otcrypto_ecc_p384_public_key_import,
 * and otcrypto_ecc_p384_public_key_export together: a valid signature can only
 * be produced and verified if both imports round-tripped the key material
 * correctly, and both exports are verified against the original raw values.
 */
static status_t import_then_verify_test(void) {
  // Allocate space for the generated private key.
  uint32_t keyblob[kP384MaskedScalarTotalShareWords];
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

  // Import the private key shares into a fresh blinded key struct.
  // Use an exportable config so we can round-trip via export below.
  static const otcrypto_key_config_t kExportableKeyConfig = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeEcdsaP384,
      .key_length = kP384PrivateKeyBytes,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolTrue,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  otcrypto_const_word32_buf_t share0 = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, keyblob, kP384MaskedScalarShareWords);

  otcrypto_const_word32_buf_t share1 = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, keyblob + kP384MaskedScalarShareWords,
      kP384MaskedScalarShareWords);

  uint32_t imported_keyblob[kP384MaskedScalarTotalShareWords];
  otcrypto_blinded_key_t imported_private_key = {
      .config = kExportableKeyConfig,
      .keyblob_length = sizeof(imported_keyblob),
      .keyblob = imported_keyblob,
  };
  LOG_INFO("Importing private key shares...");
  TRY(otcrypto_ecc_p384_private_key_import(share0, share1,
                                           &imported_private_key));

  // Export the imported private key back to shares and verify they match the
  // originals.
  uint32_t exported_share0_data[kP384MaskedScalarShareWords];
  uint32_t exported_share1_data[kP384MaskedScalarShareWords];
  otcrypto_word32_buf_t exported_share0 = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, exported_share0_data, kP384MaskedScalarShareWords);
  otcrypto_word32_buf_t exported_share1 = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, exported_share1_data, kP384MaskedScalarShareWords);
  LOG_INFO("Exporting private key shares...");
  TRY(otcrypto_ecc_p384_private_key_export(&imported_private_key,
                                           &exported_share0, &exported_share1));
  TRY_CHECK_ARRAYS_EQ(exported_share0_data, keyblob,
                      kP384MaskedScalarShareWords);
  TRY_CHECK_ARRAYS_EQ(exported_share1_data,
                      keyblob + kP384MaskedScalarShareWords,
                      kP384MaskedScalarShareWords);

  // Import the public key from its coordinates into a fresh buffer.
  p384_point_t *pt = (p384_point_t *)pk_buf;
  otcrypto_const_word32_buf_t x =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, pt->x, kP384CoordWords);

  otcrypto_const_word32_buf_t y =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, pt->y, kP384CoordWords);

  uint32_t imported_pk_buf[kP384PublicKeyWords];
  otcrypto_unblinded_key_t imported_public_key = {
      .key_mode = kOtcryptoKeyModeEcdsaP384,
      .key_length = sizeof(imported_pk_buf),
      .key = imported_pk_buf,
  };
  LOG_INFO("Importing public key from coordinates...");
  TRY(otcrypto_ecc_p384_public_key_import(x, y, &imported_public_key));
  TRY_CHECK_ARRAYS_EQ(imported_pk_buf, pk_buf, kP384PublicKeyWords);

  // Export the imported public key back to affine coordinates and confirm they
  // match the originals, completing the import → export round-trip.
  uint32_t exported_x_data[kP384CoordWords];
  uint32_t exported_y_data[kP384CoordWords];
  otcrypto_word32_buf_t exported_x = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, exported_x_data, kP384CoordWords);
  otcrypto_word32_buf_t exported_y = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, exported_y_data, kP384CoordWords);
  LOG_INFO("Exporting public key to coordinates...");
  TRY(otcrypto_ecc_p384_public_key_export(&imported_public_key, &exported_x,
                                          &exported_y));
  TRY_CHECK_ARRAYS_EQ(exported_x_data, pt->x, kP384CoordWords);
  TRY_CHECK_ARRAYS_EQ(exported_y_data, pt->y, kP384CoordWords);

  // Hash the message.
  otcrypto_const_byte_buf_t msg =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, (unsigned char *)kMessage,
                        sizeof(kMessage) - 1);
  uint32_t msg_digest_data[kP384DigestWords];
  otcrypto_hash_digest_t msg_digest = {
      .data = msg_digest_data,
      .len = ARRAYSIZE(msg_digest_data),
  };
  TRY(otcrypto_sha2_384(&msg, &msg_digest));

  // Sign the message with the imported private key.
  uint32_t sig[kP384SignatureWords] = {0};
  otcrypto_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig, ARRAYSIZE(sig));
  LOG_INFO("Signing with imported private key...");
  TRY(otcrypto_ecdsa_p384_sign(&imported_private_key, msg_digest, &sig_buf));

  // Verify the signature using the imported public key.
  LOG_INFO("Verifying signature with imported public key...");
  otcrypto_const_word32_buf_t const_sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, sig, ARRAYSIZE(sig));

  hardened_bool_t verification_result;
  TRY(otcrypto_ecdsa_p384_verify(&imported_public_key, msg_digest,
                                 &const_sig_buf, &verification_result));
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

  otcrypto_const_word32_buf_t x =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, x_data, kP384CoordWords);

  otcrypto_const_word32_buf_t y =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, y_data, kP384CoordWords);

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

static status_t run_import_export_negative_tests(void) {
  LOG_INFO("Running import/export negative tests.");

  uint32_t x_data[12] = {0};
  uint32_t y_data[12] = {0};
  otcrypto_const_word32_buf_t x =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, x_data, 12);
  otcrypto_const_word32_buf_t y =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, y_data, 12);
  otcrypto_word32_buf_t x_out =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, x_data, 12);
  otcrypto_word32_buf_t y_out =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, y_data, 12);

  otcrypto_const_word32_buf_t x_bad_len = {.data = x_data, .len = 11};
  otcrypto_const_word32_buf_t y_bad_len = {.data = y_data, .len = 11};
  otcrypto_word32_buf_t x_out_bad = {.data = x_data, .len = 11};
  otcrypto_word32_buf_t y_out_bad = {.data = y_data, .len = 11};

  uint32_t pk_buf[24] = {0};
  otcrypto_unblinded_key_t pub_key = {
      .key_mode = kOtcryptoKeyModeEcdsaP384,
      .key_length = sizeof(pk_buf),
      .key = pk_buf,
  };
  pub_key.checksum = integrity_unblinded_checksum(&pub_key);

  uint32_t share0_data[14] = {0};
  uint32_t share1_data[14] = {0};
  otcrypto_const_word32_buf_t share0 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, share0_data, 14);
  otcrypto_const_word32_buf_t share1 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, share1_data, 14);
  otcrypto_word32_buf_t share0_out =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, share0_data, 14);
  otcrypto_word32_buf_t share1_out =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, share1_data, 14);

  otcrypto_const_word32_buf_t share0_bad_len = {.data = share0_data, .len = 13};
  otcrypto_const_word32_buf_t share1_bad_len = {.data = share1_data, .len = 13};
  otcrypto_word32_buf_t share0_out_bad = {.data = share0_data, .len = 13};
  otcrypto_word32_buf_t share1_out_bad = {.data = share1_data, .len = 13};

  uint32_t keyblob[28] = {0};
  otcrypto_key_config_t priv_cfg = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeEcdsaP384,
      .key_length = 48,
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
  CHECK(otcrypto_ecc_p384_public_key_import(null_in_buf, y, &pub_key).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p384_public_key_import(x, null_in_buf, &pub_key).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p384_public_key_import(x, y, NULL).value !=
        OTCRYPTO_OK.value);

  otcrypto_unblinded_key_t pub_null_key = pub_key;
  pub_null_key.key = NULL;
  CHECK(otcrypto_ecc_p384_public_key_import(x, y, &pub_null_key).value !=
        OTCRYPTO_OK.value);

  // Bad length inputs
  CHECK(otcrypto_ecc_p384_public_key_import(x_bad_len, y, &pub_key).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p384_public_key_import(x, y_bad_len, &pub_key).value !=
        OTCRYPTO_OK.value);

  // Bad key mode
  otcrypto_unblinded_key_t pub_bad_mode = {
      .key_mode = kOtcryptoKeyModeAesCtr,
      .key_length = sizeof(pk_buf),
      .key = pk_buf,
  };
  CHECK(otcrypto_ecc_p384_public_key_import(x, y, &pub_bad_mode).value !=
        OTCRYPTO_OK.value);

  // -- Public Key Export --
  // Null inputs
  CHECK(otcrypto_ecc_p384_public_key_export(NULL, &x_out, &y_out).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p384_public_key_export(&pub_key, NULL, &y_out).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p384_public_key_export(&pub_key, &x_out, NULL).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p384_public_key_export(&pub_key, &null_out_buf, &y_out)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p384_public_key_export(&pub_null_key, &x_out, &y_out)
            .value != OTCRYPTO_OK.value);

  // Bad length inputs
  CHECK(
      otcrypto_ecc_p384_public_key_export(&pub_key, &x_out_bad, &y_out).value !=
      OTCRYPTO_OK.value);
  CHECK(
      otcrypto_ecc_p384_public_key_export(&pub_key, &x_out, &y_out_bad).value !=
      OTCRYPTO_OK.value);

  // Bad mode & integrity
  pub_bad_mode.checksum = integrity_unblinded_checksum(&pub_bad_mode);
  CHECK(otcrypto_ecc_p384_public_key_export(&pub_bad_mode, &x_out, &y_out)
            .value != OTCRYPTO_OK.value);

  otcrypto_unblinded_key_t pub_bad_integ = pub_key;
  pub_bad_integ.checksum ^= 0xFFFFFFFF;
  CHECK(otcrypto_ecc_p384_public_key_export(&pub_bad_integ, &x_out, &y_out)
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
  CHECK(otcrypto_ecc_p384_private_key_import(null_in_buf, share1, &priv_key)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p384_private_key_import(share0, null_in_buf, &priv_key)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p384_private_key_import(share0, share1, NULL).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p384_private_key_import(share0, share1, &priv_null_blob)
            .value != OTCRYPTO_OK.value);

  // Bad length inputs
  CHECK(otcrypto_ecc_p384_private_key_import(share0_bad_len, share1, &priv_key)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p384_private_key_import(share0, share1_bad_len, &priv_key)
            .value != OTCRYPTO_OK.value);

  // Bad mode & hw_backed
  CHECK(otcrypto_ecc_p384_private_key_import(share0, share1, &priv_bad_mode)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p384_private_key_import(share0, share1, &priv_bad_hw)
            .value != OTCRYPTO_OK.value);

  // -- Private Key Export --
  // Null inputs
  CHECK(otcrypto_ecc_p384_private_key_export(NULL, &share0_out, &share1_out)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p384_private_key_export(&priv_key, NULL, &share1_out)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p384_private_key_export(&priv_key, &share0_out, NULL)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p384_private_key_export(&priv_key, &null_out_buf,
                                             &share1_out)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p384_private_key_export(&priv_null_blob, &share0_out,
                                             &share1_out)
            .value != OTCRYPTO_OK.value);

  // Bad length inputs
  CHECK(otcrypto_ecc_p384_private_key_export(&priv_key, &share0_out_bad,
                                             &share1_out)
            .value != OTCRYPTO_OK.value);
  CHECK(otcrypto_ecc_p384_private_key_export(&priv_key, &share0_out,
                                             &share1_out_bad)
            .value != OTCRYPTO_OK.value);

  // Bad mode & hw_backed
  priv_bad_mode.checksum = integrity_blinded_checksum(&priv_bad_mode);
  CHECK(otcrypto_ecc_p384_private_key_export(&priv_bad_mode, &share0_out,
                                             &share1_out)
            .value != OTCRYPTO_OK.value);

  priv_bad_hw.checksum = integrity_blinded_checksum(&priv_bad_hw);
  CHECK(otcrypto_ecc_p384_private_key_export(&priv_bad_hw, &share0_out,
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
  CHECK(otcrypto_ecc_p384_private_key_export(&priv_no_export, &share0_out,
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
