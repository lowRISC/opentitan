// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/drivers/keymgr.h"
#include "sw/device/lib/crypto/impl/ecc/p256.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/ecc_p256.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/key_transport.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/hexstr.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Keymgr handle for this test.
static dif_keymgr_t keymgr;

OTTF_DEFINE_TEST_CONFIG();

status_t dice_test(void) {
  char buf[256];

  otcrypto_key_config_t kPrivateKeyConfig = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = 256 / 8,
      .hw_backed = kHardenedBoolTrue,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };

  // This is an example salt, for the CDI key, a specific salt should be used.
  const uint32_t kPrivateKeySalt[8] = {0x00010203, 0x04050607, 0x08090a0b,
                                       0x0c0d0e0f, 0xf0f1f2f3, 0xf4f5f6f7,
                                       0xf8f9fafb, 0xfcfdfeff};

  const uint32_t kPrivateKeyVersion = 0x0;

  uint32_t keyblob[9];
  otcrypto_blinded_key_t private_key = {
      .config = kPrivateKeyConfig,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };

  TRY(otcrypto_hw_backed_attestation_key(kPrivateKeyVersion, kPrivateKeySalt,
                                         &private_key));

  // This is an example attestation seed, for the CDI key, a specific seed
  // should be used.
  uint32_t attestation_data[10] = {
      0x70717273, 0x74757677, 0x78797a7b, 0x7c7d7e7f, 0x80818283,
      0x84858687, 0x88898a8b, 0x8c8d8e8f, 0x90b1b2b3, 0x94959697};
  otcrypto_const_word32_buf_t attestation_seed =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, attestation_data, 10);

  uint32_t pk[512 / 32] = {0};
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = sizeof(pk),
      .key = pk,
  };

  // We generate a public key, however, this is currently not checked against
  // the x509 certificate.
  TRY(otcrypto_ecdsa_p256_dice_keygen_async_start(&private_key,
                                                  &attestation_seed));
  TRY(otcrypto_ecdsa_p256_dice_keygen_async_finalize(&private_key,
                                                     &public_key));
  hexstr_encode(buf, sizeof(buf), pk, sizeof(pk));
  LOG_INFO("Public key: %s\r", buf);
  LOG_INFO("OTBN keygen instruction count: 0x%08x",
           otbn_instruction_count_get());

  // Checking the synchronous call and whether the same public key is generated
  // the second time.
  uint32_t pk_2[512 / 32] = {0};
  otcrypto_unblinded_key_t public_key_2 = {
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = sizeof(pk_2),
      .key = pk_2,
  };
  TRY(otcrypto_ecdsa_p256_dice_keygen(&private_key, &public_key_2,
                                      &attestation_seed));
  CHECK_ARRAYS_EQ(pk, pk_2, 512 / 32);

  uint32_t sigdata[16] = {0};
  otcrypto_word32_buf_t signature =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sigdata, 16);

  uint32_t digest_data[8] = {1, 2, 3, 4, 5, 6, 7, 8};
  otcrypto_hash_digest_t digest = {
      .mode = 0,
      .data = digest_data,
      .len = 8,
  };

  hexstr_encode(buf, sizeof(buf), digest_data, sizeof(digest_data));
  LOG_INFO("Message: %s\r", buf);

  // Perform a sign and verify where the sign uses the generated key in OTBN.
  TRY(otcrypto_ecdsa_p256_dice_sign_async_start(&private_key, digest,
                                                &attestation_seed));
  TRY(otcrypto_ecdsa_p256_dice_sign_async_finalize(&signature));
  LOG_INFO("OTBN sign instruction count: 0x%08x", otbn_instruction_count_get());

  hexstr_encode(buf, sizeof(buf), sigdata, sizeof(sigdata));
  LOG_INFO("Signature: %s\r", buf);

  hardened_bool_t result = 0;
  TRY(p256_ecdsa_verify_start((const p256_ecdsa_signature_t *)sigdata,
                              digest_data, (const p256_point_t *)pk));
  TRY(p256_ecdsa_verify_finalize((const p256_ecdsa_signature_t *)sigdata,
                                 &result));
  CHECK(result == kHardenedBoolTrue);

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
  return otcrypto_init(kOtcryptoKeySecurityLevelLow);
}

static status_t run_dice_negative_tests(void) {
  LOG_INFO("Running DICE negative tests.");

  uint32_t priv_keyblob[80] = {0};
  otcrypto_key_config_t dice_cfg = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = 256 / 8,
      .hw_backed = kHardenedBoolTrue,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  otcrypto_blinded_key_t valid_priv = {
      .config = dice_cfg,
      .keyblob_length = sizeof(priv_keyblob),
      .keyblob = priv_keyblob,
  };
  valid_priv.checksum = integrity_blinded_checksum(&valid_priv);

  uint32_t digest_data[8] = {0};
  otcrypto_hash_digest_t valid_digest = {
      .data = digest_data,
      .len = 8,
  };

  uint32_t attestation_data[10] = {0};
  otcrypto_const_word32_buf_t attestation_seed =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, attestation_data, 10);

  // Null inputs
  CHECK(otcrypto_ecdsa_p256_dice_sign_async_start(NULL, valid_digest,
                                                  &attestation_seed)
            .value != OTCRYPTO_OK.value);

  otcrypto_hash_digest_t null_digest = {.data = NULL, .len = 8};
  CHECK(otcrypto_ecdsa_p256_dice_sign_async_start(&valid_priv, null_digest,
                                                  &attestation_seed)
            .value != OTCRYPTO_OK.value);

  // Bad key_mode
  otcrypto_key_config_t bad_mode_cfg = dice_cfg;
  bad_mode_cfg.key_mode = kOtcryptoKeyModeEcdhP256;
  otcrypto_blinded_key_t bad_mode_priv = {
      .config = bad_mode_cfg,
      .keyblob_length = sizeof(priv_keyblob),
      .keyblob = priv_keyblob,
  };
  bad_mode_priv.checksum = integrity_blinded_checksum(&bad_mode_priv);
  CHECK(otcrypto_ecdsa_p256_dice_sign_async_start(&bad_mode_priv, valid_digest,
                                                  &attestation_seed)
            .value != OTCRYPTO_OK.value);

  // Bad length inputs
  otcrypto_hash_digest_t bad_len_digest = {.data = digest_data, .len = 7};
  CHECK(otcrypto_ecdsa_p256_dice_sign_async_start(&valid_priv, bad_len_digest,
                                                  &attestation_seed)
            .value != OTCRYPTO_OK.value);

  return OTCRYPTO_OK;
}

bool test_main(void) {
  status_t result = OTCRYPTO_OK;
  CHECK_STATUS_OK(test_setup());
  EXECUTE_TEST(result, dice_test);
  EXECUTE_TEST(result, run_dice_negative_tests);
  return status_ok(result);
}
