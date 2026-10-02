// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <string.h>

#include "sw/device/lib/crypto/impl/state.h"
#include "sw/device/lib/crypto/include/aes.h"
#include "sw/device/lib/crypto/include/aes_gcm.h"
#include "sw/device/lib/crypto/include/cmvp.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/ecc_curve25519.h"
#include "sw/device/lib/crypto/include/ecc_p256.h"
#include "sw/device/lib/crypto/include/ecc_p384.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/key_transport.h"
#include "sw/device/lib/crypto/include/rsa.h"
#include "sw/device/lib/crypto/include/self_integrity.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

OTTF_DEFINE_TEST_CONFIG();

/**
 * @brief Tests state checks before otcrypto_init() is called.
 */
status_t test_pre_init_state_checks(void) {
  otcrypto_cmvp_service_indicator_t indicator = kOtcryptoCmvpApprovedService;
  TRY_CHECK(!status_ok(otcrypto_cmvp_service_indicator(NULL)),
            "Expected NULL indicator to fail.");
  TRY_CHECK(status_ok(otcrypto_cmvp_service_indicator(&indicator)),
            "Expected uninitialized state indicator query to succeed.");
  TRY_CHECK(indicator == kOtcryptoCmvpNoService,
            "Expected NoService before otcrypto_init.");

#ifdef FIPS_MODE
  // Before otcrypto_init, the OTBN scratch registers hold 0 (security_level ==
  // 0), so read_state fails with OTCRYPTO_RECOV_ERR in both
  // stateful_health_check and locked_state_check.
  otcrypto_status_t status = otcrypto_aes(NULL, NULL, kOtcryptoAesModeCbc,
                                          kOtcryptoAesOperationEncrypt, NULL,
                                          kOtcryptoAesPaddingNull, NULL);
  TRY_CHECK(status.value != kHardenedBoolTrue,
            "Expected stateful_health_check to fail before otcrypto_init.");

  status = otcrypto_ed25519_public_key_from_private(NULL, NULL);
  TRY_CHECK(status.value != kHardenedBoolTrue,
            "Expected locked_state_check to fail before otcrypto_init.");
#endif

  return OK_STATUS();
}

/**
 * @brief Tests that the KAT evaluation runs once and skips thereafter.
 */
status_t test_stateful_kat_execution(void) {
#ifdef FIPS_MODE
  LOG_INFO("Testing stateful KAT execution for FIPS build using AES...");

  // Read the initial state stored in the OTBN scratch registers
  crypto_state_t initial_state = {0};
  TRY(read_state(&initial_state));

  otcrypto_key_config_t config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeAesEcb,
      .key_length = 16,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };

  uint32_t share0_data[4] = {0x01234567, 0x89abcdef, 0x55aa55aa, 0xaa55aa55};
  uint32_t share1_data[4] = {0};
  otcrypto_const_word32_buf_t key_share0 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, share0_data, 4);
  otcrypto_const_word32_buf_t key_share1 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, share1_data, 4);

  uint32_t keyblob[8] = {0};
  otcrypto_blinded_key_t key = {
      .config = config,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };

  otcrypto_status_t import_status =
      otcrypto_import_blinded_key(&key_share0, &key_share1, &key);
  TRY_CHECK(import_status.value == kHardenedBoolTrue, "Key import failed.");

  uint32_t iv_data[4] = {0};
  otcrypto_word32_buf_t iv =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv_data, 4);

  uint8_t input_data[16] = {0};
  otcrypto_const_byte_buf_t input =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, input_data, 16);

  uint8_t output_data[16] = {0};
  otcrypto_byte_buf_t output =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, output_data, 16);

  uint64_t t1_start = ibex_mcycle_read();
  otcrypto_status_t status1 =
      otcrypto_aes(&key, &iv, kOtcryptoAesModeCbc, kOtcryptoAesOperationEncrypt,
                   &input, kOtcryptoAesPaddingNull, &output);
  uint64_t t1_end = ibex_mcycle_read();
  uint64_t first_run_cycles = t1_end - t1_start;

  // Ensure it failed properly inside otcrypto_aes
  TRY_CHECK(status1.value != kHardenedBoolTrue,
            "Expected failure due to mode mismatch.");

  // Verify that some KAT bit was successfully set in our stashed state
  crypto_state_t updated_state = {0};
  TRY(read_state(&updated_state));
  TRY_CHECK(memcmp(&initial_state, &updated_state, sizeof(crypto_state_t)) != 0,
            "KAT state was not mutated by the cryptolib.");

  uint64_t t2_start = ibex_mcycle_read();
  otcrypto_status_t status2 =
      otcrypto_aes(&key, &iv, kOtcryptoAesModeCbc, kOtcryptoAesOperationEncrypt,
                   &input, kOtcryptoAesPaddingNull, &output);
  uint64_t t2_end = ibex_mcycle_read();
  uint64_t second_run_cycles = t2_end - t2_start;

  TRY_CHECK(status2.value != kHardenedBoolTrue,
            "Expected failure due to mode mismatch.");

  LOG_INFO("First run (with KAT): %u cycles", (uint32_t)first_run_cycles);
  LOG_INFO("Second run (skipped KAT): %u cycles", (uint32_t)second_run_cycles);

  // Prove the second run was significantly faster
  TRY_CHECK(second_run_cycles < (first_run_cycles / 2),
            "Second run was not faster; KAT was not skipped.");

  LOG_INFO("KAT FIPS behavior verified using AES.");
#endif

  return OK_STATUS();
}

/**
 * @brief Tests FIPS locked_state, self_check_state, CMVP indicator, and
 *        FIPS-only parameter validation checks.
 */
status_t test_fips_state_and_param_checks(void) {
#ifdef FIPS_MODE
  // 1. Test CMVP service indicator after an operation.
  otcrypto_cmvp_service_indicator_t indicator = kOtcryptoCmvpNoService;
  TRY_CHECK(status_ok(otcrypto_cmvp_service_indicator(&indicator)),
            "Expected cmvp_service_indicator to succeed.");

  crypto_state_t state = {0};
  TRY(read_state(&state));

  // 2. Test self_check_state == kHardenedByteBoolFalse.
  uint8_t saved_self_check = state.self_check_state;
  state.self_check_state = kHardenedByteBoolFalse;
  TRY(store_state(&state));

  otcrypto_status_t status = otcrypto_aes(NULL, NULL, kOtcryptoAesModeCbc,
                                          kOtcryptoAesOperationEncrypt, NULL,
                                          kOtcryptoAesPaddingNull, NULL);
  TRY_CHECK(status.value != kHardenedBoolTrue,
            "Expected stateful_health_check to fail when self_check is false.");

  status = otcrypto_ed25519_public_key_from_private(NULL, NULL);
  TRY_CHECK(status.value != kHardenedBoolTrue,
            "Expected locked_state_check to fail when self_check is false.");

  TRY(read_state(&state));
  state.self_check_state = saved_self_check;
  TRY(store_state(&state));

  // 3. Test locked_state == kHardenedByteBoolTrue.
  uint8_t saved_locked = state.locked_state;
  state.locked_state = kHardenedByteBoolTrue;
  TRY(store_state(&state));

  status = otcrypto_integrity_check();
  TRY_CHECK(status.value != kHardenedBoolTrue,
            "Expected otcrypto_integrity_check to fail when locked.");

  status = otcrypto_aes(NULL, NULL, kOtcryptoAesModeCbc,
                        kOtcryptoAesOperationEncrypt, NULL,
                        kOtcryptoAesPaddingNull, NULL);
  TRY_CHECK(status.value != kHardenedBoolTrue,
            "Expected stateful_health_check to fail when locked.");

  status = otcrypto_ed25519_public_key_from_private(NULL, NULL);
  TRY_CHECK(status.value != kHardenedBoolTrue,
            "Expected locked_state_check to fail when locked.");

  TRY(read_state(&state));
  state.locked_state = saved_locked;
  TRY(store_state(&state));

  // 4. Mark all KATs as completed to test FIPS parameter validation directly.
  uint32_t saved_kat_state = state.kat_state;
  state.kat_state = 0xFFFFFFFF;
  TRY(store_state(&state));

  // 4a. AES-GCM non-approved tag length (64-bit) in FIPS mode.
  uint32_t dummy_words[16] = {0};
  uint8_t dummy_bytes[16] = {0};
  otcrypto_blinded_key_t gcm_key = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModeAesGcm,
              .key_length = 16,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = 32,
      .keyblob = dummy_words,
  };
  gcm_key.checksum = otcrypto_integrity_blinded_checksum(&gcm_key);
  otcrypto_const_byte_buf_t pt =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, dummy_bytes, 16);
  otcrypto_const_word32_buf_t gcm_iv =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, dummy_words, 3);
  otcrypto_const_byte_buf_t aad =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, dummy_bytes, 0);
  otcrypto_byte_buf_t ct =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, dummy_bytes, 16);
  otcrypto_word32_buf_t tag =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, dummy_words, 2);
  status = otcrypto_aes_gcm_encrypt(&gcm_key, &pt, &gcm_iv, &aad,
                                    kOtcryptoAesGcmTagLen64, &ct, &tag);
  TRY_CHECK(status.value != kHardenedBoolTrue,
            "Expected 64-bit AES-GCM tag length to be rejected in FIPS mode.");

  // 4b. ECDSA P-256 DICE sign with non-approved hash mode (SHAKE128).
  otcrypto_blinded_key_t p256_key = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModeEcdsaP256,
              .key_length = 32,
              .hw_backed = kHardenedBoolTrue,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = 32,
      .keyblob = dummy_words,
  };
  p256_key.checksum = otcrypto_integrity_blinded_checksum(&p256_key);
  otcrypto_hash_digest_t bad_p256_digest = {
      .mode = kOtcryptoHashXofModeShake128,
      .data = dummy_words,
      .len = 8,
  };
  status = otcrypto_ecdsa_p256_dice_sign_async_start(&p256_key, bad_p256_digest,
                                                     &gcm_iv);
  TRY_CHECK(status.value != kHardenedBoolTrue,
            "Expected SHAKE128 digest to be rejected for P-256 in FIPS mode.");

  // 4c. ECDSA P-384 verify with non-approved hash mode (SHA-256).
  uint32_t p384_pk_words[24] = {0};
  otcrypto_unblinded_key_t p384_pk = {
      .key_mode = kOtcryptoKeyModeEcdsaP384,
      .key_length = sizeof(p384_pk_words),
      .key = p384_pk_words,
  };
  p384_pk.checksum = otcrypto_integrity_unblinded_checksum(&p384_pk);
  otcrypto_hash_digest_t bad_p384_digest = {
      .mode = kOtcryptoHashModeSha256,
      .data = dummy_words,
      .len = 12,
  };
  otcrypto_const_word32_buf_t p384_sig =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, p384_pk_words, 24);
  status = otcrypto_ecdsa_p384_verify_async_start(&p384_pk, bad_p384_digest,
                                                  &p384_sig);
  TRY_CHECK(status.value != kHardenedBoolTrue,
            "Expected SHA-256 digest to be rejected for P-384 in FIPS mode.");

  // 4d. RSA-3072 sign with insufficient hash strength (SHA3-224).
  static uint32_t
      rsa3072_keyblob[kOtcryptoRsa3072PrivateKeyblobBytes / sizeof(uint32_t)];
  memset(rsa3072_keyblob, 0, sizeof(rsa3072_keyblob));
  otcrypto_blinded_key_t rsa3072_sk = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModeRsaSignPkcs,
              .key_length = kOtcryptoRsa3072PrivateKeyBytes,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = kOtcryptoRsa3072PrivateKeyblobBytes,
      .keyblob = rsa3072_keyblob,
  };
  rsa3072_sk.checksum = otcrypto_integrity_blinded_checksum(&rsa3072_sk);
  otcrypto_hash_digest_t sha3_224_digest = {
      .mode = kOtcryptoHashModeSha3_224,
      .data = dummy_words,
      .len = 7,
  };
  status = otcrypto_rsa_sign_async_start(&rsa3072_sk, sha3_224_digest,
                                         kOtcryptoRsaPaddingPkcs);
  TRY_CHECK(status.value != kHardenedBoolTrue,
            "Expected SHA3-224 digest to be rejected for RSA-3072 in FIPS "
            "mode.");

  TRY(read_state(&state));
  state.kat_state = saved_kat_state;
  TRY(store_state(&state));
#endif

  return OK_STATUS();
}

bool test_main(void) {
  CHECK_STATUS_OK(test_pre_init_state_checks());
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelHigh));

  CHECK_STATUS_OK(test_stateful_kat_execution());
  CHECK_STATUS_OK(test_fips_state_and_param_checks());

  return true;
}
