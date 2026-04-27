// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/ecc_p384.h"
#include "sw/device/lib/crypto/include/entropy_src.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/key_transport.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

enum {
  /* Number of 32-bit words in a P-384 public key. */
  kP384PublicKeyWords = 768 / 32,
  /* Number of 32-bit words in a P-384 signature. */
  kP384SignatureWords = 768 / 32,
  /* Number of bytes in a P-384 private key. */
  kP384PrivateKeyBytes = 384 / 8,
  /* Number of bytes in an ECDH/P-384 shared key. */
  kP384SharedKeyBytes = 384 / 8,
  /* Number of 32-bit words in an ECDH/P-384 shared key. */
  kP384SharedKeyWords = kP384SharedKeyBytes / sizeof(uint32_t),
};

// Configuration for the private key.
static const otcrypto_key_config_t kEcdhPrivateKeyConfig = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeEcdhP384,
    .key_length = kP384PrivateKeyBytes,
    .hw_backed = kHardenedBoolFalse,
    .exportable = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

// Configuration for the ECDH shared (symmetric) key. This configuration
// specifies an AES key, but any symmetric mode that supports 384-bit keys is
// OK here.
static const otcrypto_key_config_t kEcdhSharedKeyConfig = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeAesCtr,
    .key_length = kP384SharedKeyBytes,
    .hw_backed = kHardenedBoolFalse,
    .exportable = kHardenedBoolTrue,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

status_t key_exchange_test(void) {
  // Allocate space for two private keys.
  uint32_t keyblobA[keyblob_num_words(kEcdhPrivateKeyConfig)];
  otcrypto_blinded_key_t private_keyA = {
      .config = kEcdhPrivateKeyConfig,
      .keyblob_length = sizeof(keyblobA),
      .keyblob = keyblobA,
      .checksum = 0,
  };
  uint32_t keyblobB[keyblob_num_words(kEcdhPrivateKeyConfig)];
  otcrypto_blinded_key_t private_keyB = {
      .config = kEcdhPrivateKeyConfig,
      .keyblob_length = sizeof(keyblobB),
      .keyblob = keyblobB,
      .checksum = 0,
  };

  // Allocate space for two public keys.
  uint32_t pkA[kP384PublicKeyWords] = {0};
  uint32_t pkB[kP384PublicKeyWords] = {0};
  otcrypto_unblinded_key_t public_keyA = {
      .key_mode = kOtcryptoKeyModeEcdhP384,
      .key_length = sizeof(pkA),
      .key = pkA,
  };
  otcrypto_unblinded_key_t public_keyB = {
      .key_mode = kOtcryptoKeyModeEcdhP384,
      .key_length = sizeof(pkB),
      .key = pkB,
  };

  // Generate a keypair.
  LOG_INFO("Generating keypair A...");
  TRY(otcrypto_ecdh_p384_keygen(&private_keyA, &public_keyA));

  // Generate a second keypair.
  LOG_INFO("Generating keypair B...");
  TRY(otcrypto_ecdh_p384_keygen(&private_keyB, &public_keyB));

  // Sanity check; public keys should be different from each other.
  CHECK_ARRAYS_NE(pkA, pkB, ARRAYSIZE(pkA));
  // Sanity check; private keys should be different from each other.
  CHECK_ARRAYS_NE(keyblobA, keyblobB, ARRAYSIZE(keyblobA));

  uint32_t shared_keyblobA[keyblob_num_words(kEcdhSharedKeyConfig)];
  otcrypto_blinded_key_t shared_keyA = {
      .config = kEcdhSharedKeyConfig,
      .keyblob_length = sizeof(shared_keyblobA),
      .keyblob = shared_keyblobA,
      .checksum = 0,
  };
  uint32_t shared_keyblobB[keyblob_num_words(kEcdhSharedKeyConfig)];
  otcrypto_blinded_key_t shared_keyB = {
      .config = kEcdhSharedKeyConfig,
      .keyblob_length = sizeof(shared_keyblobB),
      .keyblob = shared_keyblobB,
      .checksum = 0,
  };

  // Compute the shared secret from A's side of the computation (using A's
  // private key and B's public key).
  LOG_INFO("Generating shared secret (A)...");
  TRY(otcrypto_ecdh_p384(&private_keyA, &public_keyB, &shared_keyA));

  // Compute the shared secret from B's side of the computation (using B's
  // private key and A's public key).
  LOG_INFO("Generating shared secret (B)...");
  TRY(otcrypto_ecdh_p384(&private_keyB, &public_keyA, &shared_keyB));

  uint32_t keyA0[kP384SharedKeyWords];
  uint32_t keyA1[kP384SharedKeyWords];
  otcrypto_word32_buf_t keyA0_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, keyA0, ARRAYSIZE(keyA0));
  otcrypto_word32_buf_t keyA1_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, keyA1, ARRAYSIZE(keyA1));
  TRY(otcrypto_export_blinded_key(&shared_keyA, &keyA0_buf, &keyA1_buf));

  uint32_t keyB0[kP384SharedKeyWords];
  uint32_t keyB1[kP384SharedKeyWords];
  otcrypto_word32_buf_t keyB0_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, keyB0, ARRAYSIZE(keyB0));
  otcrypto_word32_buf_t keyB1_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, keyB1, ARRAYSIZE(keyB1));
  TRY(otcrypto_export_blinded_key(&shared_keyB, &keyB0_buf, &keyB1_buf));

  // Unmask the keys and check that they match.
  uint32_t keyA[kP384SharedKeyWords];
  uint32_t keyB[kP384SharedKeyWords];
  TRY(hardened_xor(keyA0, keyA1, kP384SharedKeyWords, keyA));
  TRY(hardened_xor(keyB0, keyB1, kP384SharedKeyWords, keyB));
  CHECK_ARRAYS_EQ(keyA, keyB, ARRAYSIZE(keyA));

  return OTCRYPTO_OK;
}

static status_t run_ecdh_negative_tests(void) {
  LOG_INFO("Running ECDH negative tests.");

  uint32_t priv_keyblob[112 / 4] = {0};
  otcrypto_blinded_key_t valid_priv = {
      .config = kEcdhPrivateKeyConfig,
      .keyblob_length = 112,
      .keyblob = priv_keyblob,
  };
  valid_priv.checksum = integrity_blinded_checksum(&valid_priv);

  uint32_t pub_key_data[96 / 4] = {0};
  otcrypto_unblinded_key_t valid_pub = {
      .key_mode = kOtcryptoKeyModeEcdhP384,
      .key_length = 96,
      .key = pub_key_data,
  };
  valid_pub.checksum = integrity_unblinded_checksum(&valid_pub);

  uint32_t shared_keyblob[keyblob_num_words(kEcdhSharedKeyConfig)];
  otcrypto_blinded_key_t valid_shared = {
      .config = kEcdhSharedKeyConfig,
      .keyblob_length = sizeof(shared_keyblob),
      .keyblob = shared_keyblob,
  };
  valid_shared.checksum = integrity_blinded_checksum(&valid_shared);

  // ECDH keygen negative tests

  // Null pointers
  CHECK(otcrypto_ecdh_p384_keygen(NULL, &valid_pub).value != OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdh_p384_keygen_async_start(NULL).value != OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdh_p384_keygen_async_finalize(NULL, &valid_pub).value !=
        OTCRYPTO_OK.value);

  CHECK(otcrypto_ecdh_p384_keygen(&valid_priv, NULL).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdh_p384_keygen_async_finalize(&valid_priv, NULL).value !=
        OTCRYPTO_OK.value);

  // Null keyblob
  otcrypto_blinded_key_t bad_priv_null = {
      .config = kEcdhPrivateKeyConfig,
      .keyblob_length = 112,
      .keyblob = NULL,
  };
  CHECK(otcrypto_ecdh_p384_keygen(&bad_priv_null, &valid_pub).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdh_p384_keygen_async_start(&bad_priv_null).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdh_p384_keygen_async_finalize(&bad_priv_null, &valid_pub)
            .value != OTCRYPTO_OK.value);

  // Bad mode
  otcrypto_key_config_t bad_mode_cfg = kEcdhPrivateKeyConfig;
  bad_mode_cfg.key_mode = kOtcryptoKeyModeEcdsaP384;
  otcrypto_blinded_key_t bad_priv_mode = {
      .config = bad_mode_cfg,
      .keyblob_length = 112,
      .keyblob = priv_keyblob,
  };
  bad_priv_mode.checksum = integrity_blinded_checksum(&bad_priv_mode);
  CHECK(otcrypto_ecdh_p384_keygen(&bad_priv_mode, &valid_pub).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdh_p384_keygen_async_start(&bad_priv_mode).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdh_p384_keygen_async_finalize(&bad_priv_mode, &valid_pub)
            .value != OTCRYPTO_OK.value);

  // Bad length
  otcrypto_key_config_t bad_len_cfg = kEcdhPrivateKeyConfig;
  bad_len_cfg.key_length = 47;
  otcrypto_blinded_key_t bad_priv_len = {
      .config = bad_len_cfg,
      .keyblob_length = 112,
      .keyblob = priv_keyblob,
  };
  bad_priv_len.checksum = integrity_blinded_checksum(&bad_priv_len);
  CHECK(otcrypto_ecdh_p384_keygen(&bad_priv_len, &valid_pub).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdh_p384_keygen_async_start(&bad_priv_len).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdh_p384_keygen_async_finalize(&bad_priv_len, &valid_pub)
            .value != OTCRYPTO_OK.value);

  // Bad keyblob length
  otcrypto_blinded_key_t bad_priv_blob_len = {
      .config = kEcdhPrivateKeyConfig,
      .keyblob_length = 111,  // Should be 112
      .keyblob = priv_keyblob,
  };
  bad_priv_blob_len.checksum = integrity_blinded_checksum(&bad_priv_blob_len);
  CHECK(otcrypto_ecdh_p384_keygen(&bad_priv_blob_len, &valid_pub).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdh_p384_keygen_async_start(&bad_priv_blob_len).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdh_p384_keygen_async_finalize(&bad_priv_blob_len, &valid_pub)
            .value != OTCRYPTO_OK.value);

  // Bad hardware backed configuration
  otcrypto_key_config_t bad_hw_cfg = kEcdhPrivateKeyConfig;
  bad_hw_cfg.hw_backed = (hardened_bool_t)0x12345678;  // Invalid boolean
  otcrypto_blinded_key_t bad_priv_hw = {
      .config = bad_hw_cfg,
      .keyblob_length = 112,
      .keyblob = priv_keyblob,
  };
  bad_priv_hw.checksum = integrity_blinded_checksum(&bad_priv_hw);
  CHECK(otcrypto_ecdh_p384_keygen(&bad_priv_hw, &valid_pub).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdh_p384_keygen_async_start(&bad_priv_hw).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdh_p384_keygen_async_finalize(&bad_priv_hw, &valid_pub)
            .value != OTCRYPTO_OK.value);

  // ECDH shared secret negative tests

  // Null pointers
  CHECK(otcrypto_ecdh_p384(NULL, &valid_pub, &valid_shared).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdh_p384_async_start(NULL, &valid_pub).value !=
        OTCRYPTO_OK.value);

  CHECK(otcrypto_ecdh_p384(&valid_priv, NULL, &valid_shared).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdh_p384_async_start(&valid_priv, NULL).value !=
        OTCRYPTO_OK.value);

  CHECK(otcrypto_ecdh_p384(&valid_priv, &valid_pub, NULL).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdh_p384_async_finalize(NULL).value != OTCRYPTO_OK.value);

  // Bad private key checksum
  otcrypto_blinded_key_t bad_priv_chk = {
      .config = kEcdhPrivateKeyConfig,
      .keyblob_length = 112,
      .keyblob = priv_keyblob,
  };
  bad_priv_chk.checksum = valid_priv.checksum ^ 0xFFFFFFFF;
  CHECK(otcrypto_ecdh_p384(&bad_priv_chk, &valid_pub, &valid_shared).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdh_p384_async_start(&bad_priv_chk, &valid_pub).value !=
        OTCRYPTO_OK.value);

  // Bad public key checksum
  otcrypto_unblinded_key_t bad_pub_chk = {
      .key_mode = kOtcryptoKeyModeEcdhP384,
      .key_length = 96,
      .key = pub_key_data,
  };
  bad_pub_chk.checksum = valid_pub.checksum ^ 0xFFFFFFFF;
  CHECK(otcrypto_ecdh_p384(&valid_priv, &bad_pub_chk, &valid_shared).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdh_p384_async_start(&valid_priv, &bad_pub_chk).value !=
        OTCRYPTO_OK.value);

  // Bad shared secret HW backed
  otcrypto_key_config_t bad_shared_hw_cfg = kEcdhSharedKeyConfig;
  bad_shared_hw_cfg.hw_backed = kHardenedBoolTrue;
  otcrypto_blinded_key_t bad_shared_hw = {
      .config = bad_shared_hw_cfg,
      .keyblob_length = sizeof(shared_keyblob),
      .keyblob = shared_keyblob,
  };
  bad_shared_hw.checksum = integrity_blinded_checksum(&bad_shared_hw);
  CHECK(otcrypto_ecdh_p384(&valid_priv, &valid_pub, &bad_shared_hw).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdh_p384_async_finalize(&bad_shared_hw).value !=
        OTCRYPTO_OK.value);

  // Bad shared secret length
  otcrypto_key_config_t bad_sym_len_cfg = kEcdhSharedKeyConfig;
  bad_sym_len_cfg.key_length = 47;
  otcrypto_blinded_key_t bad_shared_len = {
      .config = bad_sym_len_cfg,
      .keyblob_length = sizeof(shared_keyblob),
      .keyblob = shared_keyblob,
  };
  bad_shared_len.checksum = integrity_blinded_checksum(&bad_shared_len);
  CHECK(otcrypto_ecdh_p384(&valid_priv, &valid_pub, &bad_shared_len).value !=
        OTCRYPTO_OK.value);
  CHECK(otcrypto_ecdh_p384_async_finalize(&bad_shared_len).value !=
        OTCRYPTO_OK.value);

  otcrypto_key_config_t bad_ecdh_mode_cfg = kEcdhPrivateKeyConfig;
  bad_ecdh_mode_cfg.key_mode = kOtcryptoKeyModeEcdsaP384;
  otcrypto_blinded_key_t bad_ecdh_mode = {
      .config = bad_ecdh_mode_cfg,
      .keyblob_length = 112,
      .keyblob = priv_keyblob,
  };
  bad_ecdh_mode.checksum = integrity_blinded_checksum(&bad_ecdh_mode);
  CHECK(otcrypto_ecdh_p384_async_start(&bad_ecdh_mode, &valid_pub).value !=
        OTCRYPTO_OK.value);

  otcrypto_key_config_t bad_ecdh_hw_cfg = kEcdhPrivateKeyConfig;
  bad_ecdh_hw_cfg.hw_backed = (hardened_bool_t)0xFFFFFFFF;  // invalid value
  otcrypto_blinded_key_t bad_ecdh_hw = {
      .config = bad_ecdh_hw_cfg,
      .keyblob_length = 112,
      .keyblob = priv_keyblob,
  };
  bad_ecdh_hw.checksum = integrity_blinded_checksum(&bad_ecdh_hw);
  CHECK(otcrypto_ecdh_p384_async_start(&bad_ecdh_hw, &valid_pub).value !=
        OTCRYPTO_OK.value);

  otcrypto_blinded_key_t bad_shared_blob_len = {
      .config = kEcdhSharedKeyConfig,
      .keyblob_length = sizeof(shared_keyblob) - 4,  // Off by one word
      .keyblob = valid_shared.keyblob,
  };
  bad_shared_blob_len.checksum =
      integrity_blinded_checksum(&bad_shared_blob_len);
  CHECK(otcrypto_ecdh_p384_async_finalize(&bad_shared_blob_len).value !=
        OTCRYPTO_OK.value);

  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

  status_t err = key_exchange_test();
  if (!status_ok(err)) {
    // If there was an error, print the OTBN error bits and instruction count.
    LOG_INFO("OTBN error bits: 0x%08x", otbn_err_bits_get());
    LOG_INFO("OTBN instruction count: 0x%08x", otbn_instruction_count_get());
    CHECK_STATUS_OK(err);
    return false;
  }

  err = run_ecdh_negative_tests();
  if (!status_ok(err)) {
    CHECK_STATUS_OK(err);
    return false;
  }

  return true;
}
