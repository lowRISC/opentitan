// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/drivers/kmac.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/hash.h"
#include "sw/device/lib/crypto/include/mac.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

// Most fields of the following structs are not used during sideload testing
// but they are copied over from KMAC testing for consistency. Later, we can
// merge the sideload and non-sideload testing if required. Normally, these two
// structs would be defined by "kmac_testvectors.h" generated automatically by
// a Bazel rule.
typedef enum kmac_test_operation_t {
  kKmacTestOperationCshake,
  kKmacTestOperationShake,
  kKmacTestOperationSha3,
  kKmacTestOperationKmac,
} kmac_test_operation_t;

typedef struct kmac_test_vector {
  char *vector_identifier;
  kmac_test_operation_t test_operation;
  size_t security_strength;
  otcrypto_blinded_key_t key;
  otcrypto_const_byte_buf_t input_msg;
  otcrypto_const_byte_buf_t func_name;
  otcrypto_const_byte_buf_t cust_str;
  otcrypto_const_byte_buf_t digest;
} kmac_test_vector_t;

// Note that since the following vectors are used for sideloading, the digest
// result is irrelevant.
static kmac_test_vector_t kKmacTestVectors[] = {
    {
        .vector_identifier = "Manually edited sample #1",
        .security_strength = 128,
        .key =
            {
                .config =
                    {
                        .key_mode = kOtcryptoKeyModeKmac128,
                        .key_length = kKmacSideloadKeyLength / 8,
                        .hw_backed = kHardenedBoolTrue,
                        .exportable = kHardenedBoolFalse,
                        .security_level = kOtcryptoKeySecurityLevelHigh,
                    },
                .keyblob_length = 32,
                .keyblob =
                    (uint32_t[]){
                        0x00000001,
                        0x47464544,
                        0x4b4a4948,
                        0x4f4e4d4c,
                        0x53525150,
                        0x57565554,
                        0x5b5a5958,
                        0x5f5e5d5c,
                    },
            },
        .input_msg =
            {
                .data =
                    (uint8_t[]){
                        0xf5, 0xb1, 0x65, 0x22, 0x4a, 0x58, 0xb7, 0x91,
                        0xdf, 0x6a, 0xf1, 0xd8, 0x30, 0x3e, 0x61, 0xcd,
                        0xc4, 0xbb, 0x86, 0xc3, 0xd1, 0xc4, 0x27, 0x10,
                        0x3c, 0x34, 0x4c, 0x41, 0x89, 0xeb, 0x2f, 0x1e,
                    },
                .len = 32,
            },
        .cust_str =
            {
                .data =
                    (uint8_t[]){
                        0x7b, 0xd5, 0xd4, 0x7e, 0x44, 0x6f, 0xce, 0xc2,
                        0xa3, 0xd8, 0x11, 0x73, 0x61, 0x10, 0xe5, 0x78,
                        0x1b, 0xcc, 0xce, 0xa6, 0x96, 0x76, 0x2e, 0x61,
                        0x16, 0xc6, 0xe9, 0xc9, 0x2d, 0x99, 0xbf, 0x35,
                    },
                .len = 32,
            },
        .digest =
            {
                // `data` field does not matter because this is a sideload test
                // vector.
                .len = 20,
            },
    },
    {
        .vector_identifier = "Manually edited sample #2",
        .security_strength = 256,
        .key =
            {
                .config =
                    {
                        .key_mode = kOtcryptoKeyModeKmac256,
                        .key_length = kKmacSideloadKeyLength / 8,
                        .hw_backed = kHardenedBoolTrue,
                        .exportable = kHardenedBoolFalse,
                        .security_level = kOtcryptoKeySecurityLevelHigh,
                    },
                .keyblob_length = 32,
                .keyblob =
                    (uint32_t[]){
                        0x00000002,
                        0x11111111,
                        0x4b4a4948,
                        0x4f4e4d4c,
                        0x53525150,
                        0x57565554,
                        0x5b5a5958,
                        0xffffffff,
                    },
            },
        .input_msg =
            {
                .data =
                    (uint8_t[]){
                        0xf5,
                        0xb1,
                        0x65,
                        0x22,
                        0x4a,
                        0x58,
                        0xb7,
                        0x91,
                        0xdf,
                        0x6a,
                        0xf1,
                        0xd8,
                        0x30,
                        0x3e,
                        0x61,
                        0xcd,
                    },
                .len = 16,
            },
        .cust_str =
            {
                .data =
                    (uint8_t[]){
                        0x7b,
                        0xd5,
                        0xd4,
                        0x7e,
                        0x44,
                        0x6f,
                        0xce,
                        0xc2,
                        0xa3,
                        0xd8,
                        0x11,
                        0x73,
                        0x61,
                        0x10,
                        0xe5,
                        0x78,
                    },
                .len = 16,
            },
        .digest =
            {
                // `data` field does not matter because this is a sideload test
                // vector.
                .len = 32,
            },
    },
    {
        .vector_identifier = "Manually edited sample #3",
        .security_strength = 128,
        .key =
            {
                .config =
                    {
                        .key_mode = kOtcryptoKeyModeKmac128,
                        .key_length = kKmacSideloadKeyLength / 8,
                        .hw_backed = kHardenedBoolTrue,
                        .exportable = kHardenedBoolFalse,
                        .security_level = kOtcryptoKeySecurityLevelHigh,
                    },
                .keyblob_length = 32,
                .keyblob =
                    (uint32_t[]){
                        0x00000001,
                        0x00000000,
                        0x00000000,
                        0x00000000,
                        0x00000000,
                        0x00000000,
                        0x00000000,
                        0x0000000f,
                    },
            },
        .input_msg =
            {
                .data = (uint8_t[]){0xf5, 0xb1, 0x65, 0x22},
                .len = 4,
            },
        .cust_str =
            {
                .data = (uint8_t[]){0x7b, 0xd5, 0xd4, 0x7e},
                .len = 4,
            },
        .digest =
            {
                // `data` field does not matter because this is a sideload test
                // vector.
                .len = 16,
            },
    },
};

// We use the following SHA-3 vector between 2 sideload executions in order to
// clear internal KMAC engine.
static kmac_test_vector_t sha3_test_vector = {
    .vector_identifier =
        "NIST CAVP, byte-oriented, SHA3_224ShortMsg.rsp, Len = 8",
    .test_operation = kKmacTestOperationSha3,
    .security_strength = 224,
    .input_msg =
        {
            .data =
                (uint8_t[]){
                    0x01,
                },
            .len = 1,
        },
    .func_name =
        {
            .data = NULL,
            .len = 0,
        },
    .cust_str =
        {
            .data = NULL,
            .len = 0,
        },
    .digest =
        {
            .data =
                (uint8_t[]){
                    0x48, 0x82, 0x86, 0xd9, 0xd3, 0x27, 0x16, 0xe5, 0x88, 0x1e,
                    0xa1, 0xee, 0x51, 0xf3, 0x6d, 0x36, 0x60, 0xd7, 0x0f, 0x0d,
                    0xb0, 0x3b, 0x3f, 0x61, 0x2c, 0xe9, 0xed, 0xa4,
                },
            .len = 28,
        },
};

// Global pointer to the current test vector.
static kmac_test_vector_t *current_test_vector = NULL;

/**
 * Get the mode for SHA3 based on the security strength.
 *
 * @param security_str Security strength (in bits).
 * @param[out] mode Hash mode enum value.
 */
status_t get_sha3_mode(size_t security_strength, otcrypto_hash_mode_t *mode) {
  switch (security_strength) {
    case 224:
      *mode = kOtcryptoHashModeSha3_224;
      break;
    case 256:
      *mode = kOtcryptoHashModeSha3_256;
      break;
    case 384:
      *mode = kOtcryptoHashModeSha3_384;
      break;
    case 512:
      *mode = kOtcryptoHashModeSha3_512;
      break;
    default:
      LOG_INFO("Invalid size for SHA3: %d bits", security_strength);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}

/**
 * Get the mode for KMAC based on the security strength.
 *
 * @param security_str Security strength (in bits).
 * @param[out] mode KMAC mode enum value.
 */
status_t get_kmac_mode(size_t security_strength, otcrypto_kmac_mode_t *mode) {
  switch (security_strength) {
    case 128:
      *mode = kOtcryptoKmacModeKmac128;
      break;
    case 256:
      *mode = kOtcryptoKmacModeKmac256;
      break;
    default:
      LOG_INFO("Invalid size for KMAC: %d bits", security_strength);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}

/**
 * Run the test pointed to by `current_test_vector`.
 */
static status_t run_test_vector(void) {
  size_t digest_num_words = current_test_vector->digest.len / sizeof(uint32_t);
  if (current_test_vector->digest.len % sizeof(uint32_t) != 0) {
    digest_num_words++;
  }
  uint32_t digest1[digest_num_words];
  uint32_t digest2[digest_num_words];

  current_test_vector->key.checksum =
      integrity_blinded_checksum(&current_test_vector->key);

  otcrypto_kmac_mode_t mode;
  TRY(get_kmac_mode(current_test_vector->security_strength, &mode));

  otcrypto_word32_buf_t tag_buf1 = {
      .data = digest1,
      .len = ARRAYSIZE(digest1),
  };
  otcrypto_word32_buf_t tag_buf2 = {
      .data = digest2,
      .len = ARRAYSIZE(digest2),
  };

  digest_num_words = sha3_test_vector.digest.len / sizeof(uint32_t);
  if (sha3_test_vector.digest.len % sizeof(uint32_t) != 0) {
    digest_num_words++;
  }
  uint32_t digest3[digest_num_words];

  otcrypto_hash_digest_t digest_buf = {
      .data = digest3,
      .len = ARRAYSIZE(digest3),
  };

  LOG_INFO("Running the first KMAC sideload operation.");
  TRY(otcrypto_kmac(&current_test_vector->key, current_test_vector->input_msg,
                    mode, current_test_vector->cust_str,
                    current_test_vector->digest.len, tag_buf1));

  // Run a SHA-3 operation in between the two KMAC operations.
  LOG_INFO("Running the intermediate SHA3 operation.");
  TRY(get_sha3_mode(sha3_test_vector.security_strength, &digest_buf.mode));
  TRY(otcrypto_hash(sha3_test_vector.input_msg, digest_buf));

  LOG_INFO("Running the second KMAC sideload operation for comparison.");
  TRY(otcrypto_kmac(&current_test_vector->key, current_test_vector->input_msg,
                    mode, current_test_vector->cust_str,
                    current_test_vector->digest.len, tag_buf2));

  TRY_CHECK_ARRAYS_EQ((unsigned char *)tag_buf1.data,
                      (unsigned char *)tag_buf2.data,
                      current_test_vector->digest.len);
  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();
bool test_main(void) {
  // Initialize keymgr and advance to CreatorRootKey state.
  dif_keymgr_t keymgr;
  dif_kmac_t kmac;
  CHECK_STATUS_OK(keymgr_testutils_startup(&keymgr, &kmac));

  CHECK_STATUS_OK(keymgr_testutils_advance_state(&keymgr, &kOwnerIntParams));
  CHECK_STATUS_OK(keymgr_testutils_check_state(
      &keymgr, kDifKeymgrStateOwnerIntermediateKey));
  LOG_INFO("Keymgr entered OwnerIntKey State");
  LOG_INFO("Testing cryptolib KMAC driver with sideloaded key.");

  // Initialize the core with default parameters
  CHECK_STATUS_OK(entropy_complex_init());
  CHECK_STATUS_OK(kmac_hwip_default_configure());

  status_t test_result = OK_STATUS();
  for (size_t i = 0; i < ARRAYSIZE(kKmacTestVectors); i++) {
    // copy version
    current_test_vector = &kKmacTestVectors[i];

    LOG_INFO("Running test %d of %d, test vector identifier: %s", i + 1,
             ARRAYSIZE(kKmacTestVectors),
             current_test_vector->vector_identifier);
    EXECUTE_TEST(test_result, run_test_vector);
  }
  return status_ok(test_result);
}
