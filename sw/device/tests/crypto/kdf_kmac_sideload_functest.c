// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/drivers/kmac.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/hash.h"
#include "sw/device/lib/crypto/include/kdf.h"
#include "sw/device/lib/crypto/include/mac.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

// Most fields of the following structs are not used during sideload testing
// but they are copied over from KDF-KMAC testing for consistency. Later, we can
// merge the sideload and non-sideload testing if required. Normally, these two
// structs would be defined by "kdf_testvectors.h" generated automatically by
// a Bazel rule.
typedef enum kdf_test_operation_t {
  kKdfTestOperationKmac128,
  kKdfTestOperationKmac256,
} kdf_test_operation_t;

typedef struct kdf_test_vector {
  char *vector_identifier;
  kdf_test_operation_t test_operation;
  otcrypto_blinded_key_t key_derivation_key;
  otcrypto_const_byte_buf_t label;
  otcrypto_const_byte_buf_t context;
  otcrypto_blinded_key_t keying_material;
} kdf_kmac_test_vector_t;

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

// Note that since the following vectors are used for sideloading, the resulting
// `keying_material` result is irrelevant. Only its length is used as input.
static kdf_kmac_test_vector_t kKdfTestVectors[] = {
    {
        .vector_identifier = "Manually edited KDF-KMAC sample #1",
        .test_operation = kKdfTestOperationKmac128,
        .key_derivation_key =
            {
                .config =
                    {
                        .key_mode = kOtcryptoKeyModeKdfKmac128,
                        .key_length = 32,
                        .hw_backed = kHardenedBoolTrue,
                        .security_level = kOtcryptoKeySecurityLevelLow,
                        .exportable = kHardenedBoolFalse,
                    },
                .keyblob_length = 32,
                .keyblob =
                    (uint32_t[]){
                        0x00000002,
                        0xa0d0e9b4,
                        0x7e790e8b,
                        0x2ed764b2,
                        0x7ad25f92,
                        0x4ba41700,
                        0x75553000,
                        0xe3089c7a,
                    },
            },
        .context =
            {
                .data =
                    (uint8_t[]){
                        0x5f,
                        0x67,
                        0x2e,
                    },
                .len = 3,
            },
        .label =
            {
                .data =
                    (uint8_t[]){
                        0xdc, 0xd5, 0x70, 0x1f, 0x22, 0x83, 0x53,
                        0xa9, 0xc7, 0x3a, 0xe6, 0x72, 0x65, 0xb4,
                        0xa5, 0x55, 0x84, 0xa0, 0x4f, 0x3d, 0x62,
                        0x2b, 0xac, 0x32, 0x69, 0x8f, 0xb0, 0xf3,
                    },
                .len = 28,
            },
        .keying_material =
            {
                // other fields of `keying_material` is not used, since it is
                // not
                // directy passed to KDF-KMAC function.
                .config =
                    {
                        .key_length = 24,
                    },
            },
    },
    {
        .vector_identifier = "Manually edited KDF-KMAC sample #2",
        .test_operation = kKdfTestOperationKmac128,
        .key_derivation_key =
            {
                .config =
                    {
                        .key_mode = kOtcryptoKeyModeKdfKmac128,
                        .key_length = 32,
                        .hw_backed = kHardenedBoolTrue,
                        .security_level = kOtcryptoKeySecurityLevelHigh,
                        .exportable = kHardenedBoolFalse,
                    },
                .keyblob_length = 32,
                .keyblob =
                    (uint32_t[]){
                        0x0000000f,
                        0x1600a35a,
                        0x6f03675a,
                        0x6b0d549b,
                        0x11e20b8f,
                        0x3d9c1724,
                        0x1738f7d9,
                        0x8d116ece,
                    },
            },
        .context =
            {
                .data =
                    (uint8_t[]){
                        0xfe,
                        0x55,
                        0x18,
                        0xcb,
                        0xe8,
                        0xdf,
                        0xe5,
                        0x92,
                        0x96,
                        0x94,
                        0x6b,
                        0xd2,
                        0x35,
                        0xa0,
                        0x14,
                    },
                .len = 15,
            },
        .label =
            {
                .data =
                    (uint8_t[]){
                        0xbe,
                        0x3a,
                        0x2b,
                        0x7c,
                        0x73,
                        0xa4,
                        0x20,
                        0xc3,
                        0x39,
                        0xa0,
                        0xf9,
                        0x42,
                        0x37,
                        0x37,
                        0x6d,
                        0x09,
                    },
                .len = 16,
            },
        .keying_material =
            {
                // other fields of `keying_material` is not used, since it is
                // not
                // directy passed to KDF-KMAC function.
                .config =
                    {
                        .key_length = 32,
                    },
            },
    },
    {
        .vector_identifier = "Manually edited KDF-KMAC sample #3",
        .test_operation = kKdfTestOperationKmac256,
        .key_derivation_key =
            {
                .config =
                    {
                        .key_mode = kOtcryptoKeyModeKdfKmac256,
                        .key_length = 32,
                        .hw_backed = kHardenedBoolTrue,
                        .security_level = kOtcryptoKeySecurityLevelHigh,
                        .exportable = kHardenedBoolFalse,
                    },
                .keyblob_length = 32,
                .keyblob =
                    (uint32_t[]){
                        0x00000001,
                        0xe5f6db1d,
                        0x9acd8acd,
                        0x14b044d7,
                        0x558298e2,
                        0x8de4ab47,
                        0xefb6fbfe,
                        0x9ddcc6f8,
                    },
            },
        .context =
            {
                .data =
                    (uint8_t[]){
                        0x6e, 0xa6, 0x87, 0x76, 0x6e, 0xac, 0xfb,
                        0x9c, 0xf0, 0x5e, 0x91, 0x5f, 0xfc, 0xeb,
                        0x62, 0x44, 0x51, 0x77, 0x23,
                    },
                .len = 19,
            },
        .label =
            {
                .data =
                    (uint8_t[]){
                        0x07, 0x32, 0xa7, 0x2f, 0x55, 0xff, 0xd6, 0xdd,
                        0x5e, 0x83, 0x38, 0xad, 0x50, 0xba, 0xa5, 0x01,
                        0x36, 0x80, 0x9c, 0x56, 0x53, 0xb6, 0x80,
                    },
                .len = 23,
            },
        .keying_material =
            {
                // other fields of `keying_material` is not used, since it is
                // not
                // directy passed to KDF-KMAC function.
                .config =
                    {
                        .key_length = 64,
                    },
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
static kdf_kmac_test_vector_t *current_test_vector = NULL;

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
 * Get the mode for KMAC based on test operation.
 *
 * @param test_operation Security strength of KMAC.
 * @param[out] mode KMAC mode enum value.
 */
status_t get_kmac_mode(kdf_test_operation_t test_operation,
                       otcrypto_kmac_mode_t *mode) {
  switch (test_operation) {
    case kKdfTestOperationKmac128:
      *mode = kOtcryptoKmacModeKmac128;
      break;
    case kKdfTestOperationKmac256:
      *mode = kOtcryptoKmacModeKmac256;
      break;
    default:
      LOG_INFO("Invalid test operation is given for KDF-KMAC");
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}

/**
 * Run the test pointed to by `current_test_vector`.
 */
static status_t run_test_vector(void) {
  // Below, `km` prefix refers to keying_material, and
  // `kdk` prefix refers to key derivation key
  size_t km_key_len = current_test_vector->keying_material.config.key_length;
  size_t km_keyblob_len =
      keyblob_num_words(current_test_vector->keying_material.config);
  uint32_t km_buffer1[km_keyblob_len];
  uint32_t km_buffer2[km_keyblob_len];

  current_test_vector->key_derivation_key.checksum =
      integrity_blinded_checksum(&current_test_vector->key_derivation_key);

  otcrypto_kmac_mode_t mode;
  TRY(get_kmac_mode(current_test_vector->test_operation, &mode));

  otcrypto_key_config_t km_config = {
      // The following key_mode is a dummy placeholder. It does not
      // necessarily match the `key_length`.
      .key_mode = kOtcryptoKeyModeKdfKmac128,
      .key_length = km_key_len,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelHigh,
      .exportable = kHardenedBoolFalse,
  };

  otcrypto_blinded_key_t keying_material1 = {
      .config = km_config,
      .keyblob = km_buffer1,
      .keyblob_length = km_keyblob_len * sizeof(uint32_t),
  };

  otcrypto_blinded_key_t keying_material2 = {
      .config = km_config,
      .keyblob = km_buffer2,
      .keyblob_length = km_keyblob_len * sizeof(uint32_t),
  };

  size_t digest_num_words = sha3_test_vector.digest.len / sizeof(uint32_t);
  if (sha3_test_vector.digest.len % sizeof(uint32_t) != 0) {
    digest_num_words++;
  }
  uint32_t digest[digest_num_words];

  otcrypto_hash_digest_t digest_buf = {
      .data = digest,
      .len = ARRAYSIZE(digest),
  };

  LOG_INFO("Running the first KDF-KMAC sideload operation.");
  TRY(otcrypto_kdf_kmac(
      current_test_vector->key_derivation_key, mode, current_test_vector->label,
      current_test_vector->context, km_key_len, &keying_material1));

  // Run a SHA-3 operation in between the two KMAC operations.
  LOG_INFO("Running the intermediate SHA3 operation.");
  TRY(get_sha3_mode(sha3_test_vector.security_strength, &digest_buf.mode));
  TRY(otcrypto_hash(sha3_test_vector.input_msg, digest_buf));

  LOG_INFO("Running the second KDF-KMAC sideload operation for comparison.");
  TRY(otcrypto_kdf_kmac(
      current_test_vector->key_derivation_key, mode, current_test_vector->label,
      current_test_vector->context, km_key_len, &keying_material2));

  TRY_CHECK_ARRAYS_EQ((unsigned char *)keying_material1.keyblob,
                      (unsigned char *)keying_material2.keyblob, km_key_len);
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
  LOG_INFO("Testing cryptolib KDF-KMAC driver with sideloaded key.");

  // Initialize the core with default parameters
  CHECK_STATUS_OK(entropy_complex_init());
  CHECK_STATUS_OK(kmac_hwip_default_configure());

  status_t test_result = OK_STATUS();
  for (size_t i = 0; i < ARRAYSIZE(kKdfTestVectors); i++) {
    // copy version
    current_test_vector = &kKdfTestVectors[i];

    LOG_INFO("Running test %d of %d, test vector identifier: %s", i + 1,
             ARRAYSIZE(kKdfTestVectors),
             current_test_vector->vector_identifier);
    EXECUTE_TEST(test_result, run_test_vector);
  }
  return status_ok(test_result);
}
