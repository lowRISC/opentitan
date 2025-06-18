// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/drivers/kmac.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/kmac.h"
#include "sw/device/lib/crypto/include/sha3.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// The autogen rule that creates this header creates it in a directory named
// after the rule, then manipulates the include path in the
// cc_compilation_context to include that directory, so the compiler will find
// the version of this file matching the Bazel rule under test.
#include "kmac_testvectors.h"

#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

// Global pointer to the current test vector.
static kmac_test_vector_t *current_test_vector = NULL;

/**
 * Get the mode for SHAKE based on the security strength.
 *
 * @param security_str Security strength (in bits).
 * @param[out] mode SHAKE mode enum value.
 */
status_t get_shake_mode(size_t security_strength, otcrypto_hash_mode_t *mode) {
  switch (security_strength) {
    case 128:
      *mode = kOtcryptoHashXofModeShake128;
      break;
    case 256:
      *mode = kOtcryptoHashXofModeShake256;
      break;
    default:
      LOG_INFO("Invalid security strength for SHAKE: %d bits",
               security_strength);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}

/**
 * Get the mode for cSHAKE based on the security strength.
 *
 * @param security_str Security strength (in bits).
 * @param[out] mode cSHAKE mode enum value.
 */
status_t get_cshake_mode(size_t security_strength, otcrypto_hash_mode_t *mode) {
  switch (security_strength) {
    case 128:
      *mode = kOtcryptoHashXofModeCshake128;
      break;
    case 256:
      *mode = kOtcryptoHashXofModeCshake256;
      break;
    default:
      LOG_INFO("Invalid security strength for cSHAKE: %d bits",
               security_strength);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}

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
 * Call SHA3 to compute the digest.
 *
 * Should only be called when `current_test_vector` is a SHA3 operation.
 *
 * @param[out] digest Computed digest.
 * @return OK or error.
 */
static status_t run_sha3(otcrypto_hash_digest_t *digest) {
  switch (current_test_vector->security_strength) {
    case 224:
      return otcrypto_sha3_224(current_test_vector->input_msg, digest);
    case 256:
      return otcrypto_sha3_256(current_test_vector->input_msg, digest);
    case 384:
      return otcrypto_sha3_384(current_test_vector->input_msg, digest);
    case 512:
      return otcrypto_sha3_512(current_test_vector->input_msg, digest);
    default:
      break;
  }
  LOG_ERROR("Invalid strength for SHA3: %d bits",
            current_test_vector->security_strength);
  return INVALID_ARGUMENT();
}

/**
 * Call SHAKE to compute the digest.
 *
 * Should only be called when `current_test_vector` is a SHAKE operation.
 *
 * @param[out] digest Computed digest.
 * @return OK or error.
 */
static status_t run_shake(otcrypto_hash_digest_t *digest) {
  switch (current_test_vector->security_strength) {
    case 128:
      return otcrypto_shake128(current_test_vector->input_msg, digest);
    case 256:
      return otcrypto_shake256(current_test_vector->input_msg, digest);
    default:
      break;
  }
  LOG_ERROR("Invalid strength for SHAKE: %d bits",
            current_test_vector->security_strength);
  return INVALID_ARGUMENT();
}

/**
 * Call cSHAKE to compute the digest.
 *
 * Should only be called when `current_test_vector` is a cSHAKE operation.
 *
 * @param[out] digest Computed digest.
 * @return OK or error.
 */
static status_t run_cshake(otcrypto_hash_digest_t *digest) {
  switch (current_test_vector->security_strength) {
    case 128:
      return otcrypto_cshake128(current_test_vector->input_msg,
                                current_test_vector->func_name,
                                current_test_vector->cust_str, digest);
    case 256:
      return otcrypto_cshake256(current_test_vector->input_msg,
                                current_test_vector->func_name,
                                current_test_vector->cust_str, digest);
    default:
      break;
  }
  LOG_ERROR("Invalid strength for cSHAKE: %d bits",
            current_test_vector->security_strength);
  return INVALID_ARGUMENT();
}

/**
 * Call KMAC to compute the authentication tag.
 *
 * Should only be called when `current_test_vector` is a KMAC operation.
 *
 * @param[out] tag Computed tag (digest).
 * @return OK or error.
 */
static status_t run_kmac(otcrypto_word32_buf_t tag) {
  current_test_vector->key.checksum =
      integrity_blinded_checksum(&current_test_vector->key);
  return otcrypto_kmac(
      &current_test_vector->key, current_test_vector->input_msg,
      current_test_vector->cust_str, current_test_vector->digest.len, tag);
}

/**
 * Run the test pointed to by `current_test_vector`.
 */
static status_t run_test_vector(void) {
  size_t digest_num_words = current_test_vector->digest.len / sizeof(uint32_t);
  if (current_test_vector->digest.len % sizeof(uint32_t) != 0) {
    digest_num_words++;
  }
  uint32_t digest_data[digest_num_words];
  otcrypto_hash_digest_t digest = {
      .data = digest_data,
      .len = digest_num_words,
  };

  switch (current_test_vector->test_operation) {
    case kKmacTestOperationShake: {
      run_shake(&digest);
      break;
    }
    case kKmacTestOperationCshake: {
      run_cshake(&digest);
      break;
    }
    case kKmacTestOperationSha3: {
      run_sha3(&digest);
      break;
    }
    case kKmacTestOperationKmac: {
      otcrypto_word32_buf_t tag_buf = {
          .data = digest.data,
          .len = digest.len,
      };
      run_kmac(tag_buf);
      break;
    }
    default: {
      LOG_INFO("Unrecognized `operation` field: 0x%04x",
               current_test_vector->test_operation);
      return INVALID_ARGUMENT();
    }
  }

  TRY_CHECK_ARRAYS_EQ((unsigned char *)digest.data,
                      current_test_vector->digest.data,
                      current_test_vector->digest.len);
  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();
bool test_main(void) {
  LOG_INFO("Testing cryptolib KMAC driver.");

  // Initialize the core with default parameters
  CHECK_STATUS_OK(entropy_complex_init());
  CHECK_STATUS_OK(kmac_hwip_default_configure());

  status_t test_result = OK_STATUS();
  for (size_t i = 0; i < ARRAYSIZE(kKmacTestVectors); i++) {
    current_test_vector = &kKmacTestVectors[i];
    LOG_INFO("Running test %d of %d, test vector identifier: %s", i + 1,
             ARRAYSIZE(kKmacTestVectors),
             current_test_vector->vector_identifier);
    EXECUTE_TEST(test_result, run_test_vector);
  }
  return status_ok(test_result);
}
