// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/kmac.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/hash.h"
#include "sw/device/lib/crypto/include/mac.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// The autogen rule that creates this header creates it in a directory named
// after the rule, then manipulates the include path in the
// cc_compilation_context to include that directory, so the compiler will find
// the version of this file matching the Bazel rule under test.
#include "kmac_testvectors.h"

// Global pointer to the current test vector.
static kmac_test_vector_t *current_test_vector = NULL;

/**
 * Get the mode for SHAKE based on the security strength.
 *
 * @param security_str Security strength (in bits).
 * @param[out] mode SHAKE mode enum value.
 */
status_t get_shake_mode(size_t security_strength, xof_shake_mode_t *mode) {
  switch (security_strength) {
    case 128:
      *mode = kXofShakeModeShake128;
      break;
    case 256:
      *mode = kXofShakeModeShake256;
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
status_t get_cshake_mode(size_t security_strength, xof_cshake_mode_t *mode) {
  switch (security_strength) {
    case 128:
      *mode = kXofCshakeModeCshake128;
      break;
    case 256:
      *mode = kXofCshakeModeCshake256;
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
status_t get_sha3_mode(size_t security_strength, hash_mode_t *mode) {
  switch (security_strength) {
    case 224:
      *mode = kHashModeSha3_224;
      break;
    case 256:
      *mode = kHashModeSha3_256;
      break;
    case 384:
      *mode = kHashModeSha3_384;
      break;
    case 512:
      *mode = kHashModeSha3_512;
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
status_t get_kmac_mode(size_t security_strength, kmac_mode_t *mode) {
  switch (security_strength) {
    case 128:
      *mode = kMacModeKmac128;
      break;
    case 256:
      *mode = kMacModeKmac256;
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
  uint32_t digest[digest_num_words];
  crypto_word32_buf_t digest_buf = {
      .data = digest,
      .len = digest_num_words,
  };

  switch (current_test_vector->test_operation) {
    case kKmacTestOperationShake: {
      xof_shake_mode_t mode;
      TRY(get_shake_mode(current_test_vector->security_strength, &mode));
      TRY(otcrypto_xof_shake(current_test_vector->input_msg, mode,
                             current_test_vector->digest.len, &digest_buf));
      break;
    }
    case kKmacTestOperationCshake: {
      xof_cshake_mode_t mode;
      TRY(get_cshake_mode(current_test_vector->security_strength, &mode));
      TRY(otcrypto_xof_cshake(current_test_vector->input_msg, mode,
                              current_test_vector->func_name,
                              current_test_vector->cust_str,
                              current_test_vector->digest.len, &digest_buf));
      break;
    }
    case kKmacTestOperationSha3: {
      hash_mode_t mode;
      TRY(get_sha3_mode(current_test_vector->security_strength, &mode));
      TRY(otcrypto_hash(current_test_vector->input_msg, mode, &digest_buf));
      break;
    }
    case kKmacTestOperationKmac: {
      kmac_mode_t mode;
      TRY(get_kmac_mode(current_test_vector->security_strength, &mode));
      TRY(otcrypto_kmac(&current_test_vector->key,
                        current_test_vector->input_msg, mode,
                        current_test_vector->cust_str,
                        current_test_vector->digest.len, &digest_buf));
      break;
    }
    default: {
      LOG_INFO("Unrecognized `operation` field: 0x%04x",
               current_test_vector->test_operation);
      return INVALID_ARGUMENT();
    }
  }

  TRY_CHECK_ARRAYS_EQ((unsigned char *)digest_buf.data,
                      current_test_vector->digest.data,
                      current_test_vector->digest.len);
  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();
bool test_main(void) {
  LOG_INFO("Testing cryptolib KMAC driver.");

  // Initialize the core with default parameters
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
