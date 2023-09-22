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
 * Run the test pointed to by `current_test_vector`.
 */
static status_t run_test_vector(void) {
  size_t digest_len_words = current_test_vector->digest.len / sizeof(uint32_t);
  if (current_test_vector->digest.len % sizeof(uint32_t) != 0) {
    digest_len_words++;
  }
  uint32_t digest[digest_len_words];
  crypto_word32_buf_t digest_buf = {
      .data = digest,
      .len = digest_len_words,
  };

  switch (current_test_vector->test_operation) {
    case kKmacTestOperationXOF: {
      TRY(otcrypto_xof(
          current_test_vector->input_msg, current_test_vector->xof_mode,
          current_test_vector->func_name, current_test_vector->cust_str,
          current_test_vector->digest.len, &digest_buf));
      break;
    }
    case kKmacTestOperationHASH: {
      TRY(otcrypto_hash(current_test_vector->input_msg,
                        current_test_vector->hash_mode, &digest_buf));
      break;
    }
    case kKmacTestOperationMAC: {
      TRY(otcrypto_kmac(
          &current_test_vector->key, current_test_vector->input_msg,
          current_test_vector->mac_mode, current_test_vector->cust_str,
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
