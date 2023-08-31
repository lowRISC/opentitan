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
#include "kmac_verify_testvectors.h"

OTTF_DEFINE_TEST_CONFIG();
bool test_main(void) {
  LOG_INFO("Testing cryptolib KMAC driver.");

  // Initialize the core with default parameters
  CHECK_STATUS_OK(kmac_hwip_default_configure());

  for (size_t i = 0; i < ARRAYSIZE(nist_kmac_vectors); i++) {
    kmac_test_vector_t *current_test_vector = &nist_kmac_vectors[i];
    LOG_INFO("loop counter = %d, vector identifier: %s", i,
             current_test_vector->vector_identifier);

    size_t digest_len_words =
        current_test_vector->digest.len / sizeof(uint32_t);
    if (current_test_vector->digest.len % sizeof(uint32_t) != 0) {
      digest_len_words++;
    }
    uint32_t digest[digest_len_words];
    crypto_word_buf_t digest_buf = {
        .data = digest,
        .len = digest_len_words,
    };

    crypto_status_t err_status;
    switch (current_test_vector->test_operation) {
      case kKmacTestOperationXOF:
        err_status = otcrypto_xof(
            current_test_vector->input_msg, current_test_vector->xof_mode,
            current_test_vector->func_name, current_test_vector->cust_str,
            current_test_vector->digest.len, &digest_buf);
        break;
      case kKmacTestOperationHASH:
        err_status = otcrypto_hash(current_test_vector->input_msg,
                                   current_test_vector->hash_mode, &digest_buf);
        break;
      case kKmacTestOperationMAC:
        err_status = otcrypto_kmac(
            &current_test_vector->key, current_test_vector->input_msg,
            current_test_vector->mac_mode, current_test_vector->cust_str,
            current_test_vector->digest.len, &digest_buf);
        break;
      default:
        LOG_INFO("The test vector has undefined `operation` field.");
        return false;
    }

    CHECK_STATUS_OK(err_status);
    CHECK_ARRAYS_EQ((unsigned char *)digest_buf.data,
                    current_test_vector->digest.data,
                    current_test_vector->digest.len);
  }

  return true;
}
