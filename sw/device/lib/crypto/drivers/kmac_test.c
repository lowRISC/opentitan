// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/kmac.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/kmac_test_vectors.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

OTTF_DEFINE_TEST_CONFIG();
bool test_main(void) {
  kmac_error_t err;
  // Current the largest digest size is 2000 bits.
  // For test vectors with bigger digest sizes, `digest` buffer needs to be
  // enlarged.
  uint8_t digest[250];
  kmac_test_vector_t *current_test_vector;

  // Initialize the core with default parameters
  err = kmac_hwip_default_configure();
  if (err != kKmacOk) {
    return err;
  }

  size_t i = 0;
  for (; i < nist_kmac_nr_of_vectors; i++) {
    LOG_INFO("test #%d", i);
    current_test_vector = nist_kmac_vectors[i];

    err = kmac_init(
        current_test_vector->operation, current_test_vector->security_str,
        current_test_vector->func_name, current_test_vector->func_name_len,
        current_test_vector->custom_str, current_test_vector->custom_str_len);
    CHECK(err == kKmacOk);

    if (current_test_vector->operation == kKmacOperationKMAC) {
      err = kmac_write_key_block(current_test_vector->key,
                                 current_test_vector->key_len);
      CHECK(err == kKmacOk);
    }

    if (current_test_vector->operation == kKmacOperationKMAC ||
        current_test_vector->operation == kKmacOperationCSHAKE) {
      err = kmac_write_prefix_block(
          current_test_vector->operation, current_test_vector->func_name,
          current_test_vector->func_name_len, current_test_vector->custom_str,
          current_test_vector->custom_str_len);
      CHECK(err == kKmacOk);
    }

    err = kmac_process_msg_blocks(current_test_vector->operation,
                                  current_test_vector->input_str,
                                  current_test_vector->input_str_len, digest,
                                  current_test_vector->digest_len);

    CHECK(err == kKmacOk);
    CHECK_ARRAYS_EQ(current_test_vector->digest, digest,
                    current_test_vector->digest_len);
  }

  return true;
}
