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

  size_t i = 0;
  for (; i < nist_kmac_nr_of_vectors; i++) {
    LOG_INFO("loop_ctr = %d", i);
    current_test_vector = nist_kmac_vectors[i];

    err = kmac_init(current_test_vector->operation);
    CHECK(err == kKmacOk);

    err = kmac_update(current_test_vector->input_str,
                      current_test_vector->input_str_len, digest,
                      current_test_vector->digest_len);

    CHECK(err == kKmacOk);
    CHECK_ARRAYS_EQ(current_test_vector->digest, digest,
                    current_test_vector->digest_len);
  }

  return true;
}
