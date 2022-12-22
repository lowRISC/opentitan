// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/kmac.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/kmac_test_vectors.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/hash.h"
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
    LOG_INFO("Testing internal KMAC driver API #%d", i);
    current_test_vector = nist_kmac_vectors[i];

    crypto_const_uint8_buf_t input_buf;
    input_buf.data = current_test_vector->input_str;
    input_buf.len = current_test_vector->input_str_len;

    crypto_const_uint8_buf_t func_name;
    func_name.data = current_test_vector->func_name;
    func_name.len = current_test_vector->func_name_len;

    crypto_const_uint8_buf_t cust_str;
    cust_str.data = current_test_vector->custom_str;
    cust_str.len = current_test_vector->custom_str_len;

    crypto_uint8_buf_t digest_buf;
    digest_buf.data = digest;
    digest_buf.len = current_test_vector->digest_len;

    err = kmac_init(current_test_vector->operation,
                    current_test_vector->security_str);
    CHECK(err == kKmacOk);

    if (current_test_vector->operation == kKmacOperationKMAC) {
      err = kmac_write_key_block(current_test_vector->key,
                                 current_test_vector->key_len);
      CHECK(err == kKmacOk);
    }

    if (current_test_vector->operation == kKmacOperationKMAC ||
        current_test_vector->operation == kKmacOperationCSHAKE) {
      err = kmac_write_prefix_block(current_test_vector->operation, func_name,
                                    cust_str);
      CHECK(err == kKmacOk);
    }

    err = kmac_process_msg_blocks(current_test_vector->operation, input_buf,
                                  &digest_buf);

    CHECK(err == kKmacOk);
    CHECK_ARRAYS_EQ(current_test_vector->digest, digest_buf.data,
                    current_test_vector->digest_len);
  }

  // Below we repeat some of the test above, but through higher-level
  // cryptolib API. The gist is to test if glueing is done correctly.
  for (i = 0; i < nist_kmac_nr_of_vectors; i++) {
    current_test_vector = nist_kmac_vectors[i];
    // Skip CSHAKE and KMAC because they are not connected yet
    if (current_test_vector->operation == kKmacOperationCSHAKE ||
        current_test_vector->operation == kKmacOperationKMAC) {
      continue;
    }

    LOG_INFO("Testing cryptolib API (glueing) #%d", i);
    hash_mode_t hash_mode;
    xof_mode_t xof_mode;

    crypto_const_uint8_buf_t input_buf = {
        .data = current_test_vector->input_str,
        .len = current_test_vector->input_str_len,
    };

    crypto_uint8_buf_t digest_buf = {
        .data = digest,
        .len = current_test_vector->digest_len,
    };

    crypto_uint8_buf_t func_name = {
        .data = current_test_vector->func_name,
        .len = current_test_vector->func_name_len,
    };

    crypto_uint8_buf_t cust_str = {
        .data = current_test_vector->custom_str,
        .len = current_test_vector->custom_str_len,
    };

    switch (current_test_vector->security_str) {
      case kKmacSecurityStrength128:
        xof_mode = kXofModeSha3Shake128;
        break;
      case kKmacSecurityStrength224:
        hash_mode = kHashModeSha3_224;
        break;
      case kKmacSecurityStrength256:
        xof_mode = kXofModeSha3Shake256;
        hash_mode = kHashModeSha3_256;
        break;
      case kKmacSecurityStrength384:
        hash_mode = kHashModeSha3_384;
        break;
      case kKmacSecurityStrength512:
        hash_mode = kHashModeSha3_512;
        break;
      default:
        return false;
    }

    crypto_status_t err_status;
    switch (current_test_vector->operation) {
      case kKmacOperationSHAKE:
        err_status = otcrypto_xof(input_buf, xof_mode, func_name, cust_str,
                                  digest_buf.len, &digest_buf);
        break;
      case kKmacOperationSHA3:
        err_status = otcrypto_hash(input_buf, hash_mode, &digest_buf);
        break;
      default:
        return false;
    }

    CHECK(err_status == kCryptoStatusOK);
    CHECK_ARRAYS_EQ(current_test_vector->digest, digest_buf.data,
                    current_test_vector->digest_len);
  }

  return true;
}
