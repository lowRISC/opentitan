// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/kmac.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/kmac_test_vectors.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/hash.h"
#include "sw/device/lib/crypto/include/mac.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Use this as the second share of the key. We need 512-bit for the max key
// size.
static const uint32_t kZeroVector[512 / 32] = {0};

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

    kmac_blinded_key_t kmac_key = {
        .share0 = (uint32_t *)current_test_vector->key,
        .share1 = kZeroVector,
        .len = current_test_vector->key_len,
    };

    err = kmac_init(current_test_vector->operation,
                    current_test_vector->security_str);
    CHECK(err == kKmacOk);

    if (current_test_vector->operation == kKmacOperationKMAC) {
      err = kmac_write_key_block(&kmac_key);
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
    LOG_INFO("Testing cryptolib API (glueing) #%d", i);
    current_test_vector = nist_kmac_vectors[i];

    hash_mode_t hash_mode;
    xof_mode_t xof_mode;
    mac_mode_t mac_mode;

    // Reserve keyblob large enough to accommodate:
    // 1) Key with max size (512 bits)
    // 2) Both shares of this key (hence, 2 * 512)
    uint32_t keyblob[2 * 512 / 32];

    for (size_t j = 0; j < current_test_vector->key_len / 2; j++) {
      keyblob[j] =
          j < current_test_vector->key_len / 4
              ? read_32(current_test_vector->key + sizeof(uint32_t) * j)
              : 0;
    }

    crypto_blinded_key_t key = {
        .config =
            {
                .key_mode = current_test_vector->security_str ==
                                    kKmacSecurityStrength128
                                ? kKeyModeKmac128
                                : kKeyModeKmac256,
                .key_length = current_test_vector->key_len,
                .hw_backed = kHardenedBoolFalse,
            },
        .keyblob_length = 2 * current_test_vector->key_len,
        .keyblob = keyblob,
    };

    crypto_const_uint8_buf_t input_buf = {
        .data = current_test_vector->input_str,
        .len = current_test_vector->input_str_len,
    };

    crypto_uint8_buf_t digest_buf = {
        .data = digest,
        .len = current_test_vector->digest_len,
    };

    crypto_const_uint8_buf_t func_name = {
        .data = current_test_vector->func_name,
        .len = current_test_vector->func_name_len,
    };

    crypto_const_uint8_buf_t cust_str = {
        .data = current_test_vector->custom_str,
        .len = current_test_vector->custom_str_len,
    };

    switch (current_test_vector->security_str) {
      case kKmacSecurityStrength128:
        xof_mode = (current_test_vector->operation == kKmacOperationSHAKE)
                       ? kXofModeSha3Shake128
                       : kXofModeSha3Cshake128;
        mac_mode = kMacModeKmac128;
        break;
      case kKmacSecurityStrength224:
        hash_mode = kHashModeSha3_224;
        break;
      case kKmacSecurityStrength256:
        xof_mode = (current_test_vector->operation == kKmacOperationSHAKE)
                       ? kXofModeSha3Shake256
                       : kXofModeSha3Cshake256;
        hash_mode = kHashModeSha3_256;
        mac_mode = kMacModeKmac256;
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
      case kKmacOperationCSHAKE:
        OT_FALLTHROUGH_INTENDED;
      case kKmacOperationSHAKE:
        err_status = otcrypto_xof(input_buf, xof_mode, func_name, cust_str,
                                  digest_buf.len, &digest_buf);
        break;
      case kKmacOperationSHA3:
        err_status = otcrypto_hash(input_buf, hash_mode, &digest_buf);
        break;
      case kKmacOperationKMAC:
        err_status = otcrypto_mac(&key, input_buf, mac_mode, cust_str,
                                  current_test_vector->digest_len, &digest_buf);
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
