// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/kdf_ctr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

/**
 * Represents a test for KDF.
 */
typedef struct kdf_test_vector {
  /**
   * Key mode for KDF (e.g. kOtcryptoKeyModeHmacSha256).
   */
  otcrypto_key_mode_t key_mode;
  /**
   * Input key derivation key.
   */
  uint32_t *key_derivation_key;
  /**
   * Length of key derivation key in bytes.
   */
  size_t kdk_bytelen;
  /**
   * Context string.
   */
  uint8_t *kdf_context;
  /**
   * Length of context in bytes.
   */
  size_t kdf_context_bytelen;
  /**
   * Label string.
   */
  uint8_t *kdf_label;
  /**
   * Length of label in bytes.
   */
  size_t kdf_label_bytelen;
  /**
   * Key mode of the keying material.
   */
  otcrypto_key_mode_t km_mode;
  /**
   * Expected output keying material.
   */
  uint32_t *keying_material;
  /**
   * Length of keying material in bytes.
   */
  size_t km_bytelen;
} kdf_test_vector_t;

// Random value for masking, as large as the longest test key. This value
// should not affect the result.
static const uint32_t kTestMask[512] = {
    0x8cb847c3, 0xc6d34f36, 0x72edbf7b, 0x9bc0317f, 0x8f003c7f, 0x1d7ba049,
    0xfd463b63, 0xbb720c44, 0x784c215e, 0xeb101d65, 0x35beb911, 0xab481345,
    0xa7ebc3e3, 0x04b2a1b9, 0x764a9630, 0x78b8f9c5, 0x3f2a1d8e, 0x8cb847c3,
    0xc6d34f36, 0x72edbf7b, 0x9bc0317f, 0x8f003c7f, 0x1d7ba049, 0xfd463b63,
    0xbb720c44, 0x784c215e, 0xeb101d65, 0x35beb911, 0xab481345, 0xa7ebc3e3,
    0x04b2a1b9, 0x764a9630, 0x78b8f9c5, 0x3f2a1d8e,
};

/**
 * Call KDF through the API and check the result.
 *
 * @param test Test vector to run.
 * @return Result (OK or error).
 */
static status_t run_test(kdf_test_vector_t *test) {
  if (test->kdk_bytelen > sizeof(kTestMask)) {
    // If we get this error, we probably just need to make `kTestMask` longer.
    return OUT_OF_RANGE();
  }

  // Construct the input key derivation key.
  otcrypto_key_config_t kdk_config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = test->key_mode,
      .key_length = test->kdk_bytelen,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t kdk_keyblob[keyblob_num_words(kdk_config)];
  TRY(keyblob_from_key_and_mask(test->key_derivation_key, kTestMask, kdk_config,
                                kdk_keyblob));
  otcrypto_blinded_key_t kdk = {
      .config = kdk_config,
      .keyblob = kdk_keyblob,
      .keyblob_length = sizeof(kdk_keyblob),
  };
  kdk.checksum = integrity_blinded_checksum(&kdk);

  // Construct a blinded key struct for the output keying material. The key mode
  // here doesn't really matter, it just needs to be some symmetric key.
  otcrypto_key_config_t km_config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = test->km_mode,
      .key_length = test->km_bytelen,
      .hw_backed = kHardenedBoolFalse,
      .exportable = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t km_keyblob[keyblob_num_words(km_config)];
  otcrypto_blinded_key_t km = {
      .config = km_config,
      .keyblob = km_keyblob,
      .keyblob_length = sizeof(km_keyblob),
  };

  // Construct a buffer for the context.
  otcrypto_const_byte_buf_t context = {
      .data = test->kdf_context,
      .len = test->kdf_context_bytelen,
  };

  // Construct a buffer for the label.
  otcrypto_const_byte_buf_t label = {
      .data = test->kdf_label,
      .len = test->kdf_label_bytelen,
  };

  // Run the KDF specified by the key mode.
  switch (test->key_mode) {
    case kOtcryptoKeyModeHmacSha256:
    case kOtcryptoKeyModeHmacSha384:
    case kOtcryptoKeyModeHmacSha512:
      TRY(otcrypto_kdf_ctr_hmac(&kdk, label, context, &km));
      break;
    default:
      LOG_INFO("Should never end up here.");
      return INVALID_ARGUMENT();
  }

  LOG_INFO("KDF operation completed.");

  // Unmask the output key value and compare to the expected value.
  uint32_t *km_share0;
  uint32_t *km_share1;

  TRY(keyblob_to_shares(&km, &km_share0, &km_share1));
  uint32_t unmasked_km[keyblob_share_num_words(km_config)];
  for (size_t i = 0; i < ARRAYSIZE(unmasked_km); i++) {
    unmasked_km[i] = km_share0[i] ^ km_share1[i];
  }

  TRY_CHECK_ARRAYS_EQ((unsigned char *)unmasked_km,
                      (unsigned char *)test->keying_material, test->km_bytelen);
  return OK_STATUS();
}

/**
 * Test case 1:
 *
 * Basic test case with HMAC SHA256 using 128 bit input and output keys
 *
 * KDF Mode = HMAC Counter
 * KDK      = 0x0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b (16 octets)
 * context  = 0x01020304 (4 octets)
 * label    = 0xf0f1f2f3 (4 octets)
 * L        = 128 bits
 *
 * KM       = 0xe934f5c810d429b26c747541d898e19a (16 octets)
 */
static status_t kdf_hmac_ctr_sha256_kdk16_km16_test(void) {
  uint32_t kdk_data[] = {
      0x0b0b0b0b,
      0x0b0b0b0b,
      0x0b0b0b0b,
      0x0b0b0b0b,
  };
  uint8_t context_data[] = {
      0x01,
      0x02,
      0x03,
      0x04,
  };
  uint8_t label_data[] = {
      0xf0,
      0xf1,
      0xf2,
      0xf3,
  };
  uint32_t km_data[] = {
      0xc8f534e9,
      0xb229d410,
      0x4175746c,
      0x9ae198d8,
  };

  kdf_test_vector_t test = {
      .key_mode = kOtcryptoKeyModeHmacSha256,
      .key_derivation_key = kdk_data,
      .kdk_bytelen = 16,
      .kdf_context = context_data,
      .kdf_context_bytelen = sizeof(context_data),
      .kdf_label = label_data,
      .kdf_label_bytelen = sizeof(label_data),
      .km_mode = kOtcryptoKeyModeAesCtr,
      .keying_material = km_data,
      .km_bytelen = 16,
  };
  return run_test(&test);
}

/**
 * Test case 2:
 *
 * Basic test case with HMAC SHA256 using 256 bit input and output keys
 *
 * KDF Mode = HMAC Counter
 * KDK      = 0x0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b (32 octets)
 * context  = 0x606162636465 (6 octets)
 * label    = 0xb0b1b2b3b4b5 (6 octets)
 * L        = 256 bits
 *
 * KM       = 0x12b44b700276c03074cd99f98763574b
 *              7bf71c30340223790bf0b8f53fcf3c86 (32 octets)
 */
static status_t kdf_hmac_ctr_sha256_kdk32_km32_test(void) {
  uint32_t kdk_data[] = {
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
  };
  uint8_t context_data[] = {
      0x60, 0x61, 0x62, 0x63, 0x64, 0x65,
  };
  uint8_t label_data[] = {
      0xb0, 0xb1, 0xb2, 0xb3, 0xb4, 0xb5,
  };
  uint32_t km_data[] = {
      0x704bb412, 0x30c07602, 0xf999cd74, 0x4b576387,
      0x301cf77b, 0x79230234, 0xf5b8f00b, 0x863ccf3f,
  };

  kdf_test_vector_t test = {
      .key_mode = kOtcryptoKeyModeHmacSha256,
      .key_derivation_key = kdk_data,
      .kdk_bytelen = 32,
      .kdf_context = context_data,
      .kdf_context_bytelen = sizeof(context_data),
      .kdf_label = label_data,
      .kdf_label_bytelen = sizeof(label_data),
      .km_mode = kOtcryptoKeyModeAesCbc,
      .keying_material = km_data,
      .km_bytelen = 32,
  };
  return run_test(&test);
}

/**
 * Test case 3:
 *
 * Basic test case with HMAC SHA256 using 384 bit input and output keys
 *
 * KDF Mode = HMAC Counter
 * KDK      = 0x0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b (48 octets)
 * context  = (0 octets)
 * label    = (0 octets)
 * L        = 384 bits
 *
 * KM       = 0xf42c0c520de76893bba8aa7271431fdd
 *              86b55523d3287a8e81b206685d3b3b95
 *              c099031b5aa56d98656220a715a1b145 (48 octets)
 */
static status_t kdf_hmac_ctr_sha256_kdk48_km48_test(void) {
  uint32_t kdk_data[] = {
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
  };
  uint32_t km_data[] = {
      0x520c2cf4, 0x9368e70d, 0x72aaa8bb, 0xdd1f4371, 0x2355b586, 0x8e7a28d3,
      0x6806b281, 0x953b3b5d, 0x1b0399c0, 0x986da55a, 0xa7206265, 0x45b1a115,
  };

  kdf_test_vector_t test = {
      .key_mode = kOtcryptoKeyModeHmacSha256,
      .key_derivation_key = kdk_data,
      .kdk_bytelen = 48,
      .kdf_context = NULL,
      .kdf_context_bytelen = 0,
      .kdf_label = NULL,
      .kdf_label_bytelen = 0,
      .km_mode = kOtcryptoKeyModeAesEcb,
      .keying_material = km_data,
      .km_bytelen = 48,
  };
  return run_test(&test);
}

/**
 * Test case 4:
 *
 * Basic test case with HMAC SHA256 using 2048 bit input and output keys
 *
 * KDF Mode = HMAC Counter
 * KDK      = 0x0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b (256 octets)
 * context  = 0x8081828384858687 (8 octets)
 * label    = 0xc0c1c2c3c4c5(6 octets)
 * L        = 2048 bits
 *
 * KM       = 0x555a7c55afffa007213b9fd8560362d1
 *              d1fa720e5273e66ab5454516b809c48f
 *              8da0380745a93db45e3a46212e05ce04
 *              93b85b5a7cd46d22202b75b4c6dfb16f
 *              4fc70602188836591c2ab936e44ee94a
 *              7413e28ebcb0e896f4f0ddb1311c19b6
 *              4cc79e9abe86fe60dca62a1328c8f444
 *              9db4e63d1dde6cebad5a21e649080c94
 *              6438a31f50428aaa88c379e188ec09e5
 *              515d5acddfd68b4907d895b2213d8d47
 *              f2f521dee8c3abf00e3b3b119ff60375
 *              18b12d0136a0c3f3ce414ad211939f1a
 *              fbd1526772a2f3df7899b477a2f13ed7
 *              57657d423655920c8b7adc56adbac307
 *              9dca7183554f46b4864d9aa0f9dadfc0
 *              d62fa1f4c7e8459b607aad9946003982 (256 octets)
 */
static status_t kdf_hmac_ctr_sha256_kdk256_km256_test(void) {
  uint32_t kdk_data[] = {
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
  };
  uint8_t context_data[] = {
      0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87,
  };
  uint8_t label_data[] = {
      0xc0, 0xc1, 0xc2, 0xc3, 0xc4, 0xc5,
  };
  uint32_t km_data[] = {
      0x557c5a55, 0x07a0ffaf, 0xd89f3b21, 0xd1620356, 0x0e72fad1, 0x6ae67352,
      0x164545b5, 0x8fc409b8, 0x0738a08d, 0xb43da945, 0x21463a5e, 0x04ce052e,
      0x5a5bb893, 0x226dd47c, 0xb4752b20, 0x6fb1dfc6, 0x0206c74f, 0x59368818,
      0x36b92a1c, 0x4ae94ee4, 0x8ee21374, 0x96e8b0bc, 0xb1ddf0f4, 0xb6191c31,
      0x9a9ec74c, 0x60fe86be, 0x132aa6dc, 0x44f4c828, 0x3de6b49d, 0xeb6cde1d,
      0xe6215aad, 0x940c0849, 0x1fa33864, 0xaa8a4250, 0xe179c388, 0xe509ec88,
      0xcd5a5d51, 0x498bd6df, 0xb295d807, 0x478d3d21, 0xde21f5f2, 0xf0abc3e8,
      0x113b3b0e, 0x7503f69f, 0x012db118, 0xf3c3a036, 0xd24a41ce, 0x1a9f9311,
      0x6752d1fb, 0xdff3a272, 0x77b49978, 0xd73ef1a2, 0x427d6557, 0x0c925536,
      0x56dc7a8b, 0x07c3baad, 0x8371ca9d, 0xb4464f55, 0xa09a4d86, 0xc0dfdaf9,
      0xf4a12fd6, 0x9b45e8c7, 0x99ad7a60, 0x82390046,
  };

  kdf_test_vector_t test = {
      .key_mode = kOtcryptoKeyModeHmacSha256,
      .key_derivation_key = kdk_data,
      .kdk_bytelen = 256,
      .kdf_context = context_data,
      .kdf_context_bytelen = sizeof(context_data),
      .kdf_label = label_data,
      .kdf_label_bytelen = sizeof(label_data),
      .km_mode = kOtcryptoKeyModeAesGcm,
      .keying_material = km_data,
      .km_bytelen = 256,
  };
  return run_test(&test);
}

/**
 * Test case 5:
 *
 * Basic test case with HMAC SHA256 using 2048 bit input and 128 bit output key
 *
 * KDF Mode = HMAC Counter
 * KDK      = 0x0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b (256 octets)
 * context  = 0x90919293 (4 octets)
 * label    = 0xd0d1 (2 octets)
 * L        = 128 bits
 *
 * KM       = 0xac81a3a1f7c07a3f21d4fce68fd5ac92 (16 octets)
 */
static status_t kdf_hmac_ctr_sha256_kdk256_km16_test(void) {
  uint32_t kdk_data[] = {
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
  };
  uint8_t context_data[] = {
      0x90,
      0x91,
      0x92,
      0x93,
  };
  uint8_t label_data[] = {
      0xd0,
      0xd1,
  };
  uint32_t km_data[] = {
      0xa1a381ac,
      0x3f7ac0f7,
      0xe6fcd421,
      0x92acd58f,
  };

  kdf_test_vector_t test = {
      .key_mode = kOtcryptoKeyModeHmacSha256,
      .key_derivation_key = kdk_data,
      .kdk_bytelen = 256,
      .kdf_context = context_data,
      .kdf_context_bytelen = sizeof(context_data),
      .kdf_label = label_data,
      .kdf_label_bytelen = sizeof(label_data),
      .km_mode = kOtcryptoKeyModeAesGcm,
      .keying_material = km_data,
      .km_bytelen = 16,
  };
  return run_test(&test);
}

/**
 * Test case 6:
 *
 * Basic test case with HMAC SHA384 using 128 bit input and output keys
 *
 * KDF Mode = HMAC Counter
 * KDK      = 0x0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b (16 octets)
 * context  = 0x01020304 (4 octets)
 * label    = 0xf0f1f2f3 (4 octets)
 * L        = 128 bits
 *
 * KM       = 0x76a2316d74b63c290c009bf74798e932 (16 octets)
 */
static status_t kdf_hmac_ctr_sha384_kdk16_km16_test(void) {
  uint32_t kdk_data[] = {
      0x0b0b0b0b,
      0x0b0b0b0b,
      0x0b0b0b0b,
      0x0b0b0b0b,
  };
  uint8_t context_data[] = {
      0x01,
      0x02,
      0x03,
      0x04,
  };
  uint8_t label_data[] = {
      0xf0,
      0xf1,
      0xf2,
      0xf3,
  };
  uint32_t km_data[] = {
      0x6d31a276,
      0x293cb674,
      0xf79b000c,
      0x32e99847,
  };

  kdf_test_vector_t test = {
      .key_mode = kOtcryptoKeyModeHmacSha384,
      .key_derivation_key = kdk_data,
      .kdk_bytelen = 16,
      .kdf_context = context_data,
      .kdf_context_bytelen = sizeof(context_data),
      .kdf_label = label_data,
      .kdf_label_bytelen = sizeof(label_data),
      .km_mode = kOtcryptoKeyModeAesCtr,
      .keying_material = km_data,
      .km_bytelen = 16,
  };
  return run_test(&test);
}

/**
 * Test case 7:
 *
 * Basic test case with HMAC SHA384 using 256 bit input and output keys
 *
 * KDF Mode = HMAC Counter
 * KDK      = 0x0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b (32 octets)
 * context  = 0x606162636465 (6 octets)
 * label    = 0xb0b1b2b3b4b5 (6 octets)
 * L        = 256 bits
 *
 * KM       = 0x6049a11f8be91aa7d4550a75a02513ac
 *              0987b8beba3461d6e85919f64c789140 (32 octets)
 */
static status_t kdf_hmac_ctr_sha384_kdk32_km32_test(void) {
  uint32_t kdk_data[] = {
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
  };
  uint8_t context_data[] = {
      0x60, 0x61, 0x62, 0x63, 0x64, 0x65,
  };
  uint8_t label_data[] = {
      0xb0, 0xb1, 0xb2, 0xb3, 0xb4, 0xb5,
  };
  uint32_t km_data[] = {
      0x1fa14960, 0xa71ae98b, 0x750a55d4, 0xac1325a0,
      0xbeb88709, 0xd66134ba, 0xf61959e8, 0x4091784c,
  };

  kdf_test_vector_t test = {
      .key_mode = kOtcryptoKeyModeHmacSha384,
      .key_derivation_key = kdk_data,
      .kdk_bytelen = 32,
      .kdf_context = context_data,
      .kdf_context_bytelen = sizeof(context_data),
      .kdf_label = label_data,
      .kdf_label_bytelen = sizeof(label_data),
      .km_mode = kOtcryptoKeyModeAesCbc,
      .keying_material = km_data,
      .km_bytelen = 32,
  };
  return run_test(&test);
}

/**
 * Test case 8:
 *
 * Basic test case with HMAC SHA384 using 384 bit input and output keys
 *
 * KDF Mode = HMAC Counter
 * KDK      = 0x0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b (48 octets)
 * context  = (0 octets)
 * label    = (0 octets)
 * L        = 384 bits
 *
 * KM       = 0xdfeb8693d58307a31d467e72de28dfc2
 *              2af5d6610d2d25a409a517e412505936
 *              b3d730de63521cfed045d50b5a047415 (48 octets)
 */
static status_t kdf_hmac_ctr_sha384_kdk48_km48_test(void) {
  uint32_t kdk_data[] = {
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
  };
  uint32_t km_data[] = {
      0x9386ebdf, 0xa30783d5, 0x727e461d, 0xc2df28de, 0x61d6f52a, 0xa4252d0d,
      0xe417a509, 0x36595012, 0xde30d7b3, 0xfe1c5263, 0x0bd545d0, 0x1574045a,
  };

  kdf_test_vector_t test = {
      .key_mode = kOtcryptoKeyModeHmacSha384,
      .key_derivation_key = kdk_data,
      .kdk_bytelen = 48,
      .kdf_context = NULL,
      .kdf_context_bytelen = 0,
      .kdf_label = NULL,
      .kdf_label_bytelen = 0,
      .km_mode = kOtcryptoKeyModeAesEcb,
      .keying_material = km_data,
      .km_bytelen = 48,
  };
  return run_test(&test);
}

/**
 * Test case 9:
 *
 * Basic test case with HMAC SHA384 using 2048 bit input and output keys
 *
 * KDF Mode = HMAC Counter
 * KDK      = 0x0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b (256 octets)
 * context  = 0x8081828384858687 (8 octets)
 * label    = 0xc0c1c2c3c4c5 (6 octets)
 * L        = 2048 bits
 *
 * KM       = 0x364f6a06f49bd8c5769f307f02f77408
 *              021b18e6f7164d0072d1619802ce4d26
 *              8703c2151600c7b0407d3ab360632555
 *              4884349b297de9dc881ba3f0b4192922
 *              d31debad207f1f5814bddc5cdc83f88c
 *              c3a355cf51a208021c98c3120eeced6d
 *              1a42a893d762c19fd3d25ef7002187cd
 *              27ee87dfede8c7edba7fce4b7ac3a4a1
 *              474fb01d3dc71ecde102895968e0d579
 *              dad0a08e66ba3675a5b3c10647514dd9
 *              f6530ef6261d3b43a9c5a32332f5a3fc
 *              e7f5b78b285f78aab1edce2500999fc7
 *              3d47d6b99191a1e3ea92ecef2cba3010
 *              2ae7f786def30988e0d35e7d41f3d0e1
 *              88d9aff0710de8e6742d11af66854dc6
 *              c3033fe680f0ee5a03613d1b168e7e24 (256 octets)
 */
static status_t kdf_hmac_ctr_sha384_kdk256_km256_test(void) {
  uint32_t kdk_data[] = {
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
  };
  uint8_t context_data[] = {
      0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87,
  };
  uint8_t label_data[] = {
      0xc0, 0xc1, 0xc2, 0xc3, 0xc4, 0xc5,
  };
  uint32_t km_data[] = {
      0x066a4f36, 0xc5d89bf4, 0x7f309f76, 0x0874f702, 0xe6181b02, 0x004d16f7,
      0x9861d172, 0x264dce02, 0x15c20387, 0xb0c70016, 0xb33a7d40, 0x55256360,
      0x9b348448, 0xdce97d29, 0xf0a31b88, 0x222919b4, 0xadeb1dd3, 0x581f7f20,
      0x5cdcbd14, 0x8cf883dc, 0xcf55a3c3, 0x0208a251, 0x12c3981c, 0x6dedec0e,
      0x93a8421a, 0x9fc162d7, 0xf75ed2d3, 0xcd872100, 0xdf87ee27, 0xedc7e8ed,
      0x4bce7fba, 0xa1a4c37a, 0x1db04f47, 0xcd1ec73d, 0x598902e1, 0x79d5e068,
      0x8ea0d0da, 0x7536ba66, 0x06c1b3a5, 0xd94d5147, 0xf60e53f6, 0x433b1d26,
      0x23a3c5a9, 0xfca3f532, 0x8bb7f5e7, 0xaa785f28, 0x25ceedb1, 0xc79f9900,
      0xb9d6473d, 0xe3a19191, 0xefec92ea, 0x1030ba2c, 0x86f7e72a, 0x8809f3de,
      0x7d5ed3e0, 0xe1d0f341, 0xf0afd988, 0xe6e80d71, 0xaf112d74, 0xc64d8566,
      0xe63f03c3, 0x5aeef080, 0x1b3d6103, 0x247e8e16,
  };

  kdf_test_vector_t test = {
      .key_mode = kOtcryptoKeyModeHmacSha384,
      .key_derivation_key = kdk_data,
      .kdk_bytelen = 256,
      .kdf_context = context_data,
      .kdf_context_bytelen = sizeof(context_data),
      .kdf_label = label_data,
      .kdf_label_bytelen = sizeof(label_data),
      .km_mode = kOtcryptoKeyModeAesGcm,
      .keying_material = km_data,
      .km_bytelen = 256,
  };
  return run_test(&test);
}

/**
 * Test case 10:
 *
 * Basic test case with HMAC SHA384 using 2048 bit input and 128 bit output key
 *
 * KDF Mode = HMAC Counter
 * KDK      = 0x0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b (256 octets)
 * context  = 0x90919293 (4 octets)
 * label    = 0xd0d1 (2 octets)
 * L        = 128 bits
 *
 * KM       = 0x65c3b1827789b4ba126751e404f23e2f (16 octets)
 */
static status_t kdf_hmac_ctr_sha384_kdk256_km16_test(void) {
  uint32_t kdk_data[] = {
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
  };
  uint8_t context_data[] = {
      0x90,
      0x91,
      0x92,
      0x93,
  };
  uint8_t label_data[] = {
      0xd0,
      0xd1,
  };
  uint32_t km_data[] = {
      0x82b1c365,
      0xbab48977,
      0xe4516712,
      0x2f3ef204,
  };

  kdf_test_vector_t test = {
      .key_mode = kOtcryptoKeyModeHmacSha384,
      .key_derivation_key = kdk_data,
      .kdk_bytelen = 256,
      .kdf_context = context_data,
      .kdf_context_bytelen = sizeof(context_data),
      .kdf_label = label_data,
      .kdf_label_bytelen = sizeof(label_data),
      .km_mode = kOtcryptoKeyModeAesGcm,
      .keying_material = km_data,
      .km_bytelen = 16,
  };
  return run_test(&test);
}

/**
 * Test case 11:
 *
 * Basic test case with HMAC SHA512 using 128 bit input and output keys
 *
 * KDF Mode = HMAC Counter
 * KDK      = 0x0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b (16 octets)
 * context  = 0x01020304 (4 octets)
 * label    = 0xf0f1f2f3 (4 octets)
 * L        = 128 bits
 *
 * KM       = 0x40bc39aef846dec913e2753b96b88208 (16 octets)
 */
static status_t kdf_hmac_ctr_sha512_kdk16_km16_test(void) {
  uint32_t kdk_data[] = {
      0x0b0b0b0b,
      0x0b0b0b0b,
      0x0b0b0b0b,
      0x0b0b0b0b,
  };
  uint8_t context_data[] = {
      0x01,
      0x02,
      0x03,
      0x04,
  };
  uint8_t label_data[] = {
      0xf0,
      0xf1,
      0xf2,
      0xf3,
  };
  uint32_t km_data[] = {
      0xae39bc40,
      0xc9de46f8,
      0x3b75e213,
      0x0882b896,
  };

  kdf_test_vector_t test = {
      .key_mode = kOtcryptoKeyModeHmacSha512,
      .key_derivation_key = kdk_data,
      .kdk_bytelen = 16,
      .kdf_context = context_data,
      .kdf_context_bytelen = sizeof(context_data),
      .kdf_label = label_data,
      .kdf_label_bytelen = sizeof(label_data),
      .km_mode = kOtcryptoKeyModeAesCtr,
      .keying_material = km_data,
      .km_bytelen = 16,
  };
  return run_test(&test);
}

/**
 * Test case 12:
 *
 * Basic test case with HMAC SHA512 using 256 bit input and output keys
 *
 * KDF Mode = HMAC Counter
 * KDK      = 0x0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b (32 octets)
 * context  = 0x606162636465 (6 octets)
 * label    = 0xb0b1b2b3b4b5 (6 octets)
 * L        = 256 bits
 *
 * KM       = 0xbaab49e94918b8cb76efb15f1b2f3ffe
 *              af750e91898ebb1f6aa05f8b32392564 (32 octets)
 */
static status_t kdf_hmac_ctr_sha512_kdk32_km32_test(void) {
  uint32_t kdk_data[] = {
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
  };
  uint8_t context_data[] = {
      0x60, 0x61, 0x62, 0x63, 0x64, 0x65,
  };
  uint8_t label_data[] = {
      0xb0, 0xb1, 0xb2, 0xb3, 0xb4, 0xb5,
  };
  uint32_t km_data[] = {
      0xe949abba, 0xcbb81849, 0x5fb1ef76, 0xfe3f2f1b,
      0x910e75af, 0x1fbb8e89, 0x8b5fa06a, 0x64253932,
  };

  kdf_test_vector_t test = {
      .key_mode = kOtcryptoKeyModeHmacSha512,
      .key_derivation_key = kdk_data,
      .kdk_bytelen = 32,
      .kdf_context = context_data,
      .kdf_context_bytelen = sizeof(context_data),
      .kdf_label = label_data,
      .kdf_label_bytelen = sizeof(label_data),
      .km_mode = kOtcryptoKeyModeAesCbc,
      .keying_material = km_data,
      .km_bytelen = 32,
  };
  return run_test(&test);
}

/**
 * Test case 13:
 *
 * Basic test case with HMAC SHA512 using 384 bit input and output keys
 *
 * KDF Mode = HMAC Counter
 * KDK      = 0x0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b (48 octets)
 * context  = (0 octets)
 * label    = (0 octets)
 * L        = 384 bits
 *
 * KM       = 0x57374ecdffd0b2fee3f3352566216954
 *              4d5527dcb80b856f06f83c130089142e
 *              0a271fd516d967a43b7af81728256b9a (48 octets)
 */
static status_t kdf_hmac_ctr_sha512_kdk48_km48_test(void) {
  uint32_t kdk_data[] = {
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
  };
  uint32_t km_data[] = {
      0xcd4e3757, 0xfeb2d0ff, 0x2535f3e3, 0x54692166, 0xdc27554d, 0x6f850bb8,
      0x133cf806, 0x2e148900, 0xd51f270a, 0xa467d916, 0x17f87a3b, 0x9a6b2528,
  };

  kdf_test_vector_t test = {
      .key_mode = kOtcryptoKeyModeHmacSha512,
      .key_derivation_key = kdk_data,
      .kdk_bytelen = 48,
      .kdf_context = NULL,
      .kdf_context_bytelen = 0,
      .kdf_label = NULL,
      .kdf_label_bytelen = 0,
      .km_mode = kOtcryptoKeyModeAesEcb,
      .keying_material = km_data,
      .km_bytelen = 48,
  };
  return run_test(&test);
}

/**
 * Test case 14:
 *
 * Basic test case with HMAC SHA512 using 2048 bit input and output keys
 *
 * KDF Mode = HMAC Counter
 * KDK      = 0x0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b (256 octets)
 * context  = 0x8081828384858687 (8 octets)
 * label    = 0xc0c1c2c3c4c5 (6 octets)
 * L        = 2048 bits
 *
 * KM       = 0x77308324dafd68b6c51e50be73bb1a41
 *              c36a6b15c2216716ba21f1e41f5ca60d
 *              7aa5fa4960d16ba679d3083bb484dbd2
 *              42071daca754316f57bf7f892154c62a
 *              51598f2a3b26faf7f554f8e5d24357a2
 *              ae61198e9b5f2dc24e669d3943250631
 *              08a40a54011b6c4f908ac8bbf3dc95d2
 *              4cdc35c983fd19a9a3a7c075fc2be70f
 *              8cc9693f13e952c7c1be7cfd3aaaf163
 *              63873670e10bf17d0bcccdfc0ccce9c9
 *              2349326b09b9fe8c354944d4d1c5729f
 *              af8b4d2d9f44b9231f1397688544c6a5
 *              cc9254987851dea4372403267eb579d3
 *              95c3b926db7c0207954d95782f6db2b7
 *              8546e10571a2d47c9ff33226d5229975
 *              f4181322a22b863f588f13a385f5eb79 (256 octets)
 */
static status_t kdf_hmac_ctr_sha512_kdk256_km256_test(void) {
  uint32_t kdk_data[] = {
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
  };
  uint8_t context_data[] = {
      0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87,
  };
  uint8_t label_data[] = {
      0xc0, 0xc1, 0xc2, 0xc3, 0xc4, 0xc5,
  };
  uint32_t km_data[] = {
      0x24833077, 0xb668fdda, 0xbe501ec5, 0x411abb73, 0x156b6ac3, 0x166721c2,
      0xe4f121ba, 0x0da65c1f, 0x49faa57a, 0xa66bd160, 0x3b08d379, 0xd2db84b4,
      0xac1d0742, 0x6f3154a7, 0x897fbf57, 0x2ac65421, 0x2a8f5951, 0xf7fa263b,
      0xe5f854f5, 0xa25743d2, 0x8e1961ae, 0xc22d5f9b, 0x399d664e, 0x31062543,
      0x540aa408, 0x4f6c1b01, 0xbbc88a90, 0xd295dcf3, 0xc935dc4c, 0xa919fd83,
      0x75c0a7a3, 0x0fe72bfc, 0x3f69c98c, 0xc752e913, 0xfd7cbec1, 0x63f1aa3a,
      0x70368763, 0x7df10be1, 0xfccdcc0b, 0xc9e9cc0c, 0x6b324923, 0x8cfeb909,
      0xd4444935, 0x9f72c5d1, 0x2d4d8baf, 0x23b9449f, 0x6897131f, 0xa5c64485,
      0x985492cc, 0xa4de5178, 0x26032437, 0xd379b57e, 0x26b9c395, 0x07027cdb,
      0x78954d95, 0xb7b26d2f, 0x05e14685, 0x7cd4a271, 0x2632f39f, 0x759922d5,
      0x221318f4, 0x3f862ba2, 0xa3138f58, 0x79ebf585,
  };

  kdf_test_vector_t test = {
      .key_mode = kOtcryptoKeyModeHmacSha512,
      .key_derivation_key = kdk_data,
      .kdk_bytelen = 256,
      .kdf_context = context_data,
      .kdf_context_bytelen = sizeof(context_data),
      .kdf_label = label_data,
      .kdf_label_bytelen = sizeof(label_data),
      .km_mode = kOtcryptoKeyModeAesGcm,
      .keying_material = km_data,
      .km_bytelen = 256,
  };
  return run_test(&test);
}

/**
 * Test case 15:
 *
 * Basic test case with HMAC SHA512 using 2048 bit input and 128 bit output key
 *
 * KDF Mode = HMAC Counter
 * KDK      = 0x0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
 *              0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b (256 octets)
 * context  = 0x90919293 (4 octets)
 * label    = 0xd0d1 (2 octets)
 * L        = 128 bits
 *
 * KM       = 0x5ca93058c2a2dfb5d15063fcea57c88f (16 octets)
 */
static status_t kdf_hmac_ctr_sha512_kdk256_km16_test(void) {
  uint32_t kdk_data[] = {
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
      0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b, 0x0b0b0b0b,
  };
  uint8_t context_data[] = {
      0x90,
      0x91,
      0x92,
      0x93,
  };
  uint8_t label_data[] = {
      0xd0,
      0xd1,
  };
  uint32_t km_data[] = {
      0x5830a95c,
      0xb5dfa2c2,
      0xfc6350d1,
      0x8fc857ea,
  };

  kdf_test_vector_t test = {
      .key_mode = kOtcryptoKeyModeHmacSha512,
      .key_derivation_key = kdk_data,
      .kdk_bytelen = 256,
      .kdf_context = context_data,
      .kdf_context_bytelen = sizeof(context_data),
      .kdf_label = label_data,
      .kdf_label_bytelen = sizeof(label_data),
      .km_mode = kOtcryptoKeyModeAesGcm,
      .keying_material = km_data,
      .km_bytelen = 16,
  };
  return run_test(&test);
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  // Start the entropy complex.
  CHECK_STATUS_OK(entropy_complex_init());

  status_t test_result = OK_STATUS();

  // SHA256 tests
  EXECUTE_TEST(test_result, kdf_hmac_ctr_sha256_kdk16_km16_test);
  EXECUTE_TEST(test_result, kdf_hmac_ctr_sha256_kdk32_km32_test);
  EXECUTE_TEST(test_result, kdf_hmac_ctr_sha256_kdk48_km48_test);
  EXECUTE_TEST(test_result, kdf_hmac_ctr_sha256_kdk256_km256_test);
  EXECUTE_TEST(test_result, kdf_hmac_ctr_sha256_kdk256_km16_test);

  // SHA384 tests
  EXECUTE_TEST(test_result, kdf_hmac_ctr_sha384_kdk16_km16_test);
  EXECUTE_TEST(test_result, kdf_hmac_ctr_sha384_kdk32_km32_test);
  EXECUTE_TEST(test_result, kdf_hmac_ctr_sha384_kdk48_km48_test);
  EXECUTE_TEST(test_result, kdf_hmac_ctr_sha384_kdk256_km256_test);
  EXECUTE_TEST(test_result, kdf_hmac_ctr_sha384_kdk256_km16_test);

  // SHA512 tests
  EXECUTE_TEST(test_result, kdf_hmac_ctr_sha512_kdk16_km16_test);
  EXECUTE_TEST(test_result, kdf_hmac_ctr_sha512_kdk32_km32_test);
  EXECUTE_TEST(test_result, kdf_hmac_ctr_sha512_kdk48_km48_test);
  EXECUTE_TEST(test_result, kdf_hmac_ctr_sha512_kdk256_km256_test);
  EXECUTE_TEST(test_result, kdf_hmac_ctr_sha512_kdk256_km16_test);

  return status_ok(test_result);
}
