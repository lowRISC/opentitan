// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include "hw/top/dt/aon_timer.h"
#include "hw/top/dt/hmac.h"
#include "hw/top/dt/kmac.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/impl/mldsa/mldsa.h"
#include "sw/device/lib/crypto/impl/mlkem/mlkem.h"
#include "sw/device/lib/crypto/include/aes_gcm.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/drbg.h"
#include "sw/device/lib/crypto/include/ecc_curve25519.h"
#include "sw/device/lib/crypto/include/ecc_p256.h"
#include "sw/device/lib/crypto/include/ecc_p384.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/key_transport.h"
#include "sw/device/lib/crypto/include/mldsa.h"
#include "sw/device/lib/crypto/include/mlkem.h"
#include "sw/device/lib/crypto/include/rsa.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/crypto/include/sha3.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_entropy_src.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_src_testutils.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/kmac.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/verify.h"
#include "sw/device/silicon_creator/rom/fips_kat_table.h"

#include "hw/top/aes_regs.h"
#include "hw/top/hmac_regs.h"

OTTF_DEFINE_TEST_CONFIG(.ignore_alerts = true);

static const uint8_t __attribute__((unused)) kExpectedSha256Digest[32] = {
    0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40,
    0xde, 0x5d, 0xae, 0x22, 0x23, 0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17,
    0x7a, 0x9c, 0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad,
};

static const uint8_t __attribute__((unused)) kExpectedHmacSha256Digest[32] = {
    0xcd, 0xcb, 0x12, 0x20, 0xd1, 0xec, 0xcc, 0xea, 0x91, 0xe5, 0x3a,
    0xba, 0x30, 0x92, 0xf9, 0x62, 0xe5, 0x49, 0xfe, 0x6c, 0xe9, 0xed,
    0x7f, 0xdc, 0x43, 0x19, 0x1f, 0xbd, 0xe4, 0x5c, 0x30, 0xb0,
};

static const uint8_t __attribute__((unused)) kExpectedSha512Digest[64] = {
    0xdd, 0xaf, 0x35, 0xa1, 0x93, 0x61, 0x7a, 0xba, 0xcc, 0x41, 0x73,
    0x49, 0xae, 0x20, 0x41, 0x31, 0x12, 0xe6, 0xfa, 0x4e, 0x89, 0xa9,
    0x7e, 0xa2, 0x0a, 0x9e, 0xee, 0xe6, 0x4b, 0x55, 0xd3, 0x9a, 0x21,
    0x92, 0x99, 0x2a, 0x27, 0x4f, 0xc1, 0xa8, 0x36, 0xba, 0x3c, 0x23,
    0xa3, 0xfe, 0xeb, 0xbd, 0x45, 0x4d, 0x44, 0x23, 0x64, 0x3c, 0xe8,
    0x0e, 0x2a, 0x9a, 0xc9, 0x4f, 0xa5, 0x4c, 0xa4, 0x9f,
};

static const uint8_t __attribute__((unused)) kExpectedHmacSha512Digest[64] = {
    0xfa, 0x73, 0xb0, 0x08, 0x9d, 0x56, 0xa2, 0x84, 0xef, 0xb0, 0xf0,
    0x75, 0x6c, 0x89, 0x0b, 0xe9, 0xb1, 0xb5, 0xdb, 0xdd, 0x8e, 0xe8,
    0x1a, 0x36, 0x55, 0xf8, 0x3e, 0x33, 0xb2, 0x27, 0x9d, 0x39, 0xbf,
    0x3e, 0x84, 0x82, 0x79, 0xa7, 0x22, 0xc8, 0x06, 0xb4, 0x85, 0xa4,
    0x7e, 0x67, 0xc8, 0x07, 0xb9, 0x46, 0xa3, 0x37, 0xbe, 0xe8, 0x94,
    0x26, 0x74, 0x27, 0x88, 0x59, 0xe1, 0x32, 0x92, 0xfb,
};

static const uint8_t __attribute__((unused)) kExpectedAes256Key[32] = {
    0x60, 0x3d, 0xeb, 0x10, 0x15, 0xca, 0x71, 0xbe, 0x2b, 0x73, 0xae,
    0xf0, 0x85, 0x7d, 0x77, 0x81, 0x1f, 0x35, 0x2c, 0x07, 0x3b, 0x61,
    0x08, 0xd7, 0x2d, 0x98, 0x10, 0xa3, 0x09, 0x14, 0xdf, 0xf4,
};

static const uint8_t __attribute__((unused)) kExpectedAes256EcbPt[16] = {
    0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96,
    0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a,
};

static const uint8_t __attribute__((unused)) kExpectedAes256EcbCt[16] = {
    0xf3, 0xee, 0xd1, 0xbd, 0xb5, 0xd2, 0xa0, 0x3c,
    0x06, 0x4b, 0x5a, 0x7e, 0x3d, 0xb1, 0x81, 0xf8,
};

static const uint8_t __attribute__((unused)) kExpectedAes256CbcIv[16] = {
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
    0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
};

static const uint8_t __attribute__((unused)) kExpectedAes256CbcPt[16] = {
    0x6b, 0xc1, 0xbe, 0xe2, 0x2e, 0x40, 0x9f, 0x96,
    0xe9, 0x3d, 0x7e, 0x11, 0x73, 0x93, 0x17, 0x2a,
};

static const uint8_t __attribute__((unused)) kExpectedAes256CbcCt[16] = {
    0xf5, 0x8c, 0x4c, 0x04, 0xd6, 0xe5, 0xf1, 0xba,
    0x77, 0x9e, 0xab, 0xfb, 0x5f, 0x7b, 0xfb, 0xd6,
};

static const uint8_t __attribute__((unused)) kExpectedAesGcm256Key[32] = {
    0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
    0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
    0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa, 0xaa,
};

static const uint8_t __attribute__((unused)) kExpectedAesGcm256Iv[12] = {
    0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb, 0xbb,
};

static const uint8_t __attribute__((unused)) kExpectedAesGcm256Pt[16] = {
    0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc,
    0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc,
};

static const uint8_t __attribute__((unused)) kExpectedAesGcm256Ct[16] = {
    0x06, 0xdd, 0x87, 0x6a, 0xba, 0xd1, 0x96, 0x14,
    0xfc, 0x58, 0x61, 0x51, 0x21, 0xa9, 0x16, 0xd6,
};

static const uint8_t __attribute__((unused)) kExpectedAesGcm256Tag[16] = {
    0x8e, 0xe2, 0x59, 0x8e, 0xe0, 0xcb, 0x02, 0x99,
    0xec, 0xe2, 0x92, 0x88, 0x42, 0x7c, 0x1b, 0x22,
};

static const uint8_t __attribute__((unused)) kExpectedDrbgEntropyInput[48] = {
    0x10, 0xc0, 0xbe, 0x73, 0x4c, 0x47, 0x62, 0x92, 0x76, 0x0f, 0xa3, 0x16,
    0xde, 0x51, 0x1b, 0x53, 0xe5, 0x94, 0xe4, 0x2e, 0xb3, 0x9d, 0xec, 0xdf,
    0x9d, 0x87, 0x7a, 0xcb, 0x9c, 0x41, 0x00, 0x56, 0xb0, 0xb0, 0x79, 0xca,
    0x5c, 0x3b, 0xa3, 0xdd, 0x9e, 0x64, 0x68, 0xa4, 0xfa, 0x73, 0x5d, 0xdf,
};

static const uint8_t __attribute__((unused)) kExpectedDrbgOutput[64] = {
    0xd9, 0x7c, 0xc0, 0xd1, 0xf1, 0xa7, 0xf8, 0x5a, 0x4c, 0xc8, 0x12,
    0x10, 0xcb, 0xb8, 0x8b, 0xe4, 0x99, 0x9e, 0x18, 0x87, 0xb1, 0xcc,
    0x0f, 0xd4, 0x9b, 0x61, 0x1c, 0x77, 0x22, 0xab, 0x82, 0xdf, 0x2f,
    0xdc, 0xb1, 0x80, 0x91, 0xf3, 0x81, 0x25, 0x0c, 0xac, 0xf7, 0x64,
    0xb3, 0x94, 0x04, 0x51, 0xb7, 0x41, 0x3c, 0xa4, 0x4c, 0x51, 0x17,
    0xdb, 0xae, 0x07, 0xb1, 0x87, 0xc5, 0x01, 0x3e, 0x79,
};

static const uint8_t __attribute__((unused)) kExpectedSphincsPlusPk[32] = {
    0xb5, 0x05, 0xd7, 0xcf, 0xad, 0x1b, 0x49, 0x74, 0x99, 0x32, 0x3c,
    0x86, 0x86, 0x32, 0x5e, 0x47, 0x6d, 0x2e, 0x59, 0x93, 0xd9, 0x19,
    0xb7, 0xf2, 0x88, 0xcc, 0x82, 0x31, 0x33, 0x04, 0x6c, 0xf9,
};

static const uint8_t __attribute__((unused)) kExpectedSphincsPlusMsg[33] = {
    0xd8, 0x1c, 0x4d, 0x8d, 0x73, 0x4f, 0xcb, 0xfb, 0xea, 0xde, 0x3d,
    0x3f, 0x8a, 0x03, 0x9f, 0xaa, 0x2a, 0x2c, 0x99, 0x57, 0xe8, 0x35,
    0xad, 0x55, 0xb2, 0x2e, 0x75, 0xbf, 0x57, 0xbb, 0x55, 0x6a, 0xc8,
};

static const uint8_t __attribute__((unused)) kExpectedKdfHmacSha256Kdk[32] = {
    0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b,
    0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b,
    0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b,
};

static const uint8_t __attribute__((unused)) kExpectedKdfHmacSha256Msg[21] = {
    0x00, 0x00, 0x00, 0x01, 0xb0, 0xb1, 0xb2, 0xb3, 0xb4, 0xb5, 0x00,
    0x60, 0x61, 0x62, 0x63, 0x64, 0x65, 0x00, 0x00, 0x01, 0x00,
};

static const uint8_t __attribute__((unused)) kExpectedKdfHmacSha256Km[32] = {
    0x12, 0xb4, 0x4b, 0x70, 0x02, 0x76, 0xc0, 0x30, 0x74, 0xcd, 0x99,
    0xf9, 0x87, 0x63, 0x57, 0x4b, 0x7b, 0xf7, 0x1c, 0x30, 0x34, 0x02,
    0x23, 0x79, 0x0b, 0xf0, 0xb8, 0xf5, 0x3f, 0xcf, 0x3c, 0x86,
};

static const uint8_t __attribute__((unused)) kExpectedShake256Msg[1] = {0x0f};

static const uint8_t __attribute__((unused)) kExpectedShake256Digest[32] = {
    0xaa, 0xbb, 0x07, 0x48, 0x8f, 0xf9, 0xed, 0xd0, 0x5d, 0x6a, 0x60,
    0x3b, 0x77, 0x91, 0xb6, 0x0a, 0x16, 0xd4, 0x50, 0x93, 0x60, 0x8f,
    0x1b, 0xad, 0xc0, 0xc9, 0xcc, 0x9a, 0x91, 0x54, 0xf2, 0x15,
};

static const uint8_t __attribute__((unused)) kExpectedKmac256Key[32] = {
    0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4a,
    0x4b, 0x4c, 0x4d, 0x4e, 0x4f, 0x50, 0x51, 0x52, 0x53, 0x54, 0x55,
    0x56, 0x57, 0x58, 0x59, 0x5a, 0x5b, 0x5c, 0x5d, 0x5e, 0x5f,
};

static const uint8_t
    __attribute__((unused)) kExpectedKmac256Msg[4] = {0x00, 0x01, 0x02, 0x03};

static const uint8_t __attribute__((unused)) kExpectedKmac256Digest[64] = {
    0x20, 0xc5, 0x70, 0xc3, 0x13, 0x46, 0xf7, 0x03, 0xc9, 0xac, 0x36,
    0xc6, 0x1c, 0x03, 0xcb, 0x64, 0xc3, 0x97, 0x0d, 0x0c, 0xfc, 0x78,
    0x7e, 0x9b, 0x79, 0x59, 0x9d, 0x27, 0x3a, 0x68, 0xd2, 0xf7, 0xf6,
    0x9d, 0x4c, 0xc3, 0xde, 0x9d, 0x10, 0x4a, 0x35, 0x16, 0x89, 0xf2,
    0x7c, 0xf6, 0xf5, 0x95, 0x1f, 0x01, 0x03, 0xf3, 0x3f, 0x4f, 0x24,
    0x87, 0x10, 0x24, 0xd9, 0xc2, 0x77, 0x73, 0xa8, 0xdd,
};

static const uint8_t __attribute__((unused)) kExpectedAesKwp256Ct[24] = {
    0xcc, 0x06, 0xca, 0x9e, 0xd0, 0x8d, 0xb0, 0x32, 0x13, 0x48, 0x1e, 0x0b,
    0x44, 0x0d, 0x7f, 0xab, 0xf8, 0x85, 0x0c, 0xcc, 0xad, 0x63, 0x00, 0x53,
};

static status_t test_sha256_kat(const fips_kat_descriptor_table_t *table) {
  LOG_INFO("Searching for SHA2-256 KAT entry (alg_id = %u)...",
           kFipsKatAlgSha2_256);
  const fips_kat_entry_t *entry = find_fips_entry(table, kFipsKatAlgSha2_256);
  CHECK(entry != NULL, "SHA2-256 KAT entry not found in table!");
  LOG_INFO("Entry found: algorithm_id=%u, offset=%u, size=%u",
           entry->algorithm_id, entry->offset, entry->size);

  LOG_INFO("Resolving SHA2-256 KAT data payload...");
  const void *data = get_fips_data(table, entry);
  CHECK(data != NULL, "Failed to resolve KAT data payload (out of bounds)!");

  const hmac_kat_data_t *kat_data = (const hmac_kat_data_t *)data;
  CHECK(kat_data->key_len == 0, "Expected key_len=0, got %u",
        kat_data->key_len);
  CHECK(kat_data->msg_len == 3, "Expected msg_len=3, got %u",
        kat_data->msg_len);
  CHECK(kat_data->digest_len == 32, "Expected digest_len=32, got %u",
        kat_data->digest_len);

  const uint8_t *msg = kat_data->data;
  const uint8_t *expected_digest = kat_data->data + kat_data->msg_len;

  CHECK(msg[0] == 'a' && msg[1] == 'b' && msg[2] == 'c',
        "Test vector message mismatch!");
  CHECK_ARRAYS_EQ(expected_digest, kExpectedSha256Digest, 32);
  LOG_INFO("SHA2-256 vector payload verified against golden values.");

  LOG_INFO("Executing SHA2-256 hash using HMAC hardware accelerator...");
  hmac_digest_t digest;
  hmac_sha256(msg, kat_data->msg_len, &digest);

  // Convert little-endian word digest from hmac_sha256 to big-endian byte
  // array.
  uint8_t computed_digest[32];
  for (size_t i = 0; i < 8; ++i) {
    uint32_t word = digest.digest[7 - i];
    computed_digest[4 * i] = (uint8_t)(word >> 24);
    computed_digest[4 * i + 1] = (uint8_t)(word >> 16);
    computed_digest[4 * i + 2] = (uint8_t)(word >> 8);
    computed_digest[4 * i + 3] = (uint8_t)(word);
  }

  CHECK_ARRAYS_EQ(computed_digest, expected_digest, 32);
  LOG_INFO("SHA2-256 Known Answer Test check ok.");

  return OK_STATUS();
}

static status_t test_hmac_sha256_kat(const fips_kat_descriptor_table_t *table) {
  LOG_INFO("Searching for HMAC-SHA2-256 KAT entry (alg_id = %u)...",
           kFipsKatAlgHmacSha2_256);
  const fips_kat_entry_t *entry =
      find_fips_entry(table, kFipsKatAlgHmacSha2_256);
  CHECK(entry != NULL, "HMAC-SHA2-256 KAT entry not found in table!");
  LOG_INFO("Entry found: algorithm_id=%u, offset=%u, size=%u",
           entry->algorithm_id, entry->offset, entry->size);

  LOG_INFO("Resolving HMAC-SHA2-256 KAT data payload...");
  const void *data = get_fips_data(table, entry);
  CHECK(data != NULL, "Failed to resolve KAT data payload (out of bounds)!");

  const hmac_kat_data_t *kat_data = (const hmac_kat_data_t *)data;
  CHECK(kat_data->key_len == 32, "Expected key_len=32, got %u",
        kat_data->key_len);
  CHECK(kat_data->msg_len == 50, "Expected msg_len=50, got %u",
        kat_data->msg_len);
  CHECK(kat_data->digest_len == 32, "Expected digest_len=32, got %u",
        kat_data->digest_len);

  const uint8_t *key = kat_data->data;
  const uint8_t *msg = kat_data->data + kat_data->key_len;
  const uint8_t *expected_digest =
      kat_data->data + kat_data->key_len + kat_data->msg_len;

  for (size_t i = 0; i < 32; ++i) {
    CHECK(key[i] == 0xaa, "Key byte %zu mismatch: expected 0xaa, got 0x%02x", i,
          key[i]);
  }
  for (size_t i = 0; i < 50; ++i) {
    CHECK(msg[i] == 0xdd, "Msg byte %zu mismatch: expected 0xdd, got 0x%02x", i,
          msg[i]);
  }
  CHECK_ARRAYS_EQ(expected_digest, kExpectedHmacSha256Digest, 32);
  LOG_INFO("HMAC-SHA2-256 vector payload verified against golden values.");

  LOG_INFO("Executing HMAC-SHA2-256 using HMAC hardware accelerator...");
  hmac_key_t hkey;
  for (size_t i = 0; i < 8; ++i) {
    hkey.key[i] = (uint32_t)key[4 * i] | ((uint32_t)key[4 * i + 1] << 8) |
                  ((uint32_t)key[4 * i + 2] << 16) |
                  ((uint32_t)key[4 * i + 3] << 24);
  }
  hmac_digest_t digest;
  sc_hmac_hmac_sha256(msg, kat_data->msg_len, hkey, /*big_endian_digest=*/false,
                      &digest);

  uint8_t computed_digest[32];
  for (size_t i = 0; i < 8; ++i) {
    uint32_t word = digest.digest[7 - i];
    computed_digest[4 * i] = (uint8_t)(word >> 24);
    computed_digest[4 * i + 1] = (uint8_t)(word >> 16);
    computed_digest[4 * i + 2] = (uint8_t)(word >> 8);
    computed_digest[4 * i + 3] = (uint8_t)(word);
  }

  CHECK_ARRAYS_EQ(computed_digest, expected_digest, 32);
  LOG_INFO("HMAC-SHA2-256 Known Answer Test check ok.");

  return OK_STATUS();
}

static status_t test_sha512_kat(const fips_kat_descriptor_table_t *table) {
  LOG_INFO("Searching for SHA2-512 KAT entry (alg_id = %u)...",
           kFipsKatAlgSha2_512);
  const fips_kat_entry_t *entry = find_fips_entry(table, kFipsKatAlgSha2_512);
  CHECK(entry != NULL, "SHA2-512 KAT entry not found in table!");
  LOG_INFO("Entry found: algorithm_id=%u, offset=%u, size=%u",
           entry->algorithm_id, entry->offset, entry->size);

  LOG_INFO("Resolving SHA2-512 KAT data payload...");
  const void *data = get_fips_data(table, entry);
  CHECK(data != NULL, "Failed to resolve KAT data payload (out of bounds)!");

  const hmac_kat_data_t *kat_data = (const hmac_kat_data_t *)data;
  CHECK(kat_data->key_len == 0, "Expected key_len=0, got %u",
        kat_data->key_len);
  CHECK(kat_data->msg_len == 3, "Expected msg_len=3, got %u",
        kat_data->msg_len);
  CHECK(kat_data->digest_len == 64, "Expected digest_len=64, got %u",
        kat_data->digest_len);

  const uint8_t *msg = kat_data->data + kat_data->key_len;
  const uint8_t *expected_digest =
      kat_data->data + kat_data->key_len + kat_data->msg_len;

  CHECK(msg[0] == 'a' && msg[1] == 'b' && msg[2] == 'c',
        "Test vector message mismatch!");
  CHECK_ARRAYS_EQ(expected_digest, kExpectedSha512Digest, 64);
  LOG_INFO("SHA2-512 vector payload verified against golden values.");

  LOG_INFO("Executing SHA2-512 hash using HMAC hardware accelerator...");
  const uint32_t hmac_base_addr = dt_hmac_primary_reg_block(kDtHmac);

  // Clear config and disable interrupts
  abs_mmio_write32(hmac_base_addr + HMAC_CFG_REG_OFFSET, 0u);
  abs_mmio_write32(hmac_base_addr + HMAC_INTR_ENABLE_REG_OFFSET, 0u);
  abs_mmio_write32(hmac_base_addr + HMAC_INTR_STATE_REG_OFFSET, UINT32_MAX);

  // Configure HMAC IP for SHA2-512 with digest_swap = true
  uint32_t cfg = 0;
  cfg = bitfield_bit32_write(cfg, HMAC_CFG_DIGEST_SWAP_BIT, true);
  cfg = bitfield_bit32_write(cfg, HMAC_CFG_ENDIAN_SWAP_BIT, false);
  cfg = bitfield_bit32_write(cfg, HMAC_CFG_SHA_EN_BIT, true);
  cfg = bitfield_bit32_write(cfg, HMAC_CFG_HMAC_EN_BIT, false);
  cfg = bitfield_field32_write(cfg, HMAC_CFG_DIGEST_SIZE_FIELD,
                               HMAC_CFG_DIGEST_SIZE_VALUE_SHA2_512);
  cfg = bitfield_field32_write(cfg, HMAC_CFG_KEY_LENGTH_FIELD,
                               HMAC_CFG_KEY_LENGTH_VALUE_KEY_NONE);
  abs_mmio_write32(hmac_base_addr + HMAC_CFG_REG_OFFSET, cfg);

  // Start hash
  abs_mmio_write32(hmac_base_addr + HMAC_CMD_REG_OFFSET,
                   bitfield_bit32_write(0, HMAC_CMD_HASH_START_BIT, true));

  // Write message bytes into FIFO
  for (size_t i = 0; i < kat_data->msg_len; ++i) {
    abs_mmio_write8(hmac_base_addr + HMAC_MSG_FIFO_REG_OFFSET, msg[i]);
  }

  // Trigger process
  abs_mmio_write32(hmac_base_addr + HMAC_CMD_REG_OFFSET,
                   bitfield_bit32_write(0, HMAC_CMD_HASH_PROCESS_BIT, true));

  // Wait until hmac_done interrupt flag is asserted
  uint32_t intr_state = 0;
  do {
    intr_state = abs_mmio_read32(hmac_base_addr + HMAC_INTR_STATE_REG_OFFSET);
  } while (!bitfield_bit32_read(intr_state, HMAC_INTR_STATE_HMAC_DONE_BIT));
  abs_mmio_write32(hmac_base_addr + HMAC_INTR_STATE_REG_OFFSET, intr_state);

  // Read 16 digest registers (64 bytes)
  uint32_t computed_digest[16];
  for (size_t i = 0; i < 16; ++i) {
    computed_digest[i] = abs_mmio_read32(
        hmac_base_addr + HMAC_DIGEST_0_REG_OFFSET + i * sizeof(uint32_t));
  }

  CHECK_ARRAYS_EQ((const uint8_t *)computed_digest, expected_digest, 64);
  LOG_INFO("SHA2-512 Known Answer Test check ok.");

  return OK_STATUS();
}

static status_t test_hmac_sha512_kat(const fips_kat_descriptor_table_t *table) {
  LOG_INFO("Searching for HMAC-SHA2-512 KAT entry (alg_id = %u)...",
           kFipsKatAlgHmacSha2_512);
  const fips_kat_entry_t *entry =
      find_fips_entry(table, kFipsKatAlgHmacSha2_512);
  CHECK(entry != NULL, "HMAC-SHA2-512 KAT entry not found in table!");
  LOG_INFO("Entry found: algorithm_id=%u, offset=%u, size=%u",
           entry->algorithm_id, entry->offset, entry->size);

  LOG_INFO("Resolving HMAC-SHA2-512 KAT data payload...");
  const void *data = get_fips_data(table, entry);
  CHECK(data != NULL, "Failed to resolve KAT data payload (out of bounds)!");

  const hmac_kat_data_t *kat_data = (const hmac_kat_data_t *)data;
  CHECK(kat_data->key_len == 20, "Expected key_len=20, got %u",
        kat_data->key_len);
  CHECK(kat_data->msg_len == 50, "Expected msg_len=50, got %u",
        kat_data->msg_len);
  CHECK(kat_data->digest_len == 64, "Expected digest_len=64, got %u",
        kat_data->digest_len);

  const uint8_t *key = kat_data->data;
  const uint8_t *msg = kat_data->data + kat_data->key_len;
  const uint8_t *expected_digest =
      kat_data->data + kat_data->key_len + kat_data->msg_len;

  for (size_t i = 0; i < kat_data->key_len; ++i) {
    CHECK(key[i] == 0xaa, "Key byte %zu mismatch: expected 0xaa, got 0x%02x", i,
          key[i]);
  }
  for (size_t i = 0; i < kat_data->msg_len; ++i) {
    CHECK(msg[i] == 0xdd, "Msg byte %zu mismatch: expected 0xdd, got 0x%02x", i,
          msg[i]);
  }
  CHECK_ARRAYS_EQ(expected_digest, kExpectedHmacSha512Digest, 64);
  LOG_INFO("HMAC-SHA2-512 vector payload verified against golden values.");

  LOG_INFO("Executing HMAC-SHA2-512 using HMAC hardware accelerator...");
  const uint32_t hmac_base_addr = dt_hmac_primary_reg_block(kDtHmac);

  // Clear config and disable interrupts
  abs_mmio_write32(hmac_base_addr + HMAC_CFG_REG_OFFSET, 0u);
  abs_mmio_write32(hmac_base_addr + HMAC_INTR_ENABLE_REG_OFFSET, 0u);
  abs_mmio_write32(hmac_base_addr + HMAC_INTR_STATE_REG_OFFSET, UINT32_MAX);

  // Configure HMAC IP for HMAC-SHA2-512 with 1024-bit key block
  uint32_t cfg = 0;
  cfg = bitfield_bit32_write(cfg, HMAC_CFG_KEY_SWAP_BIT, true);
  cfg = bitfield_bit32_write(cfg, HMAC_CFG_DIGEST_SWAP_BIT, true);
  cfg = bitfield_bit32_write(cfg, HMAC_CFG_ENDIAN_SWAP_BIT, false);
  cfg = bitfield_bit32_write(cfg, HMAC_CFG_SHA_EN_BIT, true);
  cfg = bitfield_bit32_write(cfg, HMAC_CFG_HMAC_EN_BIT, true);
  cfg = bitfield_field32_write(cfg, HMAC_CFG_DIGEST_SIZE_FIELD,
                               HMAC_CFG_DIGEST_SIZE_VALUE_SHA2_512);
  cfg = bitfield_field32_write(cfg, HMAC_CFG_KEY_LENGTH_FIELD,
                               HMAC_CFG_KEY_LENGTH_VALUE_KEY_1024);
  abs_mmio_write32(hmac_base_addr + HMAC_CFG_REG_OFFSET, cfg);

  // Write 1024-bit key block (padded with zeros)
  uint32_t key_block[32] = {0};
  memcpy(key_block, key, kat_data->key_len);
  for (size_t i = 0; i < 32; ++i) {
    abs_mmio_write32(
        hmac_base_addr + HMAC_KEY_0_REG_OFFSET + i * sizeof(uint32_t),
        key_block[i]);
  }

  // Start hash
  abs_mmio_write32(hmac_base_addr + HMAC_CMD_REG_OFFSET,
                   bitfield_bit32_write(0, HMAC_CMD_HASH_START_BIT, true));

  // Write message bytes into FIFO
  for (size_t i = 0; i < kat_data->msg_len; ++i) {
    abs_mmio_write8(hmac_base_addr + HMAC_MSG_FIFO_REG_OFFSET, msg[i]);
  }

  // Trigger process
  abs_mmio_write32(hmac_base_addr + HMAC_CMD_REG_OFFSET,
                   bitfield_bit32_write(0, HMAC_CMD_HASH_PROCESS_BIT, true));

  // Wait until hmac_done interrupt flag is asserted
  uint32_t intr_state = 0;
  do {
    intr_state = abs_mmio_read32(hmac_base_addr + HMAC_INTR_STATE_REG_OFFSET);
  } while (!bitfield_bit32_read(intr_state, HMAC_INTR_STATE_HMAC_DONE_BIT));
  abs_mmio_write32(hmac_base_addr + HMAC_INTR_STATE_REG_OFFSET, intr_state);

  // Read 16 digest registers (64 bytes)
  uint32_t computed_digest[16];
  for (size_t i = 0; i < 16; ++i) {
    computed_digest[i] = abs_mmio_read32(
        hmac_base_addr + HMAC_DIGEST_0_REG_OFFSET + i * sizeof(uint32_t));
  }

  CHECK_ARRAYS_EQ((const uint8_t *)computed_digest, expected_digest, 64);
  LOG_INFO("HMAC-SHA2-512 Known Answer Test check ok.");

  return OK_STATUS();
}

static status_t test_shake256_kat(const fips_kat_descriptor_table_t *table) {
  LOG_INFO("Searching for SHAKE-256 KAT entry (alg_id = %u)...",
           kFipsKatAlgShake256);
  const fips_kat_entry_t *entry = find_fips_entry(table, kFipsKatAlgShake256);
  CHECK(entry != NULL, "SHAKE-256 KAT entry not found in table!");
  LOG_INFO("Entry found: algorithm_id=%u, offset=%u, size=%u",
           entry->algorithm_id, entry->offset, entry->size);

  LOG_INFO("Resolving SHAKE-256 KAT data payload...");
  const void *data = get_fips_data(table, entry);
  CHECK(data != NULL, "Failed to resolve KAT data payload (out of bounds)!");

  const hmac_kat_data_t *kat_data = (const hmac_kat_data_t *)data;
  CHECK(kat_data->key_len == 0, "Expected key_len=0, got %u",
        kat_data->key_len);
  CHECK(kat_data->msg_len == 1, "Expected msg_len=1, got %u",
        kat_data->msg_len);
  CHECK(kat_data->digest_len == 32, "Expected digest_len=32, got %u",
        kat_data->digest_len);

  const uint8_t *msg = kat_data->data + kat_data->key_len;
  const uint8_t *expected_digest =
      kat_data->data + kat_data->key_len + ((kat_data->msg_len + 3) & ~3u);

  CHECK(msg[0] == kExpectedShake256Msg[0], "SHAKE-256 message mismatch!");
  CHECK_ARRAYS_EQ(expected_digest, kExpectedShake256Digest, 32);
  LOG_INFO("SHAKE-256 vector payload verified against golden values.");

  LOG_INFO("Executing SHAKE-256 using KMAC hardware accelerator...");
  CHECK(kmac_shake256_configure() == kErrorOk,
        "Failed to configure KMAC for SHAKE-256!");
  CHECK(kmac_shake256_start() == kErrorOk, "Failed to start SHAKE-256!");

  kmac_shake256_absorb(msg, kat_data->msg_len);
  kmac_shake256_squeeze_start();

  uint32_t act_digest_words[8];
  CHECK(kmac_shake256_squeeze_end(act_digest_words, 8) == kErrorOk,
        "Failed to squeeze SHAKE-256 digest!");

  CHECK_ARRAYS_EQ((const uint8_t *)act_digest_words, expected_digest, 32);
  LOG_INFO("SHAKE-256 Known Answer Test check ok.");

  return OK_STATUS();
}

static status_t test_kmac256_kat(const fips_kat_descriptor_table_t *table) {
  LOG_INFO("Searching for KMAC-256 KAT entry (alg_id = %u)...",
           kFipsKatAlgKmac256);
  const fips_kat_entry_t *entry = find_fips_entry(table, kFipsKatAlgKmac256);
  CHECK(entry != NULL, "KMAC-256 KAT entry not found in table!");
  LOG_INFO("Entry found: algorithm_id=%u, offset=%u, size=%u",
           entry->algorithm_id, entry->offset, entry->size);

  LOG_INFO("Resolving KMAC-256 KAT data payload...");
  const void *data = get_fips_data(table, entry);
  CHECK(data != NULL, "Failed to resolve KAT data payload (out of bounds)!");

  const hmac_kat_data_t *kat_data = (const hmac_kat_data_t *)data;
  CHECK(kat_data->key_len == 32, "Expected key_len=32, got %u",
        kat_data->key_len);
  CHECK(kat_data->msg_len == 4, "Expected msg_len=4, got %u",
        kat_data->msg_len);
  CHECK(kat_data->digest_len == 64, "Expected digest_len=64, got %u",
        kat_data->digest_len);

  const uint8_t *key = kat_data->data;
  const uint8_t *msg = kat_data->data + kat_data->key_len;
  const uint8_t *expected_digest =
      kat_data->data + kat_data->key_len + kat_data->msg_len;

  CHECK_ARRAYS_EQ(key, kExpectedKmac256Key, 32);
  CHECK_ARRAYS_EQ(msg, kExpectedKmac256Msg, 4);
  CHECK_ARRAYS_EQ(expected_digest, kExpectedKmac256Digest, 64);
  LOG_INFO("KMAC-256 vector payload verified against golden values.");

  LOG_INFO("Executing KMAC-256 using KMAC hardware accelerator...");
  CHECK(kmac_kmac256_sw_configure() == kErrorOk,
        "Failed to configure KMAC for KMAC-256!");

  // Key array in words (32 bytes = 8 words)
  uint32_t key_words[8];
  memcpy(key_words, key, sizeof(key_words));
  CHECK(kmac_kmac256_sw_key(key_words, 8) == kErrorOk,
        "Failed to load software key into KMAC!");

  const char prefix[] = "My Tagged Application";
  kmac_kmac256_set_prefix(prefix, sizeof(prefix) - 1);

  CHECK(kmac_kmac256_start() == kErrorOk, "Failed to start KMAC-256!");
  kmac_kmac256_absorb(msg, kat_data->msg_len);

  uint32_t act_digest_words[16];
  CHECK(kmac_kmac256_final(act_digest_words, 16) == kErrorOk,
        "Failed to finalize KMAC-256!");

  CHECK_ARRAYS_EQ((const uint8_t *)act_digest_words, expected_digest, 64);
  LOG_INFO("KMAC-256 Known Answer Test check ok.");

  return OK_STATUS();
}

static status_t test_aes_ecb256_kat(const fips_kat_descriptor_table_t *table) {
  LOG_INFO("Searching for AES-256-ECB Decrypt KAT entry (alg_id = %u)...",
           kFipsKatAlgAesEcb256Decrypt);
  const fips_kat_entry_t *entry =
      find_fips_entry(table, kFipsKatAlgAesEcb256Decrypt);
  CHECK(entry != NULL, "AES-256-ECB Decrypt KAT entry not found in table!");
  LOG_INFO("Entry found: algorithm_id=%u, offset=%u, size=%u",
           entry->algorithm_id, entry->offset, entry->size);

  LOG_INFO("Resolving AES-256-ECB KAT data payload...");
  const void *data = get_fips_data(table, entry);
  CHECK(data != NULL, "Failed to resolve KAT data payload (out of bounds)!");

  const aes_kat_data_t *kat_data = (const aes_kat_data_t *)data;
  CHECK(kat_data->key_len == 32, "Expected key_len=32, got %u",
        kat_data->key_len);
  CHECK(kat_data->iv_len == 0, "Expected iv_len=0, got %u", kat_data->iv_len);
  CHECK(kat_data->aad_len == 0, "Expected aad_len=0, got %u",
        kat_data->aad_len);
  CHECK(kat_data->pt_len == 16, "Expected pt_len=16, got %u", kat_data->pt_len);
  CHECK(kat_data->ct_len == 16, "Expected ct_len=16, got %u", kat_data->ct_len);
  CHECK(kat_data->tag_len == 0, "Expected tag_len=0, got %u",
        kat_data->tag_len);

  const uint8_t *key = kat_data->data;
  const uint8_t *expected_pt = kat_data->data + kat_data->key_len;
  const uint8_t *ct = kat_data->data + kat_data->key_len + kat_data->pt_len;

  CHECK_ARRAYS_EQ(key, kExpectedAes256Key, 32);
  CHECK_ARRAYS_EQ(expected_pt, kExpectedAes256EcbPt, 16);
  CHECK_ARRAYS_EQ(ct, kExpectedAes256EcbCt, 16);
  LOG_INFO("AES-256-ECB vector payload verified against golden values.");

  LOG_INFO(
      "Executing AES-256-ECB decryption using AES hardware accelerator...");
  dif_aes_t aes;
  CHECK_DIF_OK(dif_aes_init_from_dt(kDtAes, &aes));
  CHECK_DIF_OK(dif_aes_reset(&aes));

  dif_aes_transaction_t transaction = {
      .operation = kDifAesOperationDecrypt,
      .mode = kDifAesModeEcb,
      .key_len = kDifAesKey256,
      .key_provider = kDifAesKeySoftwareProvided,
      .mask_reseeding = kDifAesReseedPer8kBlock,
      .manual_operation = kDifAesManualOperationAuto,
      .reseed_on_key_change = false,
      .ctrl_aux_lock = false,
  };

  dif_aes_key_share_t key_shares;
  memcpy(key_shares.share0, key, 32);
  memset(key_shares.share1, 0, sizeof(key_shares.share1));

  CHECK_DIF_OK(dif_aes_start(&aes, &transaction, &key_shares, /*iv=*/NULL));

  dif_aes_data_t in_data;
  memcpy(in_data.data, ct, 16);

  bool input_ready = false;
  for (size_t i = 0; i < 1000000; ++i) {
    CHECK_DIF_OK(
        dif_aes_get_status(&aes, kDifAesStatusInputReady, &input_ready));
    if (input_ready) {
      break;
    }
  }
  CHECK(input_ready, "Timed out waiting for AES input ready!");

  CHECK_DIF_OK(dif_aes_load_data(&aes, in_data));

  bool output_valid = false;
  for (size_t i = 0; i < 1000000; ++i) {
    CHECK_DIF_OK(
        dif_aes_get_status(&aes, kDifAesStatusOutputValid, &output_valid));
    if (output_valid) {
      break;
    }
  }
  CHECK(output_valid, "Timed out waiting for AES output valid!");

  dif_aes_data_t out_data;
  CHECK_DIF_OK(dif_aes_read_output(&aes, &out_data));
  CHECK_DIF_OK(dif_aes_end(&aes));

  CHECK_ARRAYS_EQ((const uint8_t *)out_data.data, expected_pt, 16);
  LOG_INFO("AES-256-ECB Decrypt Known Answer Test check ok.");

  return OK_STATUS();
}

static status_t test_aes_cbc256_kat(const fips_kat_descriptor_table_t *table) {
  LOG_INFO("Searching for AES-256-CBC Decrypt KAT entry (alg_id = %u)...",
           kFipsKatAlgAesCbc256Decrypt);
  const fips_kat_entry_t *entry =
      find_fips_entry(table, kFipsKatAlgAesCbc256Decrypt);
  CHECK(entry != NULL, "AES-256-CBC Decrypt KAT entry not found in table!");
  LOG_INFO("Entry found: algorithm_id=%u, offset=%u, size=%u",
           entry->algorithm_id, entry->offset, entry->size);

  LOG_INFO("Resolving AES-256-CBC KAT data payload...");
  const void *data = get_fips_data(table, entry);
  CHECK(data != NULL, "Failed to resolve KAT data payload (out of bounds)!");

  const aes_kat_data_t *kat_data = (const aes_kat_data_t *)data;
  CHECK(kat_data->key_len == 32, "Expected key_len=32, got %u",
        kat_data->key_len);
  CHECK(kat_data->iv_len == 16, "Expected iv_len=16, got %u", kat_data->iv_len);
  CHECK(kat_data->aad_len == 0, "Expected aad_len=0, got %u",
        kat_data->aad_len);
  CHECK(kat_data->pt_len == 16, "Expected pt_len=16, got %u", kat_data->pt_len);
  CHECK(kat_data->ct_len == 16, "Expected ct_len=16, got %u", kat_data->ct_len);
  CHECK(kat_data->tag_len == 0, "Expected tag_len=0, got %u",
        kat_data->tag_len);

  const uint8_t *key = kat_data->data;
  const uint8_t *iv = kat_data->data + kat_data->key_len;
  const uint8_t *expected_pt =
      kat_data->data + kat_data->key_len + kat_data->iv_len;
  const uint8_t *ct =
      kat_data->data + kat_data->key_len + kat_data->iv_len + kat_data->pt_len;

  CHECK_ARRAYS_EQ(key, kExpectedAes256Key, 32);
  CHECK_ARRAYS_EQ(iv, kExpectedAes256CbcIv, 16);
  CHECK_ARRAYS_EQ(expected_pt, kExpectedAes256CbcPt, 16);
  CHECK_ARRAYS_EQ(ct, kExpectedAes256CbcCt, 16);
  LOG_INFO("AES-256-CBC vector payload verified against golden values.");

  LOG_INFO(
      "Executing AES-256-CBC decryption using AES hardware accelerator...");
  dif_aes_t aes;
  CHECK_DIF_OK(dif_aes_init_from_dt(kDtAes, &aes));
  CHECK_DIF_OK(dif_aes_reset(&aes));

  dif_aes_transaction_t transaction = {
      .operation = kDifAesOperationDecrypt,
      .mode = kDifAesModeCbc,
      .key_len = kDifAesKey256,
      .key_provider = kDifAesKeySoftwareProvided,
      .mask_reseeding = kDifAesReseedPer8kBlock,
      .manual_operation = kDifAesManualOperationAuto,
      .reseed_on_key_change = false,
      .ctrl_aux_lock = false,
  };

  dif_aes_key_share_t key_shares;
  memcpy(key_shares.share0, key, 32);
  memset(key_shares.share1, 0, sizeof(key_shares.share1));

  dif_aes_iv_t aes_iv;
  memcpy(aes_iv.iv, iv, 16);

  CHECK_DIF_OK(dif_aes_start(&aes, &transaction, &key_shares, &aes_iv));

  dif_aes_data_t in_data;
  memcpy(in_data.data, ct, 16);

  bool input_ready = false;
  for (size_t i = 0; i < 1000000; ++i) {
    CHECK_DIF_OK(
        dif_aes_get_status(&aes, kDifAesStatusInputReady, &input_ready));
    if (input_ready) {
      break;
    }
  }
  CHECK(input_ready, "Timed out waiting for AES input ready!");

  CHECK_DIF_OK(dif_aes_load_data(&aes, in_data));

  bool output_valid = false;
  for (size_t i = 0; i < 1000000; ++i) {
    CHECK_DIF_OK(
        dif_aes_get_status(&aes, kDifAesStatusOutputValid, &output_valid));
    if (output_valid) {
      break;
    }
  }
  CHECK(output_valid, "Timed out waiting for AES output valid!");

  dif_aes_data_t out_data;
  CHECK_DIF_OK(dif_aes_read_output(&aes, &out_data));
  CHECK_DIF_OK(dif_aes_end(&aes));

  CHECK_ARRAYS_EQ((const uint8_t *)out_data.data, expected_pt, 16);
  LOG_INFO("AES-256-CBC Decrypt Known Answer Test check ok.");

  return OK_STATUS();
}

static status_t test_aes_kwp256_kat(const fips_kat_descriptor_table_t *table) {
  LOG_INFO("Searching for AES-KWP-256 Wrap KAT entry (alg_id = %u)...",
           kFipsKatAlgAesKwp256Wrap);
  const fips_kat_entry_t *entry =
      find_fips_entry(table, kFipsKatAlgAesKwp256Wrap);
  CHECK(entry != NULL, "AES-KWP-256 Wrap KAT entry not found in table!");
  LOG_INFO("Entry found: algorithm_id=%u, offset=%u, size=%u",
           entry->algorithm_id, entry->offset, entry->size);

  LOG_INFO("Resolving AES-KWP-256 KAT data payload...");
  const void *data = get_fips_data(table, entry);
  CHECK(data != NULL, "Failed to resolve KAT data payload (out of bounds)!");

  const aes_kat_data_t *kat_data = (const aes_kat_data_t *)data;
  CHECK(kat_data->key_len == 32, "Expected key_len=32, got %u",
        kat_data->key_len);
  CHECK(kat_data->iv_len == 0, "Expected iv_len=0, got %u", kat_data->iv_len);
  CHECK(kat_data->aad_len == 0, "Expected aad_len=0, got %u",
        kat_data->aad_len);
  CHECK(kat_data->pt_len == 16, "Expected pt_len=16, got %u", kat_data->pt_len);
  CHECK(kat_data->ct_len == 24, "Expected ct_len=24, got %u", kat_data->ct_len);
  CHECK(kat_data->tag_len == 0, "Expected tag_len=0, got %u",
        kat_data->tag_len);

  const uint8_t *key = kat_data->data;
  const uint8_t *pt = kat_data->data + kat_data->key_len;
  const uint8_t *expected_ct =
      kat_data->data + kat_data->key_len + kat_data->pt_len;

  CHECK_ARRAYS_EQ(key, kExpectedAes256Key, 32);
  CHECK_ARRAYS_EQ(pt, kExpectedAes256EcbPt, 16);
  CHECK_ARRAYS_EQ(expected_ct, kExpectedAesKwp256Ct, 24);
  LOG_INFO("AES-KWP-256 vector payload verified against golden values.");

  LOG_INFO("Executing AES-KWP-256 wrapping using AES hardware accelerator...");
  dif_aes_t aes;
  CHECK_DIF_OK(dif_aes_init_from_dt(kDtAes, &aes));
  CHECK_DIF_OK(dif_aes_reset(&aes));

  dif_aes_transaction_t transaction = {
      .operation = kDifAesOperationEncrypt,
      .mode = kDifAesModeEcb,
      .key_len = kDifAesKey256,
      .key_provider = kDifAesKeySoftwareProvided,
      .mask_reseeding = kDifAesReseedPer8kBlock,
      .manual_operation = kDifAesManualOperationAuto,
      .reseed_on_key_change = false,
      .ctrl_aux_lock = false,
  };

  dif_aes_key_share_t key_shares;
  memcpy(key_shares.share0, key, 32);
  memset(key_shares.share1, 0, sizeof(key_shares.share1));

  CHECK_DIF_OK(dif_aes_start(&aes, &transaction, &key_shares, /*iv=*/NULL));

  // Initialize semiblocks A, R[0], R[1]
  // A = 0xA65959A6 || 32-bit big-endian length (16 = 0x00000010)
  uint8_t a[8] = {0xa6, 0x59, 0x59, 0xa6, 0x00, 0x00, 0x00, 0x10};
  uint8_t r[2][8];
  memcpy(r[0], pt, 8);
  memcpy(r[1], pt + 8, 8);

  uint64_t t = 1;
  for (size_t j = 0; j < 6; ++j) {
    for (size_t i = 0; i < 2; ++i) {
      dif_aes_data_t in_block;
      memcpy(&in_block.data[0], a, 8);
      memcpy(&in_block.data[2], r[i], 8);

      bool input_ready = false;
      for (size_t k = 0; k < 1000000; ++k) {
        CHECK_DIF_OK(
            dif_aes_get_status(&aes, kDifAesStatusInputReady, &input_ready));
        if (input_ready)
          break;
      }
      CHECK(input_ready, "Timed out waiting for AES input ready!");

      CHECK_DIF_OK(dif_aes_load_data(&aes, in_block));

      bool output_valid = false;
      for (size_t k = 0; k < 1000000; ++k) {
        CHECK_DIF_OK(
            dif_aes_get_status(&aes, kDifAesStatusOutputValid, &output_valid));
        if (output_valid)
          break;
      }
      CHECK(output_valid, "Timed out waiting for AES output valid!");

      dif_aes_data_t out_block;
      CHECK_DIF_OK(dif_aes_read_output(&aes, &out_block));

      memcpy(a, &out_block.data[0], 8);
      uint64_t a_val = ((uint64_t)a[0] << 56) | ((uint64_t)a[1] << 48) |
                       ((uint64_t)a[2] << 40) | ((uint64_t)a[3] << 32) |
                       ((uint64_t)a[4] << 24) | ((uint64_t)a[5] << 16) |
                       ((uint64_t)a[6] << 8) | ((uint64_t)a[7]);
      a_val ^= t;
      a[0] = (uint8_t)(a_val >> 56);
      a[1] = (uint8_t)(a_val >> 48);
      a[2] = (uint8_t)(a_val >> 40);
      a[3] = (uint8_t)(a_val >> 32);
      a[4] = (uint8_t)(a_val >> 24);
      a[5] = (uint8_t)(a_val >> 16);
      a[6] = (uint8_t)(a_val >> 8);
      a[7] = (uint8_t)(a_val);

      memcpy(r[i], &out_block.data[2], 8);
      t++;
    }
  }

  CHECK_DIF_OK(dif_aes_end(&aes));

  uint8_t computed_ct[24];
  memcpy(computed_ct, a, 8);
  memcpy(computed_ct + 8, r[0], 8);
  memcpy(computed_ct + 16, r[1], 8);

  CHECK_ARRAYS_EQ(computed_ct, expected_ct, 24);
  LOG_INFO("AES-KWP-256 Wrap Known Answer Test check ok.");

  return OK_STATUS();
}

static status_t test_aes_gcm256_kat(const fips_kat_descriptor_table_t *table) {
  LOG_INFO("Searching for AES-256-GCM Encrypt KAT entry (alg_id = %u)...",
           kFipsKatAlgAesGcm256Encrypt);
  const fips_kat_entry_t *entry =
      find_fips_entry(table, kFipsKatAlgAesGcm256Encrypt);
  CHECK(entry != NULL, "AES-256-GCM Encrypt KAT entry not found in table!");
  LOG_INFO("Entry found: algorithm_id=%u, offset=%u, size=%u",
           entry->algorithm_id, entry->offset, entry->size);

  LOG_INFO("Resolving AES-256-GCM KAT data payload...");
  const void *data = get_fips_data(table, entry);
  CHECK(data != NULL, "Failed to resolve KAT data payload (out of bounds)!");

  const aes_kat_data_t *kat_data = (const aes_kat_data_t *)data;
  CHECK(kat_data->key_len == 32, "Expected key_len=32, got %u",
        kat_data->key_len);
  CHECK(kat_data->iv_len == 12, "Expected iv_len=12, got %u", kat_data->iv_len);
  CHECK(kat_data->aad_len == 0, "Expected aad_len=0, got %u",
        kat_data->aad_len);
  CHECK(kat_data->pt_len == 16, "Expected pt_len=16, got %u", kat_data->pt_len);
  CHECK(kat_data->ct_len == 16, "Expected ct_len=16, got %u", kat_data->ct_len);
  CHECK(kat_data->tag_len == 16, "Expected tag_len=16, got %u",
        kat_data->tag_len);

  const uint8_t *key = kat_data->data;
  const uint8_t *iv = kat_data->data + kat_data->key_len;
  const uint8_t *pt = kat_data->data + kat_data->key_len + kat_data->iv_len;
  const uint8_t *expected_ct =
      kat_data->data + kat_data->key_len + kat_data->iv_len + kat_data->pt_len;
  const uint8_t *expected_tag = kat_data->data + kat_data->key_len +
                                kat_data->iv_len + kat_data->pt_len +
                                kat_data->ct_len;

  CHECK_ARRAYS_EQ(key, kExpectedAesGcm256Key, 32);
  CHECK_ARRAYS_EQ(iv, kExpectedAesGcm256Iv, 12);
  CHECK_ARRAYS_EQ(pt, kExpectedAesGcm256Pt, 16);
  CHECK_ARRAYS_EQ(expected_ct, kExpectedAesGcm256Ct, 16);
  CHECK_ARRAYS_EQ(expected_tag, kExpectedAesGcm256Tag, 16);
  LOG_INFO("AES-256-GCM vector payload verified against golden values.");

  LOG_INFO(
      "Executing AES-256-GCM encryption using cryptolib (HW AES + SW "
      "GHASH)...");
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));
  const otcrypto_key_config_t kAesGcm256Config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeAesGcm,
      .key_length = 32,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t keyblob[keyblob_num_words(kAesGcm256Config)];
  static const uint32_t kTestMask[8] = {0};
  CHECK_STATUS_OK(keyblob_from_key_and_mask((const uint32_t *)key, kTestMask,
                                            kAesGcm256Config, keyblob));
  otcrypto_blinded_key_t blinded_key = {
      .config = kAesGcm256Config,
      .keyblob = keyblob,
      .keyblob_length = sizeof(keyblob),
      .checksum = 0,
  };
  blinded_key.checksum = otcrypto_integrity_blinded_checksum(&blinded_key);

  otcrypto_const_byte_buf_t pt_buf = otcrypto_make_const_byte_buf(pt, 16);
  otcrypto_const_byte_buf_t aad_buf = otcrypto_make_const_byte_buf(NULL, 0);
  uint32_t iv_words[3];
  memcpy(iv_words, iv, sizeof(iv_words));
  otcrypto_const_word32_buf_t iv_buf =
      otcrypto_make_const_word32_buf(iv_words, 3);

  uint8_t actual_ct[16];
  otcrypto_byte_buf_t ct_buf =
      otcrypto_make_byte_buf(actual_ct, sizeof(actual_ct));

  uint32_t actual_tag[4];
  otcrypto_word32_buf_t tag_buf = otcrypto_make_word32_buf(actual_tag, 4);

  CHECK_STATUS_OK(otcrypto_aes_gcm_encrypt(&blinded_key, &pt_buf, &iv_buf,
                                           &aad_buf, kOtcryptoAesGcmTagLen128,
                                           &ct_buf, &tag_buf));

  CHECK_ARRAYS_EQ(actual_ct, expected_ct, 16);
  CHECK_ARRAYS_EQ((const uint8_t *)actual_tag, expected_tag, 16);
  LOG_INFO("AES-256-GCM Encrypt Known Answer Test check ok.");

  LOG_INFO(
      "Executing AES-256-GCM decryption using cryptolib (HW AES + SW "
      "GHASH)...");
  uint8_t actual_pt[16];
  otcrypto_byte_buf_t actual_pt_buf =
      otcrypto_make_byte_buf(actual_pt, sizeof(actual_pt));
  otcrypto_const_byte_buf_t const_ct_buf =
      otcrypto_make_const_byte_buf(expected_ct, 16);
  otcrypto_const_word32_buf_t const_tag_buf =
      otcrypto_make_const_word32_buf((const uint32_t *)expected_tag, 4);
  hardened_bool_t success = kHardenedBoolFalse;

  CHECK_STATUS_OK(otcrypto_aes_gcm_decrypt(
      &blinded_key, &const_ct_buf, &iv_buf, &aad_buf, kOtcryptoAesGcmTagLen128,
      &const_tag_buf, &actual_pt_buf, &success));
  CHECK(success == kHardenedBoolTrue,
        "AES-256-GCM decryption tag check failed!");
  CHECK_ARRAYS_EQ(actual_pt, pt, 16);
  LOG_INFO("AES-256-GCM Decrypt Known Answer Test check ok.");

  return OK_STATUS();
}

static status_t test_drbg_aes256_kat(const fips_kat_descriptor_table_t *table) {
  LOG_INFO("Searching for CTR_DRBG AES-256 KAT entry (alg_id = %u)...",
           kFipsKatAlgDrbgAes256);
  const fips_kat_entry_t *entry = find_fips_entry(table, kFipsKatAlgDrbgAes256);
  CHECK(entry != NULL, "CTR_DRBG AES-256 KAT entry not found in table!");
  LOG_INFO("Entry found: algorithm_id=%u, offset=%u, size=%u",
           entry->algorithm_id, entry->offset, entry->size);

  LOG_INFO("Resolving CTR_DRBG AES-256 KAT data payload...");
  const void *data = get_fips_data(table, entry);
  CHECK(data != NULL, "Failed to resolve KAT data payload (out of bounds)!");

  const drbg_kat_data_t *kat_data = (const drbg_kat_data_t *)data;
  CHECK(kat_data->entropy_input_len == 48,
        "Expected entropy_input_len=48, got %u", kat_data->entropy_input_len);
  CHECK(kat_data->expected_output_len == 64,
        "Expected expected_output_len=64, got %u",
        kat_data->expected_output_len);

  const uint8_t *entropy_input = kat_data->data;
  const uint8_t *expected_output = kat_data->data + kat_data->entropy_input_len;

  CHECK_ARRAYS_EQ(entropy_input, kExpectedDrbgEntropyInput, 48);
  CHECK_ARRAYS_EQ(expected_output, kExpectedDrbgOutput, 64);
  LOG_INFO("CTR_DRBG AES-256 vector payload verified against golden values.");

  LOG_INFO("Executing CTR_DRBG AES-256 test using cryptolib DRBG driver...");
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

  otcrypto_const_byte_buf_t kEmptyBuffer =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 0);
  otcrypto_const_byte_buf_t entropy = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, entropy_input, kat_data->entropy_input_len);

  // 1. Manual instantiate with 48 bytes of seed (32B entropy + 16B nonce).
  CHECK_STATUS_OK(otcrypto_drbg_manual_instantiate(&entropy, &kEmptyBuffer));

  // 2. Generate output twice as required by NIST SP 800-90A.
  uint32_t actual_output_words[16];
  otcrypto_word32_buf_t actual_output =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, actual_output_words,
                        ARRAYSIZE(actual_output_words));

  CHECK_STATUS_OK(otcrypto_drbg_manual_generate(&kEmptyBuffer, &actual_output));
  CHECK_STATUS_OK(otcrypto_drbg_manual_generate(&kEmptyBuffer, &actual_output));

  // 3. Compare second generate output against expected golden output.
  CHECK_ARRAYS_EQ((const uint8_t *)actual_output_words, expected_output, 64);
  LOG_INFO("CTR_DRBG AES-256 output matches expected golden vector.");

  // 4. Clean up and uninstantiate.
  CHECK_STATUS_OK(otcrypto_drbg_uninstantiate());
  LOG_INFO("CTR_DRBG AES-256 Known Answer Test check ok.");

  return OK_STATUS();
}

static status_t test_kdf_hmac_sha256_kat(
    const fips_kat_descriptor_table_t *table) {
  LOG_INFO("Searching for KDF-HMAC-SHA2-256 KAT entry (alg_id = %u)...",
           kFipsKatAlgKdfHmacSha2_256);
  const fips_kat_entry_t *entry =
      find_fips_entry(table, kFipsKatAlgKdfHmacSha2_256);
  CHECK(entry != NULL, "KDF-HMAC-SHA2-256 KAT entry not found in table!");
  LOG_INFO("Entry found: algorithm_id=%u, offset=%u, size=%u",
           entry->algorithm_id, entry->offset, entry->size);

  LOG_INFO("Resolving KDF-HMAC-SHA2-256 KAT data payload...");
  const void *data = get_fips_data(table, entry);
  CHECK(data != NULL, "Failed to resolve KAT data payload (out of bounds)!");

  const hmac_kat_data_t *kat_data = (const hmac_kat_data_t *)data;
  CHECK(kat_data->key_len == 32, "Expected key_len=32, got %u",
        kat_data->key_len);
  CHECK(kat_data->msg_len == 21, "Expected msg_len=21, got %u",
        kat_data->msg_len);
  CHECK(kat_data->digest_len == 32, "Expected digest_len=32, got %u",
        kat_data->digest_len);

  const uint8_t *kdk = kat_data->data;
  const uint8_t *msg = kat_data->data + kat_data->key_len;
  const uint8_t *expected_km =
      kat_data->data + kat_data->key_len + ((kat_data->msg_len + 3) & ~3u);

  CHECK_ARRAYS_EQ(kdk, kExpectedKdfHmacSha256Kdk, 32);
  CHECK_ARRAYS_EQ(msg, kExpectedKdfHmacSha256Msg, 21);
  CHECK_ARRAYS_EQ(expected_km, kExpectedKdfHmacSha256Km, 32);
  LOG_INFO("KDF-HMAC-SHA2-256 vector payload verified against golden values.");

  LOG_INFO("Executing KDF-HMAC-SHA2-256 using HMAC hardware accelerator...");
  hmac_key_t hkey;
  for (size_t i = 0; i < 8; ++i) {
    hkey.key[i] = (uint32_t)kdk[4 * i] | ((uint32_t)kdk[4 * i + 1] << 8) |
                  ((uint32_t)kdk[4 * i + 2] << 16) |
                  ((uint32_t)kdk[4 * i + 3] << 24);
  }
  hmac_digest_t digest;
  sc_hmac_hmac_sha256(msg, kat_data->msg_len, hkey,
                      /*big_endian_digest=*/false, &digest);

  uint8_t computed_km[32];
  for (size_t i = 0; i < 8; ++i) {
    uint32_t word = digest.digest[7 - i];
    computed_km[4 * i] = (uint8_t)(word >> 24);
    computed_km[4 * i + 1] = (uint8_t)(word >> 16);
    computed_km[4 * i + 2] = (uint8_t)(word >> 8);
    computed_km[4 * i + 3] = (uint8_t)(word);
  }

  CHECK_ARRAYS_EQ(computed_km, expected_km, 32);
  LOG_INFO("KDF-HMAC-SHA2-256 Known Answer Test check ok.");

  return OK_STATUS();
}

static status_t test_kdf_kmac256_kat(const fips_kat_descriptor_table_t *table) {
  LOG_INFO("Searching for KDF-KMAC-256 KAT entry (alg_id = %u)...",
           kFipsKatAlgKdfKmac256);
  const fips_kat_entry_t *entry = find_fips_entry(table, kFipsKatAlgKdfKmac256);
  CHECK(entry != NULL, "KDF-KMAC-256 KAT entry not found in table!");
  LOG_INFO("Entry found: algorithm_id=%u, offset=%u, size=%u",
           entry->algorithm_id, entry->offset, entry->size);

  LOG_INFO("Resolving KDF-KMAC-256 KAT data payload...");
  const void *data = get_fips_data(table, entry);
  CHECK(data != NULL, "Failed to resolve KAT data payload (out of bounds)!");

  const hmac_kat_data_t *kat_data = (const hmac_kat_data_t *)data;
  CHECK(kat_data->key_len == 32, "Expected key_len=32, got %u",
        kat_data->key_len);
  CHECK(kat_data->msg_len == 4, "Expected msg_len=4, got %u",
        kat_data->msg_len);
  CHECK(kat_data->digest_len == 64, "Expected digest_len=64, got %u",
        kat_data->digest_len);

  const uint8_t *kdk = kat_data->data;
  const uint8_t *context = kat_data->data + kat_data->key_len;
  const uint8_t *expected_km =
      kat_data->data + kat_data->key_len + kat_data->msg_len;

  CHECK_ARRAYS_EQ(kdk, kExpectedKmac256Key, 32);
  CHECK_ARRAYS_EQ(context, kExpectedKmac256Msg, 4);
  CHECK_ARRAYS_EQ(expected_km, kExpectedKmac256Digest, 64);
  LOG_INFO("KDF-KMAC-256 vector payload verified against golden values.");

  LOG_INFO("Executing KDF-KMAC-256 using KMAC hardware accelerator...");
  CHECK(kmac_kmac256_sw_configure() == kErrorOk,
        "Failed to configure KMAC for KDF-KMAC-256!");

  uint32_t key_words[8];
  memcpy(key_words, kdk, sizeof(key_words));
  CHECK(kmac_kmac256_sw_key(key_words, 8) == kErrorOk,
        "Failed to load software key into KMAC!");

  const char prefix[] = "My Tagged Application";
  kmac_kmac256_set_prefix(prefix, sizeof(prefix) - 1);

  CHECK(kmac_kmac256_start() == kErrorOk, "Failed to start KMAC-256!");
  kmac_kmac256_absorb(context, kat_data->msg_len);

  uint32_t act_digest_words[16];
  CHECK(kmac_kmac256_final(act_digest_words, 16) == kErrorOk,
        "Failed to finalize KMAC-256!");

  CHECK_ARRAYS_EQ((const uint8_t *)act_digest_words, expected_km, 64);
  LOG_INFO("KDF-KMAC-256 Known Answer Test check ok.");

  return OK_STATUS();
}

static status_t test_rsa4096_sign_kat(
    const fips_kat_descriptor_table_t *table) {
  LOG_INFO("Searching for RSA-4096 Sign KAT entry (alg_id = %u)...",
           kFipsKatAlgRsa4096Sign);
  const fips_kat_entry_t *entry =
      find_fips_entry(table, kFipsKatAlgRsa4096Sign);
  CHECK(entry != NULL, "RSA-4096 Sign KAT entry not found in table!");
  LOG_INFO("Entry found: algorithm_id=%u, offset=%u, size=%u",
           entry->algorithm_id, entry->offset, entry->size);

  LOG_INFO("Resolving RSA-4096 KAT data payload...");
  const void *data = get_fips_data(table, entry);
  CHECK(data != NULL, "Failed to resolve KAT data payload (out of bounds)!");

  const asymmetric_sign_kat_data_t *kat_data =
      (const asymmetric_sign_kat_data_t *)data;
  CHECK(kat_data->priv_key_len == 1024, "Expected priv_key_len=1024, got %u",
        kat_data->priv_key_len);
  CHECK(kat_data->ephemeral_len == 0, "Expected ephemeral_len=0, got %u",
        kat_data->ephemeral_len);
  CHECK(kat_data->msg_len == 13, "Expected msg_len=13, got %u",
        kat_data->msg_len);
  CHECK(kat_data->sig_len1 == 512, "Expected sig_len1=512, got %u",
        kat_data->sig_len1);
  CHECK(kat_data->sig_len2 == 0, "Expected sig_len2=0, got %u",
        kat_data->sig_len2);

  const uint32_t *modulus = (const uint32_t *)kat_data->data;
  const uint32_t *d_share0 = (const uint32_t *)(kat_data->data + 512);
  const uint8_t *msg = kat_data->data + kat_data->priv_key_len;
  const uint8_t *expected_sig =
      kat_data->data + kat_data->priv_key_len + ((kat_data->msg_len + 3) & ~3u);

  LOG_INFO("Executing RSA-4096 PKCS#1 v1.5 signing using OTBN coprocessor...");
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

  otcrypto_const_word32_buf_t mod_buf =
      otcrypto_make_const_word32_buf(modulus, 512 / sizeof(uint32_t));
  otcrypto_const_word32_buf_t d0_buf =
      otcrypto_make_const_word32_buf(d_share0, 512 / sizeof(uint32_t));
  static uint32_t zero_share_4096[512 / sizeof(uint32_t)];
  memset(zero_share_4096, 0, sizeof(zero_share_4096));
  otcrypto_const_word32_buf_t d1_buf =
      otcrypto_make_const_word32_buf(zero_share_4096, 512 / sizeof(uint32_t));

  otcrypto_key_config_t private_key_config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeRsaSignPkcs,
      .key_length = kOtcryptoRsa4096PrivateKeyBytes,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  static uint32_t
      keyblob_4096[kOtcryptoRsa4096PrivateKeyblobBytes / sizeof(uint32_t)];
  otcrypto_blinded_key_t private_key = {
      .config = private_key_config,
      .keyblob = keyblob_4096,
      .keyblob_length = kOtcryptoRsa4096PrivateKeyblobBytes,
  };
  CHECK_STATUS_OK(otcrypto_rsa_private_key_from_exponents(
      kOtcryptoRsaSize4096, &mod_buf, &d0_buf, &d1_buf, &private_key));

  // Compute SHA2-512 digest of msg
  static uint32_t digest_words_4096_sign[512 / 32];
  otcrypto_hash_digest_t msg_digest = {
      .mode = kOtcryptoHashModeSha512,
      .len = 512 / 32,
      .data = digest_words_4096_sign,
  };
  otcrypto_const_byte_buf_t msg_buf =
      otcrypto_make_const_byte_buf(msg, kat_data->msg_len);
  CHECK_STATUS_OK(otcrypto_sha2_512(&msg_buf, &msg_digest));

  static uint32_t act_sig_4096[512 / sizeof(uint32_t)];
  otcrypto_word32_buf_t sig_buf =
      otcrypto_make_word32_buf(act_sig_4096, 512 / sizeof(uint32_t));

  LOG_INFO("Calling otcrypto_rsa_sign...");
  CHECK_STATUS_OK(otcrypto_rsa_sign(&private_key, msg_digest,
                                    kOtcryptoRsaPaddingPkcs, &sig_buf));

  CHECK_ARRAYS_EQ((const uint8_t *)act_sig_4096, expected_sig, 512);
  LOG_INFO("RSA-4096 PKCS#1 v1.5 Signing Known Answer Test check ok.");

  return OK_STATUS();
}

static status_t test_rsa4096_verify_kat(
    const fips_kat_descriptor_table_t *table) {
  LOG_INFO("Searching for RSA-4096 Verify KAT entry (alg_id = %u)...",
           kFipsKatAlgRsa4096Verify);
  const fips_kat_entry_t *entry =
      find_fips_entry(table, kFipsKatAlgRsa4096Verify);
  CHECK(entry != NULL, "RSA-4096 Verify KAT entry not found in table!");
  LOG_INFO("Entry found: algorithm_id=%u, offset=%u, size=%u",
           entry->algorithm_id, entry->offset, entry->size);

  LOG_INFO("Resolving RSA-4096 KAT data payload...");
  const void *data = get_fips_data(table, entry);
  CHECK(data != NULL, "Failed to resolve KAT data payload (out of bounds)!");

  const asymmetric_verify_kat_data_t *kat_data =
      (const asymmetric_verify_kat_data_t *)data;
  CHECK(kat_data->pub_key_len1 == 512, "Expected pub_key_len1=512, got %u",
        kat_data->pub_key_len1);
  CHECK(kat_data->pub_key_len2 == 4, "Expected pub_key_len2=4, got %u",
        kat_data->pub_key_len2);
  CHECK(kat_data->msg_len == 13, "Expected msg_len=13, got %u",
        kat_data->msg_len);
  CHECK(kat_data->sig_len1 == 512, "Expected sig_len1=512, got %u",
        kat_data->sig_len1);
  CHECK(kat_data->sig_len2 == 0, "Expected sig_len2=0, got %u",
        kat_data->sig_len2);

  const uint32_t *modulus = (const uint32_t *)kat_data->data;
  const uint8_t *msg =
      kat_data->data + kat_data->pub_key_len1 + kat_data->pub_key_len2;
  const uint32_t *sig =
      (const uint32_t *)(kat_data->data + kat_data->pub_key_len1 +
                         kat_data->pub_key_len2 +
                         ((kat_data->msg_len + 3) & ~3u));

  LOG_INFO(
      "Executing RSA-4096 PKCS#1 v1.5 verification using OTBN coprocessor...");
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

  otcrypto_const_word32_buf_t mod_buf =
      otcrypto_make_const_word32_buf(modulus, 512 / sizeof(uint32_t));
  static uint32_t
      public_key_data_4096[kOtcryptoRsa4096PublicKeyBytes / sizeof(uint32_t)];
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeRsaSignPkcs,
      .key_length = kOtcryptoRsa4096PublicKeyBytes,
      .key = public_key_data_4096,
  };
  CHECK_STATUS_OK(otcrypto_rsa_public_key_construct(kOtcryptoRsaSize4096,
                                                    &mod_buf, &public_key));

  // Compute SHA2-512 digest of msg using cryptolib sha2
  static uint32_t digest_words_4096_verify[512 / 32];
  otcrypto_hash_digest_t msg_digest = {
      .mode = kOtcryptoHashModeSha512,
      .len = 512 / 32,
      .data = digest_words_4096_verify,
  };
  otcrypto_const_byte_buf_t msg_buf =
      otcrypto_make_const_byte_buf(msg, kat_data->msg_len);
  CHECK_STATUS_OK(otcrypto_sha2_512(&msg_buf, &msg_digest));

  otcrypto_const_word32_buf_t sig_buf =
      otcrypto_make_const_word32_buf(sig, 512 / sizeof(uint32_t));

  hardened_bool_t verification_result = kHardenedBoolFalse;
  LOG_INFO("Calling otcrypto_rsa_verify...");
  CHECK_STATUS_OK(otcrypto_rsa_verify(&public_key, msg_digest,
                                      kOtcryptoRsaPaddingPkcs, &sig_buf,
                                      &verification_result));

  CHECK(verification_result == kHardenedBoolTrue,
        "RSA-4096 signature verification failed!");
  LOG_INFO("RSA-4096 PKCS#1 v1.5 Verification Known Answer Test check ok.");

  return OK_STATUS();
}

static status_t test_ecdsa_p256_sign_kat(
    const fips_kat_descriptor_table_t *table) {
  LOG_INFO("Searching for ECDSA-P256 Sign KAT entry (alg_id = %u)...",
           kFipsKatAlgEcdsaP256Sign);
  const fips_kat_entry_t *entry =
      find_fips_entry(table, kFipsKatAlgEcdsaP256Sign);
  CHECK(entry != NULL, "ECDSA-P256 Sign KAT entry not found in table!");
  LOG_INFO("Entry found: algorithm_id=%u, offset=%u, size=%u",
           entry->algorithm_id, entry->offset, entry->size);

  LOG_INFO("Resolving ECDSA-P256 KAT data payload...");
  const void *data = get_fips_data(table, entry);
  CHECK(data != NULL, "Failed to resolve KAT data payload (out of bounds)!");

  const asymmetric_sign_kat_data_t *kat_data =
      (const asymmetric_sign_kat_data_t *)data;
  CHECK(kat_data->priv_key_len == 32, "Expected priv_key_len=32, got %u",
        kat_data->priv_key_len);
  CHECK(kat_data->ephemeral_len == 32, "Expected ephemeral_len=32, got %u",
        kat_data->ephemeral_len);
  CHECK(kat_data->msg_len == 32, "Expected msg_len=32, got %u",
        kat_data->msg_len);
  CHECK(kat_data->sig_len1 == 32, "Expected sig_len1=32, got %u",
        kat_data->sig_len1);
  CHECK(kat_data->sig_len2 == 32, "Expected sig_len2=32, got %u",
        kat_data->sig_len2);

  const uint8_t *d = kat_data->data;
  const uint8_t *k = kat_data->data + kat_data->priv_key_len;
  const uint8_t *msg_digest =
      kat_data->data + kat_data->priv_key_len + kat_data->ephemeral_len;
  const uint8_t *expected_sig = kat_data->data + kat_data->priv_key_len +
                                kat_data->ephemeral_len + kat_data->msg_len;

  LOG_INFO("Executing ECDSA-P256 signing using OTBN coprocessor...");
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

  const otcrypto_key_config_t kP256Config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = 32,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };

  uint32_t keyblob_sk[20] = {0};
  otcrypto_blinded_key_t private_key = {
      .config = kP256Config,
      .keyblob_length = sizeof(keyblob_sk),
      .keyblob = keyblob_sk,
      .checksum = 0,
  };
  memcpy(keyblob_sk, d, 32);
  private_key.checksum = otcrypto_integrity_blinded_checksum(&private_key);

  uint32_t keyblob_scalar[20] = {0};
  otcrypto_blinded_key_t secret_scalar = {
      .config = kP256Config,
      .keyblob_length = sizeof(keyblob_scalar),
      .keyblob = keyblob_scalar,
      .checksum = 0,
  };
  memcpy(keyblob_scalar, k, 32);
  secret_scalar.checksum = otcrypto_integrity_blinded_checksum(&secret_scalar);

  otcrypto_hash_digest_t digest = {
      .mode = kOtcryptoHashModeSha256,
      .len = 8,
      .data = (uint32_t *)msg_digest,
  };

  uint32_t sig[16];
  otcrypto_word32_buf_t sig_buf = otcrypto_make_word32_buf(sig, 16);

  CHECK_STATUS_OK(otcrypto_ecdsa_p256_sign_config_k(
      &private_key, &secret_scalar, digest, &sig_buf));

  CHECK_ARRAYS_EQ((const uint8_t *)sig, expected_sig, 64);
  LOG_INFO("ECDSA-P256 Signing Known Answer Test check ok.");

  return OK_STATUS();
}

static status_t test_ecdsa_p256_verify_kat(
    const fips_kat_descriptor_table_t *table) {
  LOG_INFO("Searching for ECDSA-P256 Verify KAT entry (alg_id = %u)...",
           kFipsKatAlgEcdsaP256Verify);
  const fips_kat_entry_t *entry =
      find_fips_entry(table, kFipsKatAlgEcdsaP256Verify);
  CHECK(entry != NULL, "ECDSA-P256 Verify KAT entry not found in table!");
  LOG_INFO("Entry found: algorithm_id=%u, offset=%u, size=%u",
           entry->algorithm_id, entry->offset, entry->size);

  LOG_INFO("Resolving ECDSA-P256 KAT data payload...");
  const void *data = get_fips_data(table, entry);
  CHECK(data != NULL, "Failed to resolve KAT data payload (out of bounds)!");

  const asymmetric_verify_kat_data_t *kat_data =
      (const asymmetric_verify_kat_data_t *)data;
  CHECK(kat_data->pub_key_len1 == 32, "Expected pub_key_len1=32, got %u",
        kat_data->pub_key_len1);
  CHECK(kat_data->pub_key_len2 == 32, "Expected pub_key_len2=32, got %u",
        kat_data->pub_key_len2);
  CHECK(kat_data->msg_len == 32, "Expected msg_len=32, got %u",
        kat_data->msg_len);
  CHECK(kat_data->sig_len1 == 32, "Expected sig_len1=32, got %u",
        kat_data->sig_len1);
  CHECK(kat_data->sig_len2 == 32, "Expected sig_len2=32, got %u",
        kat_data->sig_len2);

  const uint8_t *public_key_raw = kat_data->data;
  const uint8_t *msg_digest =
      kat_data->data + kat_data->pub_key_len1 + kat_data->pub_key_len2;
  const uint8_t *sig_raw = kat_data->data + kat_data->pub_key_len1 +
                           kat_data->pub_key_len2 + kat_data->msg_len;

  LOG_INFO("Executing ECDSA-P256 verification using OTBN coprocessor...");
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = 64,
      .key = (uint32_t *)public_key_raw,
  };
  public_key.checksum = otcrypto_integrity_unblinded_checksum(&public_key);

  otcrypto_hash_digest_t digest = {
      .mode = kOtcryptoHashModeSha256,
      .len = 8,
      .data = (uint32_t *)msg_digest,
  };

  otcrypto_const_word32_buf_t sig_buf =
      otcrypto_make_const_word32_buf((const uint32_t *)sig_raw, 16);

  hardened_bool_t verification_result = kHardenedBoolFalse;
  CHECK_STATUS_OK(otcrypto_ecdsa_p256_verify(&public_key, digest, &sig_buf,
                                             &verification_result));

  CHECK(verification_result == kHardenedBoolTrue,
        "ECDSA-P256 signature verification failed!");
  LOG_INFO("ECDSA-P256 Verification Known Answer Test check ok.");

  return OK_STATUS();
}

static status_t test_ecdsa_p384_sign_kat(
    const fips_kat_descriptor_table_t *table) {
  LOG_INFO("Searching for ECDSA-P384 Sign KAT entry (alg_id = %u)...",
           kFipsKatAlgEcdsaP384Sign);
  const fips_kat_entry_t *entry =
      find_fips_entry(table, kFipsKatAlgEcdsaP384Sign);
  CHECK(entry != NULL, "ECDSA-P384 Sign KAT entry not found in table!");
  LOG_INFO("Entry found: algorithm_id=%u, offset=%u, size=%u",
           entry->algorithm_id, entry->offset, entry->size);

  LOG_INFO("Resolving ECDSA-P384 KAT data payload...");
  const void *data = get_fips_data(table, entry);
  CHECK(data != NULL, "Failed to resolve KAT data payload (out of bounds)!");

  const asymmetric_sign_kat_data_t *kat_data =
      (const asymmetric_sign_kat_data_t *)data;
  CHECK(kat_data->priv_key_len == 48, "Expected priv_key_len=48, got %u",
        kat_data->priv_key_len);
  CHECK(kat_data->ephemeral_len == 48, "Expected ephemeral_len=48, got %u",
        kat_data->ephemeral_len);
  CHECK(kat_data->msg_len == 48, "Expected msg_len=48, got %u",
        kat_data->msg_len);
  CHECK(kat_data->sig_len1 == 48, "Expected sig_len1=48, got %u",
        kat_data->sig_len1);
  CHECK(kat_data->sig_len2 == 48, "Expected sig_len2=48, got %u",
        kat_data->sig_len2);

  const uint8_t *d = kat_data->data;
  const uint8_t *k = kat_data->data + kat_data->priv_key_len;
  const uint8_t *msg_digest =
      kat_data->data + kat_data->priv_key_len + kat_data->ephemeral_len;
  const uint8_t *expected_sig = kat_data->data + kat_data->priv_key_len +
                                kat_data->ephemeral_len + kat_data->msg_len;

  LOG_INFO("Executing ECDSA-P384 signing using OTBN coprocessor...");
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

  const otcrypto_key_config_t kP384Config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeEcdsaP384,
      .key_length = 48,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };

  uint32_t keyblob_sk[28] = {0};
  otcrypto_blinded_key_t private_key = {
      .config = kP384Config,
      .keyblob_length = sizeof(keyblob_sk),
      .keyblob = keyblob_sk,
      .checksum = 0,
  };
  memcpy(keyblob_sk, d, 48);
  private_key.checksum = otcrypto_integrity_blinded_checksum(&private_key);

  uint32_t keyblob_scalar[28] = {0};
  otcrypto_blinded_key_t secret_scalar = {
      .config = kP384Config,
      .keyblob_length = sizeof(keyblob_scalar),
      .keyblob = keyblob_scalar,
      .checksum = 0,
  };
  memcpy(keyblob_scalar, k, 48);
  secret_scalar.checksum = otcrypto_integrity_blinded_checksum(&secret_scalar);

  otcrypto_hash_digest_t digest = {
      .mode = kOtcryptoHashModeSha384,
      .len = 12,
      .data = (uint32_t *)msg_digest,
  };

  uint32_t sig[24];
  otcrypto_word32_buf_t sig_buf = otcrypto_make_word32_buf(sig, 24);

  CHECK_STATUS_OK(otcrypto_ecdsa_p384_sign_config_k(
      &private_key, &secret_scalar, digest, &sig_buf));

  CHECK_ARRAYS_EQ((const uint8_t *)sig, expected_sig, 96);
  LOG_INFO("ECDSA-P384 Signing Known Answer Test check ok.");

  return OK_STATUS();
}

static status_t test_ecdsa_p384_verify_kat(
    const fips_kat_descriptor_table_t *table) {
  LOG_INFO("Searching for ECDSA-P384 Verify KAT entry (alg_id = %u)...",
           kFipsKatAlgEcdsaP384Verify);
  const fips_kat_entry_t *entry =
      find_fips_entry(table, kFipsKatAlgEcdsaP384Verify);
  CHECK(entry != NULL, "ECDSA-P384 Verify KAT entry not found in table!");
  LOG_INFO("Entry found: algorithm_id=%u, offset=%u, size=%u",
           entry->algorithm_id, entry->offset, entry->size);

  LOG_INFO("Resolving ECDSA-P384 KAT data payload...");
  const void *data = get_fips_data(table, entry);
  CHECK(data != NULL, "Failed to resolve KAT data payload (out of bounds)!");

  const asymmetric_verify_kat_data_t *kat_data =
      (const asymmetric_verify_kat_data_t *)data;
  CHECK(kat_data->pub_key_len1 == 48, "Expected pub_key_len1=48, got %u",
        kat_data->pub_key_len1);
  CHECK(kat_data->pub_key_len2 == 48, "Expected pub_key_len2=48, got %u",
        kat_data->pub_key_len2);
  CHECK(kat_data->msg_len == 48, "Expected msg_len=48, got %u",
        kat_data->msg_len);
  CHECK(kat_data->sig_len1 == 48, "Expected sig_len1=48, got %u",
        kat_data->sig_len1);
  CHECK(kat_data->sig_len2 == 48, "Expected sig_len2=48, got %u",
        kat_data->sig_len2);

  const uint8_t *public_key_raw = kat_data->data;
  const uint8_t *msg_digest =
      kat_data->data + kat_data->pub_key_len1 + kat_data->pub_key_len2;
  const uint8_t *sig_raw = kat_data->data + kat_data->pub_key_len1 +
                           kat_data->pub_key_len2 + kat_data->msg_len;

  LOG_INFO("Executing ECDSA-P384 verification using OTBN coprocessor...");
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdsaP384,
      .key_length = 96,
      .key = (uint32_t *)public_key_raw,
  };
  public_key.checksum = otcrypto_integrity_unblinded_checksum(&public_key);

  otcrypto_hash_digest_t digest = {
      .mode = kOtcryptoHashModeSha384,
      .len = 12,
      .data = (uint32_t *)msg_digest,
  };

  otcrypto_const_word32_buf_t sig_buf =
      otcrypto_make_const_word32_buf((const uint32_t *)sig_raw, 24);

  hardened_bool_t verification_result = kHardenedBoolFalse;
  CHECK_STATUS_OK(otcrypto_ecdsa_p384_verify(&public_key, digest, &sig_buf,
                                             &verification_result));

  CHECK(verification_result == kHardenedBoolTrue,
        "ECDSA-P384 signature verification failed!");
  LOG_INFO("ECDSA-P384 Verification Known Answer Test check ok.");

  return OK_STATUS();
}

static status_t test_ed25519_sign_kat(
    const fips_kat_descriptor_table_t *table) {
  LOG_INFO("Searching for Ed25519 Sign KAT entry (alg_id = %u)...",
           kFipsKatAlgEd25519Sign);
  const fips_kat_entry_t *entry =
      find_fips_entry(table, kFipsKatAlgEd25519Sign);
  CHECK(entry != NULL, "Ed25519 Sign KAT entry not found in table!");
  LOG_INFO("Entry found: algorithm_id=%u, offset=%u, size=%u",
           entry->algorithm_id, entry->offset, entry->size);

  LOG_INFO("Resolving Ed25519 KAT data payload...");
  const void *data = get_fips_data(table, entry);
  CHECK(data != NULL, "Failed to resolve KAT data payload (out of bounds)!");

  const asymmetric_sign_kat_data_t *kat_data =
      (const asymmetric_sign_kat_data_t *)data;
  CHECK(kat_data->priv_key_len == 32, "Expected priv_key_len=32, got %u",
        kat_data->priv_key_len);
  CHECK(kat_data->ephemeral_len == 0, "Expected ephemeral_len=0, got %u",
        kat_data->ephemeral_len);
  CHECK(kat_data->msg_len == 1, "Expected msg_len=1, got %u",
        kat_data->msg_len);
  CHECK(kat_data->sig_len1 == 32, "Expected sig_len1=32, got %u",
        kat_data->sig_len1);
  CHECK(kat_data->sig_len2 == 32, "Expected sig_len2=32, got %u",
        kat_data->sig_len2);

  const uint8_t *sk = kat_data->data;
  const uint8_t *msg = kat_data->data + kat_data->priv_key_len;
  const uint8_t *expected_sig =
      kat_data->data + kat_data->priv_key_len + ((kat_data->msg_len + 3) & ~3u);

  LOG_INFO("Executing Ed25519 signing using OTBN coprocessor...");
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

  const otcrypto_key_config_t kEd25519Config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeEd25519,
      .key_length = 32,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };

  uint32_t keyblob[20] = {0};
  otcrypto_blinded_key_t private_key = {
      .config = kEd25519Config,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
      .checksum = 0,
  };
  memcpy(keyblob, sk, 32);
  private_key.checksum = otcrypto_integrity_blinded_checksum(&private_key);

  otcrypto_const_byte_buf_t msg_buf =
      otcrypto_make_const_byte_buf(msg, kat_data->msg_len);

  uint32_t sig[16] = {0};
  otcrypto_word32_buf_t sig_buf = otcrypto_make_word32_buf(sig, 16);

  CHECK_STATUS_OK(otcrypto_ed25519_sign(&private_key, &msg_buf,
                                        kOtcryptoEddsaSignModeEddsa, &sig_buf));

  CHECK_ARRAYS_EQ((const uint8_t *)sig, expected_sig, 64);
  LOG_INFO("Ed25519 Signing Known Answer Test check ok.");

  return OK_STATUS();
}

static status_t test_ed25519_verify_kat(
    const fips_kat_descriptor_table_t *table) {
  LOG_INFO("Searching for Ed25519 Verify KAT entry (alg_id = %u)...",
           kFipsKatAlgEd25519Verify);
  const fips_kat_entry_t *entry =
      find_fips_entry(table, kFipsKatAlgEd25519Verify);
  CHECK(entry != NULL, "Ed25519 Verify KAT entry not found in table!");
  LOG_INFO("Entry found: algorithm_id=%u, offset=%u, size=%u",
           entry->algorithm_id, entry->offset, entry->size);

  LOG_INFO("Resolving Ed25519 Verify KAT data payload...");
  const void *data = get_fips_data(table, entry);
  CHECK(data != NULL, "Failed to resolve KAT data payload (out of bounds)!");

  const asymmetric_verify_kat_data_t *kat_data =
      (const asymmetric_verify_kat_data_t *)data;
  CHECK(kat_data->pub_key_len1 == 32, "Expected pub_key_len1=32, got %u",
        kat_data->pub_key_len1);
  CHECK(kat_data->pub_key_len2 == 0, "Expected pub_key_len2=0, got %u",
        kat_data->pub_key_len2);
  CHECK(kat_data->msg_len == 1, "Expected msg_len=1, got %u",
        kat_data->msg_len);
  CHECK(kat_data->sig_len1 == 32, "Expected sig_len1=32, got %u",
        kat_data->sig_len1);
  CHECK(kat_data->sig_len2 == 32, "Expected sig_len2=32, got %u",
        kat_data->sig_len2);

  const uint8_t *pk = kat_data->data;
  const uint8_t *msg = kat_data->data + kat_data->pub_key_len1;
  const uint8_t *sig_raw =
      kat_data->data + kat_data->pub_key_len1 + ((kat_data->msg_len + 3) & ~3u);

  LOG_INFO("Executing Ed25519 verification using OTBN coprocessor...");
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

  uint32_t pk_data[8];
  memcpy(pk_data, pk, 32);
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEd25519,
      .key_length = 32,
      .key = pk_data,
      .checksum = 0,
  };
  public_key.checksum = otcrypto_integrity_unblinded_checksum(&public_key);

  otcrypto_const_byte_buf_t msg_buf =
      otcrypto_make_const_byte_buf(msg, kat_data->msg_len);

  uint32_t sig_data[16];
  memcpy(sig_data, sig_raw, 64);
  otcrypto_const_word32_buf_t sig_buf =
      otcrypto_make_const_word32_buf(sig_data, 16);

  hardened_bool_t verification_result = kHardenedBoolFalse;
  CHECK_STATUS_OK(otcrypto_ed25519_verify(&public_key, &msg_buf,
                                          kOtcryptoEddsaSignModeEddsa, &sig_buf,
                                          &verification_result));

  CHECK(verification_result == kHardenedBoolTrue,
        "Ed25519 signature verification failed!");
  LOG_INFO("Ed25519 Verification Known Answer Test check ok.");

  return OK_STATUS();
}

static status_t test_sphincsplus_sha2_128s_verify_kat(
    const fips_kat_descriptor_table_t *table) {
  LOG_INFO("Searching for SPHINCS+-SHA2-128s Verify KAT entry (alg_id = %u)...",
           kFipsKatAlgSphincsPlusSha2_128sVerify);
  const fips_kat_entry_t *entry =
      find_fips_entry(table, kFipsKatAlgSphincsPlusSha2_128sVerify);
  CHECK(entry != NULL,
        "SPHINCS+-SHA2-128s Verify KAT entry not found in table!");
  LOG_INFO("Entry found: algorithm_id=%u, offset=%u, size=%u",
           entry->algorithm_id, entry->offset, entry->size);

  LOG_INFO("Resolving SPHINCS+-SHA2-128s Verify KAT data payload...");
  const void *data = get_fips_data(table, entry);
  CHECK(data != NULL, "Failed to resolve KAT data payload (out of bounds)!");

  const asymmetric_verify_kat_data_t *kat_data =
      (const asymmetric_verify_kat_data_t *)data;
  CHECK(kat_data->pub_key_len1 == 32, "Expected pub_key_len1=32, got %u",
        kat_data->pub_key_len1);
  CHECK(kat_data->pub_key_len2 == 0, "Expected pub_key_len2=0, got %u",
        kat_data->pub_key_len2);
  CHECK(kat_data->msg_len == 33, "Expected msg_len=33, got %u",
        kat_data->msg_len);
  CHECK(kat_data->sig_len1 == 7856, "Expected sig_len1=7856, got %u",
        kat_data->sig_len1);
  CHECK(kat_data->sig_len2 == 0, "Expected sig_len2=0, got %u",
        kat_data->sig_len2);

  const uint8_t *pk_bytes = kat_data->data;
  const uint8_t *msg_bytes = kat_data->data + kat_data->pub_key_len1;
  const uint8_t *sig_bytes =
      kat_data->data + kat_data->pub_key_len1 + ((kat_data->msg_len + 3) & ~3u);

  CHECK_ARRAYS_EQ(pk_bytes, kExpectedSphincsPlusPk, 32);
  CHECK_ARRAYS_EQ(msg_bytes, kExpectedSphincsPlusMsg, 33);
  LOG_INFO("SPHINCS+-SHA2-128s vector payload verified against golden values.");

  LOG_INFO(
      "Executing SPHINCS+-SHA2-128s verification using sigverify/sphincsplus "
      "driver...");
  uint32_t exp_root[kSpxVerifyRootNumWords];
  spx_public_key_root((const uint32_t *)pk_bytes, exp_root);

  uint32_t act_root[kSpxVerifyRootNumWords];
  rom_error_t err = spx_verify((const uint32_t *)sig_bytes, NULL, 0, NULL, 0,
                               NULL, 0, msg_bytes, kat_data->msg_len,
                               (const uint32_t *)pk_bytes, act_root);
  CHECK(err == kErrorOk, "spx_verify failed with rom_error 0x%08x", err);

  CHECK_ARRAYS_EQ(act_root, exp_root, kSpxVerifyRootNumWords);
  LOG_INFO("SPHINCS+-SHA2-128s root matches public key root.");
  LOG_INFO("SPHINCS+-SHA2-128s Known Answer Test check ok.");

  return OK_STATUS();
}

static status_t test_ecdh_p256_kat(const fips_kat_descriptor_table_t *table) {
  LOG_INFO("Searching for ECDH-P256 KAT entry (alg_id = %u)...",
           kFipsKatAlgEcdhP256);
  const fips_kat_entry_t *entry = find_fips_entry(table, kFipsKatAlgEcdhP256);
  CHECK(entry != NULL, "ECDH-P256 KAT entry not found in table!");
  LOG_INFO("Entry found: algorithm_id=%u, offset=%u, size=%u",
           entry->algorithm_id, entry->offset, entry->size);

  LOG_INFO("Resolving ECDH-P256 KAT data payload...");
  const void *data = get_fips_data(table, entry);
  CHECK(data != NULL, "Failed to resolve KAT data payload (out of bounds)!");

  const ecdh_kat_data_t *kat_data = (const ecdh_kat_data_t *)data;
  CHECK(kat_data->priv_key_len == 32, "Expected priv_key_len=32, got %u",
        kat_data->priv_key_len);
  CHECK(kat_data->pub_key_len1 == 32, "Expected pub_key_len1=32, got %u",
        kat_data->pub_key_len1);
  CHECK(kat_data->pub_key_len2 == 32, "Expected pub_key_len2=32, got %u",
        kat_data->pub_key_len2);
  CHECK(kat_data->shared_secret_len == 32,
        "Expected shared_secret_len=32, got %u", kat_data->shared_secret_len);

  const uint8_t *d = kat_data->data;
  const uint8_t *qx = kat_data->data + kat_data->priv_key_len;
  const uint8_t *qy =
      kat_data->data + kat_data->priv_key_len + kat_data->pub_key_len1;
  const uint8_t *expected_ss = kat_data->data + kat_data->priv_key_len +
                               kat_data->pub_key_len1 + kat_data->pub_key_len2;

  LOG_INFO(
      "Executing ECDH-P256 shared secret computation using OTBN "
      "coprocessor...");
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

  const otcrypto_key_config_t kP256Config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeEcdhP256,
      .key_length = 32,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };

  uint32_t keyblob_sk[20] = {0};
  otcrypto_blinded_key_t private_key = {
      .config = kP256Config,
      .keyblob_length = sizeof(keyblob_sk),
      .keyblob = keyblob_sk,
      .checksum = 0,
  };
  memcpy(keyblob_sk, d, 32);
  private_key.checksum = otcrypto_integrity_blinded_checksum(&private_key);

  uint32_t pk_data[16];
  memcpy(pk_data, qx, 32);
  memcpy(pk_data + 8, qy, 32);
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdhP256,
      .key_length = sizeof(pk_data),
      .key = pk_data,
      .checksum = 0,
  };
  public_key.checksum = otcrypto_integrity_unblinded_checksum(&public_key);

  uint32_t shared_secretblob[32];
  memset(shared_secretblob, 0, sizeof(shared_secretblob));
  otcrypto_blinded_key_t shared_secret = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModeAesCtr,
              .key_length = 64,
              .hw_backed = kHardenedBoolFalse,
              .exportable = kHardenedBoolTrue,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = sizeof(shared_secretblob),
      .keyblob = shared_secretblob,
      .checksum = 0,
  };

  CHECK_STATUS_OK(
      otcrypto_ecdh_p256(&private_key, &public_key, &shared_secret));

  uint32_t ss_share0[16];
  uint32_t ss_share1[16];
  otcrypto_word32_buf_t ss_share0_buf = otcrypto_make_word32_buf(ss_share0, 16);
  otcrypto_word32_buf_t ss_share1_buf = otcrypto_make_word32_buf(ss_share1, 16);
  CHECK_STATUS_OK(otcrypto_export_blinded_key(&shared_secret, &ss_share0_buf,
                                              &ss_share1_buf));

  uint32_t ss[16];
  for (size_t i = 0; i < 16; ++i) {
    ss[i] = ss_share0[i] ^ ss_share1[i];
  }

  CHECK_ARRAYS_EQ((const uint8_t *)ss, expected_ss, 32);
  LOG_INFO("ECDH-P256 Shared Secret Computation Known Answer Test check ok.");

  return OK_STATUS();
}

static status_t test_ecdh_p384_kat(const fips_kat_descriptor_table_t *table) {
  LOG_INFO("Searching for ECDH-P384 KAT entry (alg_id = %u)...",
           kFipsKatAlgEcdhP384);
  const fips_kat_entry_t *entry = find_fips_entry(table, kFipsKatAlgEcdhP384);
  CHECK(entry != NULL, "ECDH-P384 KAT entry not found in table!");
  LOG_INFO("Entry found: algorithm_id=%u, offset=%u, size=%u",
           entry->algorithm_id, entry->offset, entry->size);

  LOG_INFO("Resolving ECDH-P384 KAT data payload...");
  const void *data = get_fips_data(table, entry);
  CHECK(data != NULL, "Failed to resolve KAT data payload (out of bounds)!");

  const ecdh_kat_data_t *kat_data = (const ecdh_kat_data_t *)data;
  CHECK(kat_data->priv_key_len == 48, "Expected priv_key_len=48, got %u",
        kat_data->priv_key_len);
  CHECK(kat_data->pub_key_len1 == 48, "Expected pub_key_len1=48, got %u",
        kat_data->pub_key_len1);
  CHECK(kat_data->pub_key_len2 == 48, "Expected pub_key_len2=48, got %u",
        kat_data->pub_key_len2);
  CHECK(kat_data->shared_secret_len == 48,
        "Expected shared_secret_len=48, got %u", kat_data->shared_secret_len);

  const uint8_t *d = kat_data->data;
  const uint8_t *qx = kat_data->data + kat_data->priv_key_len;
  const uint8_t *qy =
      kat_data->data + kat_data->priv_key_len + kat_data->pub_key_len1;
  const uint8_t *expected_ss = kat_data->data + kat_data->priv_key_len +
                               kat_data->pub_key_len1 + kat_data->pub_key_len2;

  LOG_INFO(
      "Executing ECDH-P384 shared secret computation using OTBN "
      "coprocessor...");
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

  const otcrypto_key_config_t kP384Config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeEcdhP384,
      .key_length = 48,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };

  uint32_t keyblob_sk[28] = {0};
  otcrypto_blinded_key_t private_key = {
      .config = kP384Config,
      .keyblob_length = sizeof(keyblob_sk),
      .keyblob = keyblob_sk,
      .checksum = 0,
  };
  memcpy(keyblob_sk, d, 48);
  private_key.checksum = otcrypto_integrity_blinded_checksum(&private_key);

  uint32_t pk_data[24];
  memcpy(pk_data, qx, 48);
  memcpy(pk_data + 12, qy, 48);
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdhP384,
      .key_length = sizeof(pk_data),
      .key = pk_data,
      .checksum = 0,
  };
  public_key.checksum = otcrypto_integrity_unblinded_checksum(&public_key);

  uint32_t shared_secretblob[48];
  memset(shared_secretblob, 0, sizeof(shared_secretblob));
  otcrypto_blinded_key_t shared_secret = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModeAesCtr,
              .key_length = 96,
              .hw_backed = kHardenedBoolFalse,
              .exportable = kHardenedBoolTrue,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = sizeof(shared_secretblob),
      .keyblob = shared_secretblob,
      .checksum = 0,
  };

  CHECK_STATUS_OK(
      otcrypto_ecdh_p384(&private_key, &public_key, &shared_secret));

  uint32_t ss_share0[24];
  uint32_t ss_share1[24];
  otcrypto_word32_buf_t ss_share0_buf = otcrypto_make_word32_buf(ss_share0, 24);
  otcrypto_word32_buf_t ss_share1_buf = otcrypto_make_word32_buf(ss_share1, 24);
  CHECK_STATUS_OK(otcrypto_export_blinded_key(&shared_secret, &ss_share0_buf,
                                              &ss_share1_buf));

  uint32_t ss[24];
  for (size_t i = 0; i < 24; ++i) {
    ss[i] = ss_share0[i] ^ ss_share1[i];
  }

  CHECK_ARRAYS_EQ((const uint8_t *)ss, expected_ss, 48);
  LOG_INFO("ECDH-P384 Shared Secret Computation Known Answer Test check ok.");

  return OK_STATUS();
}

static status_t test_x25519_kat(const fips_kat_descriptor_table_t *table) {
  LOG_INFO("Searching for X25519 KAT entry (alg_id = %u)...",
           kFipsKatAlgX25519);
  const fips_kat_entry_t *entry = find_fips_entry(table, kFipsKatAlgX25519);
  CHECK(entry != NULL, "X25519 KAT entry not found in table!");
  LOG_INFO("Entry found: algorithm_id=%u, offset=%u, size=%u",
           entry->algorithm_id, entry->offset, entry->size);

  LOG_INFO("Resolving X25519 KAT data payload...");
  const void *data = get_fips_data(table, entry);
  CHECK(data != NULL, "Failed to resolve KAT data payload (out of bounds)!");

  const ecdh_kat_data_t *kat_data = (const ecdh_kat_data_t *)data;
  CHECK(kat_data->priv_key_len == 32, "Expected priv_key_len=32, got %u",
        kat_data->priv_key_len);
  CHECK(kat_data->pub_key_len1 == 32, "Expected pub_key_len1=32, got %u",
        kat_data->pub_key_len1);
  CHECK(kat_data->pub_key_len2 == 0, "Expected pub_key_len2=0, got %u",
        kat_data->pub_key_len2);
  CHECK(kat_data->shared_secret_len == 32,
        "Expected shared_secret_len=32, got %u", kat_data->shared_secret_len);

  const uint8_t *sk = kat_data->data;
  const uint8_t *pk = kat_data->data + kat_data->priv_key_len;
  const uint8_t *expected_ss =
      kat_data->data + kat_data->priv_key_len + kat_data->pub_key_len1;

  LOG_INFO("Executing X25519 key agreement using OTBN coprocessor...");
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

  const otcrypto_key_config_t kX25519Config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeX25519,
      .key_length = 32,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };

  uint32_t keyblob_sk[keyblob_num_words(kX25519Config)];
  memset(keyblob_sk, 0, sizeof(keyblob_sk));
  otcrypto_blinded_key_t private_key = {
      .config = kX25519Config,
      .keyblob_length = sizeof(keyblob_sk),
      .keyblob = keyblob_sk,
      .checksum = 0,
  };
  memcpy(keyblob_sk, sk, 32);
  private_key.checksum = otcrypto_integrity_blinded_checksum(&private_key);

  uint32_t pk_data[8];
  memcpy(pk_data, pk, 32);
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeX25519,
      .key_length = sizeof(pk_data),
      .key = pk_data,
      .checksum = 0,
  };
  public_key.checksum = otcrypto_integrity_unblinded_checksum(&public_key);

  uint32_t shared_secretblob[keyblob_num_words(kX25519Config)];
  memset(shared_secretblob, 0, sizeof(shared_secretblob));
  otcrypto_blinded_key_t shared_secret = {
      .config = kX25519Config,
      .keyblob_length = sizeof(shared_secretblob),
      .keyblob = shared_secretblob,
      .checksum = 0,
  };

  CHECK_STATUS_OK(otcrypto_x25519(&private_key, &public_key, &shared_secret));

  uint32_t ss[8];
  uint32_t *ss_share0 = shared_secretblob;
  uint32_t *ss_share1 = shared_secretblob + 8;
  for (size_t i = 0; i < 8; ++i) {
    ss[i] = ss_share0[i] ^ ss_share1[i];
  }

  CHECK_ARRAYS_EQ((const uint8_t *)ss, expected_ss, 32);
  LOG_INFO("X25519 Key Agreement Known Answer Test check ok.");

  return OK_STATUS();
}

static status_t test_mldsa87_kat(const fips_kat_descriptor_table_t *table) {
  LOG_INFO("Searching for ML-DSA-87 KAT entry (alg_id = %u)...",
           kFipsKatAlgMldsa87);
  const fips_kat_entry_t *entry = find_fips_entry(table, kFipsKatAlgMldsa87);
  CHECK(entry != NULL, "ML-DSA-87 KAT entry not found in table!");
  LOG_INFO("Entry found: algorithm_id=%u, offset=%u, size=%u",
           entry->algorithm_id, entry->offset, entry->size);

  LOG_INFO("Resolving ML-DSA-87 KAT data payload...");
  const void *data = get_fips_data(table, entry);
  CHECK(data != NULL, "Failed to resolve KAT data payload (out of bounds)!");

  const mldsa_kat_data_t *kat_data = (const mldsa_kat_data_t *)data;
  CHECK(kat_data->num_cases == 5, "Expected num_cases=5, got %u",
        kat_data->num_cases);

  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

  static uint32_t pk_data[kOtcryptoMldsa87PkWords];
  static uint32_t sk_data[kOtcryptoMldsa87SkWords];
  static uint32_t sig_data[kOtcryptoMldsa87SigWords];

  uint64_t total_suite_start = ibex_mcycle_read();

  for (size_t i = 0; i < kat_data->num_cases; ++i) {
    uint64_t case_start = ibex_mcycle_read();
    const fips_kat_mldsa87_case_t *c = &kat_data->cases[i];

    // 1. Prepare 64-byte blinded seed xi (share0 = seed, share1 = 0)
    uint32_t xi_data[16] = {0};
    memcpy(xi_data, c->seed, 32);

    otcrypto_blinded_key_t xi = {
        .config =
            {
                .version = kOtcryptoLibVersion1,
                .key_mode = kOtcryptoKeyModePqcMldsa87,
                .key_length = 64,
                .hw_backed = kHardenedBoolFalse,
                .security_level = kOtcryptoKeySecurityLevelLow,
            },
        .keyblob_length = 64,
        .keyblob = xi_data,
    };
    xi.checksum = otcrypto_integrity_blinded_checksum(&xi);

    otcrypto_unblinded_key_t pk = {
        .key_mode = kOtcryptoKeyModePqcMldsa87,
        .key_length = kOtcryptoMldsa87PkBytes,
        .key = pk_data,
    };

    otcrypto_blinded_key_t sk = {
        .config =
            {
                .version = kOtcryptoLibVersion1,
                .key_mode = kOtcryptoKeyModePqcMldsa87,
                .key_length = kOtcryptoMldsa87SkBytes,
                .hw_backed = kHardenedBoolFalse,
                .security_level = kOtcryptoKeySecurityLevelLow,
            },
        .keyblob_length = kOtcryptoMldsa87SkBytes,
        .keyblob = sk_data,
    };

    // 2. Deterministic KeyGen on OTBN
    uint64_t t_keygen_start = ibex_mcycle_read();
    CHECK_STATUS_OK(mldsa87_det_keygen_internal_start(&xi));
    CHECK_STATUS_OK(mldsa87_keygen_internal_finalize(&pk, &sk));
    uint64_t keygen_cycles = ibex_mcycle_read() - t_keygen_start;
    pk.checksum = otcrypto_integrity_unblinded_checksum(&pk);
    sk.checksum = otcrypto_integrity_blinded_checksum(&sk);

    // 3. Compute mu = SHAKE256(tr || M', 64)
    // tr (64 bytes) is located at sk.keyblob + 24
    uint64_t t_mu_start = ibex_mcycle_read();
    otcrypto_sha3_context_t sha3_ctx;
    CHECK_STATUS_OK(otcrypto_shake256_init(&sha3_ctx));
    otcrypto_const_byte_buf_t tr_buf =
        OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t,
                          (const unsigned char *)(sk.keyblob + 24), 64);
    CHECK_STATUS_OK(otcrypto_sha3_update(&sha3_ctx, &tr_buf));
    otcrypto_const_byte_buf_t mprime_buf = OTCRYPTO_MAKE_BUF(
        otcrypto_const_byte_buf_t, c->mprime, sizeof(c->mprime));
    CHECK_STATUS_OK(otcrypto_sha3_update(&sha3_ctx, &mprime_buf));

    uint32_t mu_data[16] = {0};
    otcrypto_hash_digest_t mu = {
        .data = mu_data,
        .len = 16,
    };
    CHECK_STATUS_OK(otcrypto_shake256_final(&sha3_ctx, &mu));
    uint64_t mu_cycles = ibex_mcycle_read() - t_mu_start;

    // 4. Deterministic Signing on OTBN
    uint64_t t_sign_start = ibex_mcycle_read();
    CHECK_STATUS_OK(
        mldsa87_sign_internal_start(&sk, &mu, kOtcryptoMldsaSignModeDet));
    otcrypto_word32_buf_t sig_buf = OTCRYPTO_MAKE_BUF(
        otcrypto_word32_buf_t, sig_data, kOtcryptoMldsa87SigWords);
    CHECK_STATUS_OK(
        mldsa87_sign_internal_finalize(&sig_buf, kMldsa87SingleSign));
    uint64_t sign_cycles = ibex_mcycle_read() - t_sign_start;

    // 5. Signature Output Hash Validation (SHA2-256 over exact 4627 bytes)
    uint64_t t_hash_start = ibex_mcycle_read();
    uint32_t actual_sig_hash[8] = {0};
    otcrypto_hash_digest_t sig_hash_digest = {
        .mode = kOtcryptoHashModeSha256,
        .len = 8,
        .data = actual_sig_hash,
    };
    otcrypto_const_byte_buf_t sig_bytes_buf = OTCRYPTO_MAKE_BUF(
        otcrypto_const_byte_buf_t, (const unsigned char *)sig_data, 4627);
    CHECK_STATUS_OK(otcrypto_sha2_256(&sig_bytes_buf, &sig_hash_digest));
    CHECK_ARRAYS_EQ((const uint8_t *)actual_sig_hash, c->expected_sig_hash, 32);
    uint64_t hash_cycles = ibex_mcycle_read() - t_hash_start;

    // 6. Signature Verification on OTBN
    uint64_t t_verify_start = ibex_mcycle_read();
    otcrypto_const_word32_buf_t const_sig_buf = OTCRYPTO_MAKE_BUF(
        otcrypto_const_word32_buf_t, sig_data, kOtcryptoMldsa87SigWords);
    CHECK_STATUS_OK(mldsa87_verify_internal_start(&pk, &const_sig_buf, &mu));
    hardened_bool_t verification_result = kHardenedBoolFalse;
    CHECK_STATUS_OK(
        mldsa87_verify_internal_finalize(&const_sig_buf, &verification_result));
    CHECK(verification_result == kHardenedBoolTrue,
          "ML-DSA-87 signature verification failed!");
    uint64_t verify_cycles = ibex_mcycle_read() - t_verify_start;

    uint32_t case_total_cycles = (uint32_t)(ibex_mcycle_read() - case_start);
    uint32_t case_total_us = case_total_cycles / 24;  // 24 MHz clock
    LOG_INFO(
        "ML-DSA-87 Case %u/5 timing: Total=%u cycles (%u us), KeyGen=%u, "
        "Mu=%u, Sign=%u, Hash=%u, Verify=%u",
        (uint32_t)(i + 1), case_total_cycles, case_total_us,
        (uint32_t)keygen_cycles, (uint32_t)mu_cycles, (uint32_t)sign_cycles,
        (uint32_t)hash_cycles, (uint32_t)verify_cycles);
  }

  uint32_t total_suite_cycles =
      (uint32_t)(ibex_mcycle_read() - total_suite_start);
  uint32_t total_suite_us = total_suite_cycles / 24;
  LOG_INFO(
      "ML-DSA-87 All 5 Cases Total Suite Timing: %u cycles (%u us / %u ms)",
      total_suite_cycles, total_suite_us, total_suite_us / 1000);
  busy_spin_micros(100000);
  return OK_STATUS();
}

static status_t test_mlkem1024_kat(const fips_kat_descriptor_table_t *table) {
  LOG_INFO("Searching for ML-KEM-1024 KAT entry (alg_id = %u)...",
           kFipsKatAlgMlkem1024);
  const fips_kat_entry_t *entry = find_fips_entry(table, kFipsKatAlgMlkem1024);
  CHECK(entry != NULL, "ML-KEM-1024 KAT entry not found in table!");
  LOG_INFO("Entry found: algorithm_id=%u, offset=%u, size=%u",
           entry->algorithm_id, entry->offset, entry->size);

  LOG_INFO("Resolving ML-KEM-1024 KAT data payload...");
  const void *data = get_fips_data(table, entry);
  CHECK(data != NULL, "Failed to resolve KAT data payload (out of bounds)!");

  const kem_kat_data_t *kat = (const kem_kat_data_t *)data;
  CHECK(kat->seed_d_len == 32, "Invalid seed_d_len: %u", kat->seed_d_len);
  CHECK(kat->seed_z_len == 32, "Invalid seed_z_len: %u", kat->seed_z_len);
  CHECK(kat->seed_m_len == 32, "Invalid seed_m_len: %u", kat->seed_m_len);
  CHECK(kat->exp_ct_hash_len == 32, "Invalid exp_ct_hash_len: %u",
        kat->exp_ct_hash_len);
  CHECK(kat->exp_ss_len == 32, "Invalid exp_ss_len: %u", kat->exp_ss_len);

  const uint8_t *seed_d = kat->data;
  const uint8_t *seed_z = seed_d + kat->seed_d_len;
  const uint8_t *seed_m = seed_z + kat->seed_z_len;
  const uint8_t *exp_ct_hash = seed_m + kat->seed_m_len;
  const uint8_t *exp_ss = exp_ct_hash + kat->exp_ct_hash_len;

  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

  uint64_t t_start = ibex_mcycle_read();

  // 1. Prepare deterministic key generation inputs.
  uint32_t d_blob[64 / sizeof(uint32_t)] = {0};
  memcpy(d_blob, seed_d, kat->seed_d_len);

  otcrypto_blinded_key_t d = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModePqcMlkem1024,
              .key_length = 64,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = 64,
      .keyblob = d_blob,
  };
  d.checksum = otcrypto_integrity_blinded_checksum(&d);

  uint32_t z_data[kMlkem1024SharedSecretWords];
  memcpy(z_data, seed_z, kat->seed_z_len);
  otcrypto_const_word32_buf_t z = {
      .data = z_data,
      .len = kMlkem1024SharedSecretWords,
  };

  static uint32_t pk_data[kMlkem1024PublicKeyWords];
  otcrypto_unblinded_key_t pk = {
      .key_mode = kOtcryptoKeyModePqcMlkem1024,
      .key_length = kMlkem1024PublicKeyBytes,
      .key = pk_data,
  };

  static uint32_t sk_data[kMlkem1024SecretKeyWords];
  otcrypto_blinded_key_t sk = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModePqcMlkem1024,
              .key_length = kMlkem1024SecretKeyBytes / 2,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = kMlkem1024SecretKeyBytes,
      .keyblob = sk_data,
  };
  sk.checksum = otcrypto_integrity_blinded_checksum(&sk);

  // 2. Deterministic KeyGen on OTBN
  LOG_INFO("Executing ML-KEM-1024 deterministic keygen on OTBN...");
  uint64_t t_keygen_start = ibex_mcycle_read();
  CHECK_STATUS_OK(mlkem1024_det_keygen_internal_start(&d, &z));
  CHECK_STATUS_OK(mlkem1024_keygen_internal_finalize(&pk, &sk));
  uint64_t keygen_cycles = ibex_mcycle_read() - t_keygen_start;

  // 3. Encapsulation
  LOG_INFO("Executing ML-KEM-1024 encapsulation on OTBN...");
  uint32_t m_data[kMlkem1024SharedSecretWords];
  memcpy(m_data, seed_m, kat->seed_m_len);
  otcrypto_const_word32_buf_t m = {
      .data = m_data,
      .len = kMlkem1024SharedSecretWords,
  };

  static uint32_t ct_data[kMlkem1024CiphertextWords];
  otcrypto_word32_buf_t ct = {
      .data = ct_data,
      .len = kMlkem1024CiphertextWords,
  };

  uint32_t ss1_data[kMlkem1024SharedSecretWords];
  otcrypto_blinded_key_t ss1 = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModePqcMlkem1024,
              .key_length = kMlkem1024SharedSecretBytes / 2,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = kMlkem1024SharedSecretBytes,
      .keyblob = ss1_data,
  };
  ss1.checksum = otcrypto_integrity_blinded_checksum(&ss1);

  uint64_t t_encaps_start = ibex_mcycle_read();
  CHECK_STATUS_OK(otcrypto_mlkem1024_encaps(&pk, &m, &ct, &ss1));
  uint64_t encaps_cycles = ibex_mcycle_read() - t_encaps_start;

  // 4. Validate Ciphertext Output Hash (SHA2-256 over 1568 bytes)
  uint32_t actual_ct_hash[8] = {0};
  otcrypto_hash_digest_t ct_hash_digest = {
      .mode = kOtcryptoHashModeSha256,
      .len = 8,
      .data = actual_ct_hash,
  };
  otcrypto_const_byte_buf_t ct_bytes_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, (const unsigned char *)ct_data,
      kMlkem1024CiphertextBytes);
  CHECK_STATUS_OK(otcrypto_sha2_256(&ct_bytes_buf, &ct_hash_digest));

  // 5. Decapsulation
  LOG_INFO("Executing ML-KEM-1024 decapsulation on OTBN...");
  uint32_t ss2_data[kMlkem1024SharedSecretWords];
  otcrypto_blinded_key_t ss2 = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModePqcMlkem1024,
              .key_length = kMlkem1024SharedSecretBytes / 2,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = kMlkem1024SharedSecretBytes,
      .keyblob = ss2_data,
  };
  ss2.checksum = otcrypto_integrity_blinded_checksum(&ss2);

  otcrypto_const_word32_buf_t ct_const = {
      .data = ct_data,
      .len = kMlkem1024CiphertextWords,
  };

  uint64_t t_decaps_start = ibex_mcycle_read();
  CHECK_STATUS_OK(otcrypto_mlkem1024_decaps(&sk, &ct_const, &ss2));
  uint64_t decaps_cycles = ibex_mcycle_read() - t_decaps_start;

  // 6. Validate
  CHECK_ARRAYS_EQ((const uint8_t *)actual_ct_hash, exp_ct_hash, 32);
  CHECK_ARRAYS_EQ(ss1_data, ss2_data, kMlkem1024SharedSecretWords);
  CHECK_ARRAYS_EQ((const uint8_t *)ss1_data, exp_ss, 32);

  uint32_t total_cycles = (uint32_t)(ibex_mcycle_read() - t_start);
  LOG_INFO(
      "ML-KEM-1024 KAT passed: Total=%u cycles (%u us), KeyGen=%u, "
      "Encaps=%u, Decaps=%u",
      total_cycles, total_cycles / 24, (uint32_t)keygen_cycles,
      (uint32_t)encaps_cycles, (uint32_t)decaps_cycles);

  return OK_STATUS();
}

static void stop_sha3_conditioner(dif_entropy_src_t *entropy_src) {
  uint32_t fail_count = 0;
  dif_result_t op_result;
  do {
    op_result = dif_entropy_src_conditioner_stop(entropy_src);
    if (op_result == kDifIpFifoFull) {
      fail_count++;
      CHECK(fail_count < 256);
    } else {
      CHECK_DIF_OK(op_result);
    }
  } while (op_result == kDifIpFifoFull);
}

static void flush_sha3_conditioner(dif_entropy_src_t *entropy_src) {
  CHECK_DIF_OK(dif_entropy_src_conditioner_start(entropy_src));
  stop_sha3_conditioner(entropy_src);

  int fail_count = 0;
  uint32_t got[12];
  size_t total = 0;
  do {
    dif_result_t op_result =
        dif_entropy_src_non_blocking_read(entropy_src, &got[total]);
    if (op_result == kDifUnavailable) {
      fail_count++;
      CHECK(fail_count < 256);
    } else {
      CHECK_DIF_OK(op_result);
      total++;
    }
  } while (total < ARRAYSIZE(got));
}

static status_t test_entropy_src_kat(const fips_kat_descriptor_table_t *table) {
  LOG_INFO(
      "Searching for Entropy Source SHA3 Conditioning KAT entry (alg_id = "
      "%u)...",
      kFipsKatAlgEntropySrcSha3Conditioning);
  const fips_kat_entry_t *entry =
      find_fips_entry(table, kFipsKatAlgEntropySrcSha3Conditioning);
  CHECK(entry != NULL, "Entropy Source KAT entry not found in table!");
  LOG_INFO("Entry found: algorithm_id=%u, offset=%u, size=%u",
           entry->algorithm_id, entry->offset, entry->size);

  LOG_INFO("Resolving Entropy Source KAT data payload...");
  const void *data = get_fips_data(table, entry);
  CHECK(data != NULL, "Failed to resolve KAT data payload (out of bounds)!");

  const hmac_kat_data_t *kat = (const hmac_kat_data_t *)data;
  CHECK(kat->key_len == 0, "Expected key_len=0, got %u", kat->key_len);
  CHECK(kat->msg_len == 48, "Expected msg_len=48, got %u", kat->msg_len);
  CHECK(kat->digest_len == 48, "Expected digest_len=48, got %u",
        kat->digest_len);

  const uint32_t *input_msg = (const uint32_t *)kat->data;
  const uint32_t *expected_digest =
      (const uint32_t *)(kat->data + kat->msg_len);

  LOG_INFO("Executing Entropy Source SHA3 Conditioning KAT on hardware...");
  uint64_t t_start = ibex_mcycle_read();

  dif_entropy_src_t entropy_src;
  CHECK_DIF_OK(dif_entropy_src_init_from_dt(kDtEntropySrc, &entropy_src));

  CHECK_STATUS_OK(entropy_testutils_stop_all());
  CHECK_STATUS_OK(entropy_src_testutils_fw_override_enable(
      &entropy_src, /*buffer_threshold=*/12,
      /*route_to_firmware=*/true,
      /*bypass_conditioner=*/false));

  flush_sha3_conditioner(&entropy_src);

  CHECK_DIF_OK(dif_entropy_src_conditioner_start(&entropy_src));

  dif_result_t op_result;
  uint32_t fail_count = 0;
  uint32_t count;
  uint32_t total = 0;

  do {
    op_result = dif_entropy_src_fw_ov_data_write(
        &entropy_src, input_msg + total, 12 - total, &count);
    if (op_result == kDifIpFifoFull) {
      fail_count++;
      CHECK(fail_count < 256);
    } else {
      fail_count = 0;
      CHECK_DIF_OK(op_result);
      total += count;
    }
  } while (total < 12);

  stop_sha3_conditioner(&entropy_src);

  fail_count = 0;
  uint32_t got[12];
  total = 0;
  do {
    op_result = dif_entropy_src_non_blocking_read(&entropy_src, &got[total]);
    if (op_result == kDifUnavailable) {
      fail_count++;
      CHECK(fail_count < 256);
    } else {
      CHECK_DIF_OK(op_result);
      total++;
    }
  } while (total < ARRAYSIZE(got));

  CHECK_ARRAYS_EQ(got, expected_digest, 12);

  uint32_t total_cycles = (uint32_t)(ibex_mcycle_read() - t_start);
  LOG_INFO(
      "Entropy Source SHA3 Conditioning KAT passed: Total=%u cycles (%u us)",
      total_cycles, total_cycles / 24);

  return OK_STATUS();
}

static status_t test_fips_kat_rom(void) {
  // Stop the watchdog timer to prevent timeout during long RSA-4096 OTBN
  // computations.
  dif_aon_timer_t aon_timer;
  CHECK_DIF_OK(dif_aon_timer_init_from_dt(kDtAonTimer, &aon_timer));
  CHECK_DIF_OK(dif_aon_timer_watchdog_stop(&aon_timer));

  LOG_INFO("Reading FIPS KAT descriptor table from ROM...");
  const fips_kat_descriptor_table_t *table = get_fips_descriptor_table();
  CHECK(table != NULL, "FIPS KAT table pointer is NULL!");
  CHECK(table->magic == kFipsKatDescriptorMagic, "Invalid table magic: 0x%08x",
        table->magic);
  CHECK(table->version == kFipsKatDescriptorVersion1,
        "Invalid table version: %u", table->version);
  CHECK(table->entry_count >= 28, "Expected at least 28 entries, got %u",
        table->entry_count);
  LOG_INFO(
      "FIPS KAT table found at %p (magic=0x%08x, version=%u, entries=%u, "
      "total_size=%u)",
      table, table->magic, table->version, table->entry_count,
      table->total_size);

  TRY(test_sha256_kat(table));
  TRY(test_hmac_sha256_kat(table));
  TRY(test_sha512_kat(table));
  TRY(test_hmac_sha512_kat(table));
  TRY(test_shake256_kat(table));
  TRY(test_kmac256_kat(table));
  TRY(test_aes_ecb256_kat(table));
  TRY(test_aes_cbc256_kat(table));
  TRY(test_aes_kwp256_kat(table));
  TRY(test_aes_gcm256_kat(table));
  TRY(test_drbg_aes256_kat(table));
  TRY(test_kdf_hmac_sha256_kat(table));
  TRY(test_kdf_kmac256_kat(table));
  TRY(test_rsa4096_sign_kat(table));
  TRY(test_rsa4096_verify_kat(table));
  TRY(test_ecdsa_p256_sign_kat(table));
  TRY(test_ecdsa_p256_verify_kat(table));
  TRY(test_ecdsa_p384_sign_kat(table));
  TRY(test_ecdsa_p384_verify_kat(table));
  TRY(test_ed25519_sign_kat(table));
  TRY(test_ed25519_verify_kat(table));
  TRY(test_sphincsplus_sha2_128s_verify_kat(table));
  TRY(test_ecdh_p256_kat(table));
  TRY(test_ecdh_p384_kat(table));
  TRY(test_x25519_kat(table));
  TRY(test_mldsa87_kat(table));
  TRY(test_mlkem1024_kat(table));
  TRY(test_entropy_src_kat(table));

  return OK_STATUS();
}

bool test_main(void) {
  status_t sts = test_fips_kat_rom();
  if (status_err(sts)) {
    LOG_ERROR("test_fips_kat_rom failed: %r", sts);
  }
  return status_ok(sts);
}
